import { useEffect, useRef, useState } from 'react'
import BetController from '../components/BetController'
import GameShell from '../components/GameShell'
import ResultPopup, { RoundResult } from '../components/ResultPopup'
import { BetStatus } from '../types'
import { useCasinoWallet } from '../wallet'
import { CasinoApiError, casinoApi, postCasino } from '../casinoApi'

type CashoutNotice = { id: string; username: string; multiplier: number; profit: number; isYou?: boolean }
type Phase = 'running' | 'crashed' | 'countdown'
type CrashBet = { id: string; roundId: string; betAmount: number; autoTarget: number | null; status: 'queued' | 'active' | 'cashed' }
type CrashState = { type: string; roundId: string; nextRoundId: string; phase: Phase; startsAt: number; startedAt: number | null; crashedAt: number | null; multiplier: number; crashPoint: number | null; serverNow: number; players: number; recentCashouts?: CashoutEvent[] }
type CashoutEvent = { type: 'cashout'; betId: string; userId: string; username: string; multiplier: number; profit: number }
type CrashStateResponse = CrashState & { bet: CrashBet | null; newBalance: number }
type CrashStartResponse = { bet: CrashBet; state: CrashState; newBalance: number }
type CrashCashoutResponse = { multiplier: number; payout: number; profit: number; newBalance: number }

export default function Crash({ onBack }: { onBack: () => void }) {
  const wallet = useCasinoWallet()
  const walletRef = useRef(wallet)
  walletRef.current = wallet
  const canvas = useRef<HTMLCanvasElement>(null)
  const raf = useRef(0)
  const reconnectTimer = useRef(0)
  const socketRef = useRef<WebSocket | null>(null)
  const serverState = useRef<CrashState | null>(null)
  const serverOffset = useRef(0)
  const betRef = useRef<CrashBet | null>(null)
  const cashoutPending = useRef(false)
  const settledBets = useRef(new Set<string>())
  const [amount, setAmount] = useState(10)
  const [autoCashout, setAutoCashout] = useState(2)
  const [status, setStatus] = useState<BetStatus>('idle')
  const [phase, setPhase] = useState<Phase>('countdown')
  const [countdown, setCountdown] = useState(3)
  const [multi, setMulti] = useState(1)
  const [roundResult, setRoundResult] = useState<RoundResult | null>(null)
  const [cashouts, setCashouts] = useState<CashoutNotice[]>([])
  const [betQueued, setBetQueued] = useState(false)
  const [connected, setConnected] = useState(false)
  const [players, setPlayers] = useState(0)

  const draw = (m: number) => {
    const c = canvas.current
    if (!c) return
    const dpr = devicePixelRatio || 1
    const w = c.clientWidth
    const h = c.clientHeight
    c.width = w * dpr
    c.height = h * dpr
    const x = c.getContext('2d')!
    x.scale(dpr, dpr)
    x.clearRect(0, 0, w, h)
    x.strokeStyle = '#30445a'
    x.lineWidth = 1
    x.beginPath()
    for (let i = 1; i < 5; i++) {
      x.moveTo(0, h * i / 5)
      x.lineTo(w, h * i / 5)
    }
    x.stroke()
    const p = Math.min(.94, (m - 1) / Math.max(1, m))
    x.strokeStyle = '#b7f34a'
    x.shadowColor = '#b7f34a'
    x.shadowBlur = 14
    x.lineWidth = 5
    x.beginPath()
    for (let i = 0; i <= 80; i++) {
      const t = i / 80
      x.lineTo(20 + t * w * .9, h - 28 - Math.pow(t, 2.4) * (h - 65) * Math.min(1, p * 1.8))
    }
    x.stroke()
  }

  const addCashout = (notice: CashoutNotice) => setCashouts(current => [...current.filter(item => item.id !== notice.id).slice(-3), notice])

  const settleLocalLoss = (bet: CrashBet) => {
    if (settledBets.current.has(bet.id)) return
    settledBets.current.add(bet.id)
    walletRef.current.recordRound(bet.betAmount, -bet.betAmount)
    setRoundResult({ profit: -bet.betAmount })
    betRef.current = null
    setBetQueued(false)
    setStatus('idle')
  }

  const applyState = (state: CrashState) => {
    serverState.current = state
    serverOffset.current = state.serverNow - Date.now()
    setPhase(state.phase)
    setPlayers(state.players)
    if (state.phase === 'crashed') setMulti(state.crashPoint || state.multiplier)
    const bet = betRef.current
    if (!bet) {
      setStatus('idle')
      setBetQueued(false)
      return
    }
    if (bet.roundId === state.roundId && state.phase === 'running' && bet.status !== 'cashed') {
      bet.status = 'active'
      setStatus('active')
      setBetQueued(false)
      return
    }
    if (bet.roundId === state.roundId && state.phase === 'crashed') {
      if (bet.status === 'active') settleLocalLoss(bet)
      else {
        betRef.current = null
        setStatus('idle')
        setBetQueued(false)
      }
      return
    }
    setStatus('locked')
    setBetQueued(bet.status === 'queued')
  }

  const handleOwnAutoCashout = async (event: CashoutEvent) => {
    const bet = betRef.current
    if (!bet || settledBets.current.has(bet.id)) return
    settledBets.current.add(bet.id)
    bet.status = 'cashed'
    setStatus('locked')
    setBetQueued(false)
    walletRef.current.recordRound(bet.betAmount, event.profit)
    addCashout({ id: event.betId, username: 'You', multiplier: event.multiplier, profit: event.profit, isYou: true })
    setRoundResult({ profit: event.profit, title: 'Auto cash-out profit' })
    try {
      const state = await casinoApi<CrashStateResponse>('/crash/state')
      walletRef.current.syncBalance(state.newBalance)
    } catch {
      void walletRef.current.refresh().catch(() => {})
    }
  }

  useEffect(() => {
    let disposed = false

    const hydrate = async () => {
      try {
        const response = await casinoApi<CrashStateResponse>('/crash/state')
        if (disposed) return
        walletRef.current.syncBalance(response.newBalance)
        betRef.current = response.bet
        if (response.bet) setBetQueued(response.bet.status === 'queued')
        ;(response.recentCashouts || []).forEach(event => addCashout({ id: event.betId, username: event.username, multiplier: event.multiplier, profit: event.profit }))
        applyState(response)
      } catch {
        // Anonymous visitors can still watch the shared WebSocket round.
      }
    }

    const connect = () => {
      if (disposed) return
      const protocol = location.protocol === 'https:' ? 'wss:' : 'ws:'
      const socket = new WebSocket(`${protocol}//${location.host}/ws/crash`)
      socketRef.current = socket
      socket.onopen = () => setConnected(true)
      socket.onmessage = message => {
        try {
          const event = JSON.parse(String(message.data)) as CrashState | CashoutEvent
          if (event.type === 'cashout' && 'betId' in event) {
            if (event.betId === betRef.current?.id) {
              if (!cashoutPending.current) void handleOwnAutoCashout(event)
            } else {
              addCashout({ id: event.betId, username: event.username, multiplier: event.multiplier, profit: event.profit })
            }
            return
          }
          applyState(event as CrashState)
        } catch {
          // Ignore malformed socket messages and wait for the next server tick.
        }
      }
      socket.onclose = () => {
        setConnected(false)
        if (!disposed) reconnectTimer.current = window.setTimeout(connect, 1200)
      }
      socket.onerror = () => socket.close()
    }

    void hydrate()
    connect()
    const animate = () => {
      const state = serverState.current
      if (state) {
        const now = Date.now() + serverOffset.current
        let next = 1
        if (state.phase === 'running' && state.startedAt) next = Math.max(1, Math.exp((now - state.startedAt) / 8500))
        else if (state.phase === 'crashed') next = state.crashPoint || state.multiplier
        setMulti(next)
        draw(next)
        if (state.phase === 'countdown') setCountdown(Math.max(0, Math.ceil((state.startsAt - now) / 1000)))
      }
      raf.current = requestAnimationFrame(animate)
    }
    raf.current = requestAnimationFrame(animate)

    return () => {
      disposed = true
      cancelAnimationFrame(raf.current)
      clearTimeout(reconnectTimer.current)
      socketRef.current?.close()
    }
  }, [])

  const queueForNextRound = async (target?: number) => {
    if (status !== 'idle' || amount > wallet.balance) return
    setRoundResult(null)
    setStatus('locked')
    setBetQueued(true)
    try {
      const response = await postCasino<CrashStartResponse>('/crash/start', { betAmount: amount, autoTarget: target })
      wallet.syncBalance(response.newBalance)
      betRef.current = response.bet
      applyState(response.state)
    } catch (error) {
      setBetQueued(false)
      setStatus('idle')
      setRoundResult({ profit: 0, title: error instanceof Error ? error.message : 'Unable to queue Crash bet', error: true })
    }
  }

  const cashout = async () => {
    const bet = betRef.current
    if (status !== 'active' || !bet || cashoutPending.current) return
    cashoutPending.current = true
    setStatus('locked')
    try {
      const response = await postCasino<CrashCashoutResponse>('/crash/cashout', {})
      settledBets.current.add(bet.id)
      bet.status = 'cashed'
      wallet.syncBalance(response.newBalance)
      wallet.recordRound(bet.betAmount, response.profit)
      addCashout({ id: bet.id, username: 'You', multiplier: response.multiplier, profit: response.profit, isYou: true })
      setRoundResult({ profit: response.profit, title: 'Cash-out profit' })
    } catch (error) {
      if (error instanceof CasinoApiError && error.data.newBalance !== undefined) wallet.syncBalance(Number(error.data.newBalance))
      if (!(error instanceof CasinoApiError && error.data.crashed)) {
        setStatus('active')
        setRoundResult({ profit: 0, title: error instanceof Error ? error.message : 'Unable to cash out', error: true })
      }
    } finally {
      cashoutPending.current = false
    }
  }

  const activeStake = betRef.current?.status === 'active' ? betRef.current.betAmount : 0
  const panel = <BetController amount={amount} setAmount={setAmount} status={status} onAction={status === 'active' ? () => void cashout() : () => void queueForNextRound()} onAutoAction={() => void queueForNextRound(autoCashout)} autoTarget={autoCashout} setAutoTarget={setAutoCashout} canCashOut={status === 'active'} disabled={!connected || amount > wallet.balance} potential={activeStake * multi} lastResult={roundResult} idleLabel="Bet Next Round" lockedLabel={betQueued ? 'Bet Queued' : 'Round Active'} hideChildrenInAuto>
    <div className="rounded-lg bg-[#0c1623] p-3 text-xs text-slate-400">One shared server round for every player. Bets placed now enter the next available round.</div>
  </BetController>

  return <>
    <GameShell title="Crash" onBack={onBack} panel={panel}>
      <div className="relative h-[430px] w-full max-w-[900px] overflow-hidden rounded-xl">
        <canvas ref={canvas} className="h-full w-full" />
        <div className="pointer-events-none absolute left-3 top-3 z-10 rounded-full border border-lime/20 bg-[#102331]/90 px-3 py-1.5 text-[10px] font-extrabold uppercase tracking-widest text-lime">
          {!connected ? 'Reconnecting…' : betQueued ? 'Bet queued' : phase === 'running' ? `Live round · ${players} playing` : phase === 'countdown' ? 'Bets open' : 'Round ended'}
        </div>
        <div className="pointer-events-none absolute right-3 top-3 z-10 flex w-[min(320px,82%)] flex-col items-end gap-2">
          {cashouts.map(item => <div key={item.id} className={`animate-pop rounded-lg border px-3 py-2 text-xs shadow-xl backdrop-blur ${item.isYou ? 'border-lime/40 bg-lime/15' : 'border-white/10 bg-[#132235]/90'}`}>
            <span className={item.isYou ? 'font-bold text-lime' : 'font-bold text-white'}>{item.username}</span>
            <span className="text-slate-300"> cashed out at </span>
            <b className="text-lime">{item.multiplier.toFixed(2)}×</b>
            <span className="ml-1 font-bold text-lime">(+⬡ {item.profit.toLocaleString()})</span>
          </div>)}
        </div>
        <div className="pointer-events-none absolute inset-0 flex items-center justify-center text-center">
          {phase === 'running' ? <div className="font-display text-6xl font-extrabold text-lime sm:text-8xl">{multi.toFixed(2)}×</div> : phase === 'crashed' ? <div>
            <div className="font-display text-5xl font-extrabold text-red-400 sm:text-7xl">CRASHED</div>
            <div className="mt-2 text-xl font-extrabold text-red-300">{multi.toFixed(2)}×</div>
          </div> : <div>
            <div className="text-sm font-extrabold uppercase tracking-[.25em] text-slate-400">Next round starting in</div>
            <div className="mt-2 font-display text-8xl font-extrabold text-white">{countdown}</div>
          </div>}
        </div>
      </div>
    </GameShell>
    <ResultPopup result={roundResult} onClose={() => setRoundResult(null)} />
  </>
}
