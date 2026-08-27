import { useEffect, useRef, useState } from 'react'
import BetController from '../components/BetController'
import GameShell from '../components/GameShell'
import ResultPopup, { RoundResult } from '../components/ResultPopup'
import { BetStatus } from '../types'
import { useCasinoWallet } from '../wallet'

type CashoutNotice={id:number;username:string;multiplier:number;profit:number;isYou?:boolean}
type Phase='running'|'crashed'|'countdown'
type QueuedBet={stake:number;target?:number}

const usernames=['LunaAce','diamondhand','SCLKing','Maya_22','LuckyNova','crashpilot','RioWins','greenlight','Jax_91','pixelbet']
function crashPoint(){const r=Math.random();return Math.max(1,Math.floor((.99/(1-r))*100)/100)}

export default function Crash({onBack}:{onBack:()=>void}){
 const wallet=useCasinoWallet()
 const canvas=useRef<HTMLCanvasElement>(null)
 const raf=useRef(0)
 const phaseTimer=useRef(0)
 const threshold=useRef(2)
 const liveMulti=useRef(1)
 const betCashedOut=useRef(false)
 const activeStake=useRef(0)
 const activeAutoTarget=useRef<number|undefined>()
 const queuedBet=useRef<QueuedBet|null>(null)
 const nextNoticeAt=useRef(1.08)
 const noticeId=useRef(0)
 const walletRef=useRef(wallet)
 walletRef.current=wallet
 const [amount,setAmount]=useState(10)
 const [autoCashout,setAutoCashout]=useState(2)
 const [status,setStatus]=useState<BetStatus>('idle')
 const [phase,setPhase]=useState<Phase>('running')
 const [countdown,setCountdown]=useState(3)
 const [multi,setMulti]=useState(1)
 const [roundResult,setRoundResult]=useState<RoundResult|null>(null)
 const [cashouts,setCashouts]=useState<CashoutNotice[]>([])
 const [betQueued,setBetQueued]=useState(false)

 const draw=(m:number)=>{const c=canvas.current;if(!c)return;const dpr=devicePixelRatio||1,w=c.clientWidth,h=c.clientHeight;c.width=w*dpr;c.height=h*dpr;const x=c.getContext('2d')!;x.scale(dpr,dpr);x.clearRect(0,0,w,h);x.strokeStyle='#30445a';x.lineWidth=1;x.beginPath();for(let i=1;i<5;i++){x.moveTo(0,h*i/5);x.lineTo(w,h*i/5)}x.stroke();const p=Math.min(.94,(m-1)/Math.max(1,m));x.strokeStyle='#b7f34a';x.shadowColor='#b7f34a';x.shadowBlur=14;x.lineWidth=5;x.beginPath();for(let i=0;i<=80;i++){const t=i/80;x.lineTo(20+t*w*.9,h-28-Math.pow(t,2.4)*(h-65)*Math.min(1,p*1.8))}x.stroke()}
 const addCashout=(notice:Omit<CashoutNotice,'id'>)=>setCashouts(current=>[...current.slice(-3),{...notice,id:++noticeId.current}])
 const addBotCashout=(m:number)=>{const stake=10+Math.floor(Math.random()*490);addCashout({username:usernames[Math.floor(Math.random()*usernames.length)],multiplier:m,profit:Math.floor(stake*(m-1))});nextNoticeAt.current=m+Math.max(.08,m*(.08+Math.random()*.2))}
 const settleCashout=(at:number)=>{if(betCashedOut.current||activeStake.current<=0)return;betCashedOut.current=true;const stake=activeStake.current;const payout=Math.floor(stake*at);const profit=payout-stake;walletRef.current.credit(payout);walletRef.current.recordRound(stake,profit);setStatus('locked');addCashout({username:'You',multiplier:at,profit,isYou:true});setRoundResult({profit,title:'Cash-out profit'})}
 const queueForNextRound=(target?:number)=>{if(status!=='idle'||amount>wallet.balance)return;queuedBet.current={stake:amount,target};setBetQueued(true);setRoundResult(null);setStatus('locked')}
 const cashout=()=>{if(status!=='active')return;settleCashout(liveMulti.current)}

 useEffect(()=>{
  let disposed=false
  const beginCountdown=()=>{if(disposed)return;setPhase('countdown');let left=3;setCountdown(left);phaseTimer.current=window.setInterval(()=>{left-=1;if(left<=0){clearInterval(phaseTimer.current);startRound()}else setCountdown(left)},1000)}
  const finishRound=()=>{cancelAnimationFrame(raf.current);setPhase('crashed');setMulti(threshold.current);draw(threshold.current);if(activeStake.current>0&&!betCashedOut.current){const loss=-activeStake.current;walletRef.current.recordRound(activeStake.current,loss);setRoundResult({profit:loss})}activeStake.current=0;activeAutoTarget.current=undefined;betCashedOut.current=false;setStatus('idle');phaseTimer.current=window.setTimeout(beginCountdown,850)}
  const startRound=()=>{if(disposed)return;threshold.current=crashPoint();liveMulti.current=1;nextNoticeAt.current=1.05+Math.random()*.12;setCashouts([]);setPhase('running');setMulti(1);draw(1);const queued=queuedBet.current;queuedBet.current=null;setBetQueued(false);if(queued&&walletRef.current.debit(queued.stake)){activeStake.current=queued.stake;activeAutoTarget.current=queued.target;betCashedOut.current=false;setStatus('active')}else{activeStake.current=0;activeAutoTarget.current=undefined;setStatus('idle')}const begun=performance.now();const tick=(now:number)=>{if(disposed)return;const m=Math.exp((now-begun)/8500);liveMulti.current=m;draw(m);setMulti(m);if(m>=nextNoticeAt.current&&m<threshold.current)addBotCashout(m);if(activeAutoTarget.current&&activeAutoTarget.current<threshold.current&&m>=activeAutoTarget.current)settleCashout(activeAutoTarget.current);if(m>=threshold.current){finishRound();return}raf.current=requestAnimationFrame(tick)};raf.current=requestAnimationFrame(tick)}
  startRound()
  return()=>{disposed=true;cancelAnimationFrame(raf.current);clearTimeout(phaseTimer.current);clearInterval(phaseTimer.current)}
 },[])

 const panel=<BetController amount={amount} setAmount={setAmount} status={status} onAction={status==='active'?cashout:()=>queueForNextRound()} onAutoAction={()=>queueForNextRound(autoCashout)} autoTarget={autoCashout} setAutoTarget={setAutoCashout} canCashOut={status==='active'} disabled={amount>wallet.balance} potential={activeStake.current*multi} lastResult={roundResult} idleLabel="Bet Next Round" lockedLabel={betQueued?'Bet Queued':'Round Active'} hideChildrenInAuto><div className="rounded-lg bg-[#0c1623] p-3 text-xs text-slate-400">The live round runs independently. Bets placed now enter the next round.</div></BetController>
 return <><GameShell title="Crash" onBack={onBack} panel={panel}><div className="relative h-[430px] w-full max-w-[900px] overflow-hidden rounded-xl"><canvas ref={canvas} className="h-full w-full"/><div className="pointer-events-none absolute left-3 top-3 z-10 rounded-full border border-lime/20 bg-[#102331]/90 px-3 py-1.5 text-[10px] font-extrabold uppercase tracking-widest text-lime">{betQueued?'Bet queued for next round':phase==='running'?'Live round':'Round ended'}</div><div className="pointer-events-none absolute right-3 top-3 z-10 flex w-[min(320px,82%)] flex-col items-end gap-2">{cashouts.map(item=><div key={item.id} className={`animate-pop rounded-lg border px-3 py-2 text-xs shadow-xl backdrop-blur ${item.isYou?'border-lime/40 bg-lime/15':'border-white/10 bg-[#132235]/90'}`}><span className={item.isYou?'font-bold text-lime':'font-bold text-white'}>{item.username}</span><span className="text-slate-300"> cashed out at </span><b className="text-lime">{item.multiplier.toFixed(2)}×</b><span className="ml-1 font-bold text-lime">(+⬡ {item.profit.toLocaleString()})</span></div>)}</div><div className="pointer-events-none absolute inset-0 flex items-center justify-center text-center">{phase==='running'?<div className="font-display text-6xl font-extrabold text-lime sm:text-8xl">{multi.toFixed(2)}×</div>:phase==='crashed'?<div><div className="font-display text-5xl font-extrabold text-red-400 sm:text-7xl">CRASHED</div><div className="mt-2 text-xl font-extrabold text-red-300">{multi.toFixed(2)}×</div></div>:<div><div className="text-sm font-extrabold uppercase tracking-[.25em] text-slate-400">Next round starting in</div><div className="mt-2 font-display text-8xl font-extrabold text-white">{countdown}</div></div>}</div></div></GameShell><ResultPopup result={roundResult} onClose={()=>setRoundResult(null)}/></>
}
