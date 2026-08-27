import { createContext, ReactNode, useContext, useMemo, useState } from 'react'

export type CasinoStats={wagered:number;profit:number;wins:number;losses:number;history:number[]}
type Wallet = { balance:number; debit:(amount:number)=>boolean; credit:(amount:number)=>void; reset:()=>void; stats:CasinoStats; recordRound:(stake:number,profit:number)=>void; resetStats:()=>void }
const WalletContext = createContext<Wallet | null>(null)
const STARTING_BALANCE = 10_000
const WALLET_KEY = 'sclshi-casino-demo-balance'

export function CasinoWalletProvider({children}:{children:ReactNode}){
  const [balance,setBalance] = useState(()=>Math.floor(Number(localStorage.getItem(WALLET_KEY) || localStorage.getItem('obsidian-demo-balance')) || STARTING_BALANCE))
  const [stats,setStats]=useState<CasinoStats>({wagered:0,profit:0,wins:0,losses:0,history:[0]})
  const persist = (next:number) => { const safe=Math.max(0,Math.floor(next)); localStorage.setItem(WALLET_KEY,String(safe)); return safe }
  const value=useMemo<Wallet>(()=>({
    balance,
    debit:(amount)=>{ const stake=Math.floor(amount); if(!Number.isFinite(stake)||stake<=0||stake>balance) return false; setBalance(v=>persist(v-stake)); return true },
    credit:(amount)=>{ if(Number.isFinite(amount)&&amount>0) setBalance(v=>persist(v+amount)) },
    reset:()=>setBalance(persist(STARTING_BALANCE)),
    stats,
    recordRound:(stake,profit)=>setStats(current=>{const nextProfit=current.profit+Math.floor(profit);return {wagered:current.wagered+Math.floor(stake),profit:nextProfit,wins:current.wins+(profit>=0?1:0),losses:current.losses+(profit<0?1:0),history:[...current.history.slice(-39),nextProfit]}}),
    resetStats:()=>setStats({wagered:0,profit:0,wins:0,losses:0,history:[0]})
  }),[balance,stats])
  return <WalletContext.Provider value={value}>{children}</WalletContext.Provider>
}
export function useCasinoWallet(){ const value=useContext(WalletContext); if(!value) throw new Error('Wallet provider missing'); return value }
