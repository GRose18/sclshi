import { createContext, ReactNode, useContext, useMemo, useState } from 'react'

type Wallet = { balance:number; debit:(amount:number)=>boolean; credit:(amount:number)=>void; reset:()=>void }
const WalletContext = createContext<Wallet | null>(null)
const STARTING_BALANCE = 10_000
const WALLET_KEY = 'sclshi-casino-demo-balance'

export function CasinoWalletProvider({children}:{children:ReactNode}){
  const [balance,setBalance] = useState(()=>Math.floor(Number(localStorage.getItem(WALLET_KEY) || localStorage.getItem('obsidian-demo-balance')) || STARTING_BALANCE))
  const persist = (next:number) => { const safe=Math.max(0,Math.floor(next)); localStorage.setItem(WALLET_KEY,String(safe)); return safe }
  const value=useMemo<Wallet>(()=>({
    balance,
    debit:(amount)=>{ const stake=Math.floor(amount); if(!Number.isFinite(stake)||stake<=0||stake>balance) return false; setBalance(v=>persist(v-stake)); return true },
    credit:(amount)=>{ if(Number.isFinite(amount)&&amount>0) setBalance(v=>persist(v+amount)) },
    reset:()=>setBalance(persist(STARTING_BALANCE))
  }),[balance])
  return <WalletContext.Provider value={value}>{children}</WalletContext.Provider>
}
export function useCasinoWallet(){ const value=useContext(WalletContext); if(!value) throw new Error('Wallet provider missing'); return value }
