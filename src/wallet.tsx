import { createContext, ReactNode, useContext, useMemo, useState } from 'react'

type Wallet = { balance:number; debit:(amount:number)=>boolean; credit:(amount:number)=>void; reset:()=>void }
const WalletContext = createContext<Wallet | null>(null)
const STARTING_BALANCE = 10_000

export function CasinoWalletProvider({children}:{children:ReactNode}){
  const [balance,setBalance] = useState(()=>Number(localStorage.getItem('obsidian-demo-balance')) || STARTING_BALANCE)
  const persist = (next:number) => { const safe=Math.max(0,Math.round(next*100)/100); localStorage.setItem('obsidian-demo-balance',String(safe)); return safe }
  const value=useMemo<Wallet>(()=>({
    balance,
    debit:(amount)=>{ if(!Number.isFinite(amount)||amount<=0||amount>balance) return false; setBalance(v=>persist(v-amount)); return true },
    credit:(amount)=>{ if(Number.isFinite(amount)&&amount>0) setBalance(v=>persist(v+amount)) },
    reset:()=>setBalance(persist(STARTING_BALANCE))
  }),[balance])
  return <WalletContext.Provider value={value}>{children}</WalletContext.Provider>
}
export function useCasinoWallet(){ const value=useContext(WalletContext); if(!value) throw new Error('Wallet provider missing'); return value }
