import { createContext, ReactNode, useCallback, useContext, useEffect, useMemo, useState } from 'react'
import { casinoApi } from './casinoApi'

export type CasinoStats={wagered:number;profit:number;wins:number;losses:number;history:number[]}
type Wallet = { balance:number; loading:boolean; syncBalance:(balance:number)=>void; refresh:()=>Promise<void>; stats:CasinoStats; recordRound:(stake:number,profit:number)=>void; resetStats:()=>void }
const WalletContext = createContext<Wallet | null>(null)

export function CasinoWalletProvider({children}:{children:ReactNode}){
  const [balance,setBalance] = useState(0)
  const [loading,setLoading]=useState(true)
  const [stats,setStats]=useState<CasinoStats>({wagered:0,profit:0,wins:0,losses:0,history:[0]})
  const syncBalance=useCallback((next:number)=>{
    const safe=Math.max(0,Math.floor(Number(next)||0))
    setBalance(safe)
    if(window.parent!==window) window.parent.postMessage({type:'sclshi:credits',credits:safe},window.location.origin)
  },[])
  const refresh=useCallback(async()=>{
    try{
      const data=await casinoApi<{balance:number}>('/wallet')
      syncBalance(data.balance)
    }finally{
      setLoading(false)
    }
  },[syncBalance])
  useEffect(()=>{
    void refresh().catch(()=>{})
    const onFocus=()=>void refresh().catch(()=>{})
    const onVisible=()=>{if(document.visibilityState==='visible') onFocus()}
    window.addEventListener('focus',onFocus)
    document.addEventListener('visibilitychange',onVisible)
    return()=>{window.removeEventListener('focus',onFocus);document.removeEventListener('visibilitychange',onVisible)}
  },[refresh])
  const value=useMemo<Wallet>(()=>({
    balance,
    loading,
    syncBalance,
    refresh,
    stats,
    recordRound:(stake,profit)=>setStats(current=>{const nextProfit=current.profit+Math.floor(profit);return {wagered:current.wagered+Math.floor(stake),profit:nextProfit,wins:current.wins+(profit>=0?1:0),losses:current.losses+(profit<0?1:0),history:[...current.history.slice(-39),nextProfit]}}),
    resetStats:()=>setStats({wagered:0,profit:0,wins:0,losses:0,history:[0]})
  }),[balance,loading,refresh,stats,syncBalance])
  return <WalletContext.Provider value={value}>{children}</WalletContext.Provider>
}
export function useCasinoWallet(){ const value=useContext(WalletContext); if(!value) throw new Error('Wallet provider missing'); return value }
