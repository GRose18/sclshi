import { ReactNode } from 'react'
import { BetStatus } from '../types'
import { useCasinoWallet } from '../wallet'

type Props={amount:number;setAmount:(n:number)=>void;status:BetStatus;onAction:()=>void;canCashOut?:boolean;disabled?:boolean;children?:ReactNode;potential?:number}
export default function BetController({amount,setAmount,status,onAction,canCashOut=false,disabled=false,children,potential}:Props){
 const {balance}=useCasinoWallet(); const label=status==='idle'?'Place bet':canCashOut?'Cash out':'Bet active'
 return <aside className="glass w-full shrink-0 rounded-2xl border border-white/5 p-4 lg:w-[300px] lg:rounded-r-none">
  <div className="mb-5 flex rounded-xl bg-[#0d1725] p-1"><button className="flex-1 rounded-lg bg-[#26364a] py-2 text-sm font-semibold text-white">Manual</button><button className="flex-1 py-2 text-sm font-semibold text-slate-500">Auto</button></div>
  <label className="mb-2 flex justify-between text-xs font-semibold text-slate-400"><span>Bet amount</span><span>⬡ {amount.toLocaleString()}</span></label>
  <div className="flex overflow-hidden rounded-lg border border-white/5 bg-[#0b1421] focus-within:border-sky-400/50"><div className="flex flex-1 items-center gap-2 px-3"><span className="text-sm font-bold text-lime">⬡</span><input aria-label="Bet amount" disabled={status!=='idle'} type="number" min="1" step="1" value={amount} onChange={e=>setAmount(Math.max(1,Math.floor(Number(e.target.value)||1)))} className="w-full bg-transparent py-3 text-sm font-semibold outline-none"/></div><button disabled={status!=='idle'} onClick={()=>setAmount(Math.max(1,Math.floor(amount/2)))} className="border-l border-white/5 px-3 text-xs font-bold text-slate-300 hover:bg-white/5">½</button><button disabled={status!=='idle'} onClick={()=>setAmount(Math.min(balance,amount*2))} className="border-l border-white/5 px-3 text-xs font-bold text-slate-300 hover:bg-white/5">2×</button></div>
  <div className="my-5 space-y-4">{children}</div>
  {potential && status==='active'?<div className="mb-3 flex justify-between rounded-lg bg-lime/10 px-3 py-2 text-xs"><span className="text-slate-400">Cashout value</span><b className="text-lime">⬡ {Math.floor(potential).toLocaleString()}</b></div>:null}
  <button onClick={onAction} disabled={disabled||(status!=='idle'&&!canCashOut)} className={`w-full rounded-lg py-3.5 text-sm font-bold transition active:scale-[.98] disabled:cursor-not-allowed disabled:opacity-50 ${canCashOut?'bg-amber-400 text-slate-950 hover:bg-amber-300':'bg-lime text-slate-950 hover:bg-[#c6fa66]'}`}>{label}</button>
  <div className="mt-5 flex items-center justify-between border-t border-white/5 pt-4 text-[10px] font-semibold uppercase tracking-wider text-slate-500"><span>Demo play</span><span>Provably fair</span></div>
 </aside>
}
