import { TrendingDown, TrendingUp, X } from 'lucide-react'

export type RoundResult={profit:number;title?:string;error?:boolean}

export default function ResultPopup({result,onClose}:{result:RoundResult|null;onClose:()=>void}){
 if(!result)return null
 const won=!result.error&&result.profit>=0
 const amount=Math.abs(Math.floor(result.profit))
 return <div className="fixed inset-0 z-[100] grid place-items-center bg-[#08101c]/75 p-4 backdrop-blur-sm" onClick={onClose}>
  <div className={`animate-pop relative w-full max-w-sm overflow-hidden rounded-2xl border p-7 text-center shadow-2xl ${won?'border-lime/30 bg-[#17251e]':'border-red-400/30 bg-[#281a23]'}`} onClick={e=>e.stopPropagation()}>
   <button aria-label="Close result" onClick={onClose} className="absolute right-3 top-3 rounded-full p-2 text-slate-500 hover:bg-white/5 hover:text-white"><X size={17}/></button>
   <div className={`mx-auto mb-4 grid h-14 w-14 place-items-center rounded-full ${won?'bg-lime/15 text-lime':'bg-red-400/15 text-red-400'}`}>{won?<TrendingUp size={28}/>:<TrendingDown size={28}/>}</div>
   <div className={`text-xs font-extrabold uppercase tracking-[.22em] ${won?'text-lime':'text-red-400'}`}>{result.error?(result.title||'Something went wrong'):won?(result.title||'Profit'):'Loss'}</div>
   {!result.error&&<div className={`mt-3 font-display text-5xl font-extrabold ${won?'text-lime':'text-red-400'}`}>{won?'+':'−'}⬡ {amount.toLocaleString()}</div>}
   <p className="mt-3 text-sm text-slate-400">{result.error?'Your balance was refreshed. Please try again.':won?'Credits added to your balance.':'Your stake was lost this round.'}</p>
   <button onClick={onClose} className={`mt-6 w-full rounded-lg py-3 text-sm font-extrabold ${won?'bg-lime text-slate-950':'bg-red-400 text-white'}`}>Continue</button>
  </div>
 </div>
}
