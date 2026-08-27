import { RotateCcw, X } from 'lucide-react'
import { useCasinoWallet } from '../wallet'

export default function LiveStats({open,onClose}:{open:boolean;onClose:()=>void}){
 const {stats,resetStats}=useCasinoWallet()
 if(!open)return null
 const width=360,height=230,pad=18
 const values=stats.history.length>1?stats.history:[0,0]
 const low=Math.min(0,...values),high=Math.max(0,...values),range=Math.max(1,high-low)
 const points=values.map((value,index)=>`${pad+(index/(values.length-1))*(width-pad*2)},${pad+((high-value)/range)*(height-pad*2)}`).join(' ')
 const pointList=points.split(' ');const [lastX,lastY]=pointList[pointList.length-1].split(',').map(Number)
 const zeroY=pad+((high-0)/range)*(height-pad*2)
 return <div className="absolute inset-0 z-40 bg-[#08111d]/55 backdrop-blur-sm" onClick={onClose}><aside className="absolute right-0 top-0 flex h-full w-full max-w-[420px] flex-col border-l border-white/5 bg-[#152938] shadow-2xl" onClick={event=>event.stopPropagation()}><header className="flex h-16 items-center justify-between border-b border-white/5 bg-[#0d2030] px-5"><button onClick={resetStats} title="Reset live stats" className="rounded-lg p-2 text-slate-400 hover:bg-white/5 hover:text-white"><RotateCcw size={21}/></button><h3 className="font-display text-xl font-extrabold">Live Stats</h3><button onClick={onClose} className="rounded-lg p-2 text-slate-400 hover:bg-white/5 hover:text-white"><X size={22}/></button></header><div className="flex flex-1 flex-col p-6"><div className="grid grid-cols-2 gap-5"><Stat label="Wagered" value={`⬡ ${stats.wagered.toLocaleString()}`}/><Stat label="Profit" value={`${stats.profit>=0?'+':'−'}⬡ ${Math.abs(stats.profit).toLocaleString()}`} tone={stats.profit>=0?'green':'red'}/></div><div className="my-auto rounded-2xl bg-[#102331] p-3"><svg viewBox={`0 0 ${width} ${height}`} className="w-full overflow-visible"><defs><linearGradient id="statsLine" x1="0" x2="1"><stop offset="0" stopColor="#b7f34a"/><stop offset=".7" stopColor="#64dd5d"/><stop offset="1" stopColor={stats.profit<0?'#ff486d':'#b7f34a'}/></linearGradient></defs><line x1={pad} x2={width-pad} y1={zeroY} y2={zeroY} stroke="#496070" strokeDasharray="4 5" opacity=".55"/><polyline points={points} fill="none" stroke="url(#statsLine)" strokeWidth="5" strokeLinejoin="round" strokeLinecap="round"/><circle cx={lastX} cy={lastY} r="6" fill={stats.profit<0?'#ff486d':'#b7f34a'}/></svg></div><div className="grid grid-cols-2 gap-5 border-t border-white/5 pt-6"><Stat label="Wins" value={stats.wins.toLocaleString()} tone="green"/><Stat label="Losses" value={stats.losses.toLocaleString()} tone="red"/></div></div></aside></div>
}

function Stat({label,value,tone}:{label:string;value:string;tone?:'green'|'red'}){return <div><div className="text-sm font-bold text-slate-400">{label}</div><div className={`mt-1 font-display text-2xl font-extrabold ${tone==='green'?'text-lime':tone==='red'?'text-red-400':'text-white'}`}>{value}</div></div>}
