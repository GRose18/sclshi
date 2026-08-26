import { ReactNode } from 'react'
import { ArrowLeft, BarChart3, Heart, Volume2 } from 'lucide-react'

export default function GameShell({title,onBack,panel,children}:{title:string;onBack:()=>void;panel:ReactNode;children:ReactNode}){
 return <main className="mx-auto w-full max-w-[1440px] px-3 pb-10 pt-5 sm:px-6">
  <button onClick={onBack} className="mb-4 flex items-center gap-2 text-sm font-semibold text-slate-400 hover:text-white"><ArrowLeft size={16}/> Back to lobby</button>
  <div className="overflow-hidden rounded-2xl border border-white/5 bg-[#101b2a] shadow-2xl shadow-black/20">
   <div className="flex min-h-[610px] flex-col-reverse lg:flex-row">{panel}<section className="relative flex min-h-[500px] flex-1 items-center justify-center overflow-hidden bg-[radial-gradient(circle_at_50%_35%,#21344a_0%,#111d2c_62%,#0d1724_100%)] p-4 sm:p-8">{children}</section></div>
   <div className="flex h-14 items-center justify-between border-t border-white/5 px-5"><div className="flex items-center gap-3 text-slate-500"><Volume2 size={17}/><Heart size={17}/><BarChart3 size={17}/></div><h2 className="font-display text-sm font-extrabold tracking-wide">{title}</h2><div className="rounded-full bg-white/5 px-3 py-1 text-[10px] font-bold uppercase tracking-widest text-slate-500">Original</div></div>
  </div>
 </main>
}
