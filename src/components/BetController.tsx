import { Infinity as InfinityIcon } from 'lucide-react'
import { ReactNode, useEffect, useRef, useState } from 'react'
import { BetStatus } from '../types'
import { useCasinoWallet } from '../wallet'
import NumericInput from './NumericInput'

type Result={profit:number}
type Props={amount:number;setAmount:(n:number)=>void;status:BetStatus;onAction:()=>void;onAutoAction?:()=>void;canCashOut?:boolean;disabled?:boolean;autoDisabled?:boolean;children?:ReactNode;potential?:number;autoTarget?:number;setAutoTarget?:(value:number)=>void;autoTargetLabel?:string;lastResult?:Result|null;idleLabel?:string;lockedLabel?:string;hideChildrenInAuto?:boolean;onModeChange?:(mode:'manual'|'auto')=>void}

export default function BetController({amount,setAmount,status,onAction,onAutoAction,canCashOut=false,disabled=false,autoDisabled=false,children,potential,autoTarget,setAutoTarget,autoTargetLabel='Cashout At',lastResult,idleLabel='Place bet',lockedLabel='Bet active',hideChildrenInAuto=false,onModeChange}:Props){
 const {balance}=useCasinoWallet()
 const [mode,setMode]=useState<'manual'|'auto'>('manual')
 const [autoTab,setAutoTab]=useState<'controls'|'leaderboard'>('controls')
 const [games,setGames]=useState(0)
 const [completed,setCompleted]=useState(0)
 const [autoRunning,setAutoRunning]=useState(false)
 const [onWin,setOnWin]=useState<'reset'|'increase'>('reset')
 const [onLoss,setOnLoss]=useState<'reset'|'increase'>('increase')
 const [winIncrease,setWinIncrease]=useState(0)
 const [lossIncrease,setLossIncrease]=useState(100)
 const [stopGain,setStopGain]=useState(0)
 const [stopLoss,setStopLoss]=useState(0)
 const [netGain,setNetGain]=useState(0)
 const timer=useRef(0)
 const actionRef=useRef(onAction)
 const autoActionRef=useRef(onAutoAction)
 actionRef.current=onAction
 autoActionRef.current=onAutoAction
 const startingAmount=useRef(amount)
 const processedResult=useRef<Result|null|undefined>(lastResult)
 const label=status==='idle'?idleLabel:canCashOut?'Cash out':lockedLabel

 useEffect(()=>{if(!autoRunning||!lastResult||processedResult.current===lastResult)return;processedResult.current=lastResult;const nextNet=netGain+lastResult.profit;const nextCompleted=completed+1;setNetGain(nextNet);setCompleted(nextCompleted);if(lastResult.profit>=0){setAmount(onWin==='reset'?startingAmount.current:Math.max(1,Math.floor(amount*(1+winIncrease/100))))}else{setAmount(onLoss==='reset'?startingAmount.current:Math.max(1,Math.floor(amount*(1+lossIncrease/100))))}if((games>0&&nextCompleted>=games)||(stopGain>0&&nextNet>=stopGain)||(stopLoss>0&&nextNet<=-stopLoss))setAutoRunning(false)},[lastResult,autoRunning,amount,completed,games,netGain,onLoss,onWin,lossIncrease,winIncrease,stopGain,stopLoss,setAmount])
 useEffect(()=>{clearTimeout(timer.current);if(!autoRunning||status!=='idle')return;if(amount>balance){setAutoRunning(false);return}timer.current=window.setTimeout(()=>(autoActionRef.current||actionRef.current)(),550);return()=>clearTimeout(timer.current)},[autoRunning,status,amount,balance,completed])
 useEffect(()=>()=>clearTimeout(timer.current),[])

 const changeMode=(next:'manual'|'auto')=>{if(autoRunning||status!=='idle')return;setMode(next);onModeChange?.(next)}
 const toggleAuto=()=>{if(autoRunning){setAutoRunning(false);return}if(status!=='idle'||disabled||autoDisabled||amount>balance)return;startingAmount.current=amount;processedResult.current=lastResult;setCompleted(0);setNetGain(0);setAutoRunning(true)}
 const remaining=games===0?'∞':Math.max(0,games-completed).toLocaleString()
 const netGainOnWin=Math.max(0,Math.floor(amount*((autoTarget||2)-1)))

 return <aside className="glass w-full shrink-0 rounded-2xl border border-white/5 p-4 lg:w-[320px] lg:rounded-r-none">
  <div className="mb-4 flex rounded-full border-4 border-[#0d1725] bg-[#0d1725]"><button onClick={()=>changeMode('manual')} className={`flex-1 rounded-full py-2.5 text-sm font-bold ${mode==='manual'?'bg-[#30485b] text-white':'text-slate-400'}`}>Manual</button><button onClick={()=>changeMode('auto')} className={`flex-1 rounded-full py-2.5 text-sm font-bold ${mode==='auto'?'bg-[#30485b] text-white':'text-slate-400'}`}>Auto</button></div>
  {mode==='auto'?<div className="mb-4 grid grid-cols-2 overflow-hidden rounded bg-[#0d1e2c]"><button onClick={()=>setAutoTab('controls')} className={`py-2.5 text-xs font-bold ${autoTab==='controls'?'bg-[#0b2130] text-sky-300':'bg-[#2d4558] text-white'}`}>Controls</button><button onClick={()=>setAutoTab('leaderboard')} className={`py-2.5 text-xs font-bold ${autoTab==='leaderboard'?'bg-[#0b2130] text-sky-300':'bg-[#2d4558] text-white'}`}>Leaderboard</button></div>:null}
  <label className="mb-2 flex justify-between text-xs font-semibold text-slate-400"><span>Amount</span><span>⬡ {amount.toLocaleString()}</span></label>
  <div className="flex overflow-hidden rounded border border-[#365267] bg-[#0b1d2a] focus-within:border-sky-400/60"><div className="flex flex-1 items-center gap-2 px-3"><NumericInput aria-label="Bet amount" disabled={status!=='idle'||autoRunning} value={amount} onCommit={setAmount} min={1} integer className="w-full bg-transparent py-3 text-sm font-bold outline-none"/><span className="text-sm font-bold text-lime">⬡</span></div><button disabled={status!=='idle'||autoRunning} onClick={()=>setAmount(Math.max(1,Math.floor(amount/2)))} className="border-l border-[#365267] px-3 text-xs font-bold text-slate-300 hover:bg-white/5">½</button><button disabled={status!=='idle'||autoRunning} onClick={()=>setAmount(Math.min(balance,amount*2))} className="border-l border-[#365267] px-3 text-xs font-bold text-slate-300 hover:bg-white/5">2×</button></div>
  {mode==='manual'?<div className="my-5 space-y-4">{children}</div>:autoTab==='leaderboard'?<Leaderboard/>:<div className={`my-4 space-y-4 ${autoRunning?'pointer-events-none opacity-80':''}`}>{hideChildrenInAuto?null:<div className="space-y-4">{children}</div>}<div className={`grid gap-2 ${setAutoTarget?'grid-cols-2':'grid-cols-1'}`}>{setAutoTarget&&autoTarget!==undefined?<AutoField label={autoTargetLabel}><div className="flex items-center rounded border border-[#365267] bg-[#0b1d2a] px-2"><NumericInput aria-label={autoTargetLabel} value={autoTarget} onCommit={setAutoTarget} min={1.01} className="w-full bg-transparent py-2.5 font-bold outline-none"/><b className="text-slate-500">×</b></div></AutoField>:null}<AutoField label="Number of Games"><div className="flex items-center rounded border border-[#365267] bg-[#0b1d2a] px-2"><NumericInput aria-label="Number of games" value={games} onCommit={setGames} min={0} integer className="w-full bg-transparent py-2.5 font-bold outline-none"/>{games===0?<InfinityIcon size={18} className="text-slate-400"/>:null}</div></AutoField></div><StrategyRow label="On Win" mode={onWin} setMode={setOnWin} percent={winIncrease} setPercent={setWinIncrease}/><StrategyRow label="On Loss" mode={onLoss} setMode={setOnLoss} percent={lossIncrease} setPercent={setLossIncrease}/><CreditField label="Stop on Net Gain" value={stopGain} setValue={setStopGain}/><CreditField label="Stop on Loss" value={stopLoss} setValue={setStopLoss}/><div className="rounded bg-[#294052] p-3"><div className="text-xs font-semibold text-slate-400">Net Gain on Win</div><div className="mt-1 flex justify-between font-bold"><span>{netGainOnWin.toLocaleString()}</span><span className="text-lime">⬡</span></div></div></div>}
  {potential&&status==='active'?<div className="mb-3 flex justify-between rounded-lg bg-lime/10 px-3 py-2 text-xs"><span className="text-slate-400">Cashout value</span><b className="text-lime">⬡ {Math.floor(potential).toLocaleString()}</b></div>:null}
  {mode==='manual'?<button onClick={onAction} disabled={disabled||(status!=='idle'&&!canCashOut)} className={`w-full rounded py-3.5 text-sm font-extrabold transition active:scale-[.98] disabled:cursor-not-allowed disabled:opacity-50 ${canCashOut?'bg-amber-400 text-slate-950 hover:bg-amber-300':'bg-lime text-slate-950 hover:bg-[#c6fa66]'}`}>{label}</button>:<button onClick={toggleAuto} disabled={!autoRunning&&(disabled||autoDisabled||status!=='idle')} className={`w-full rounded py-3.5 text-sm font-extrabold transition active:scale-[.98] disabled:cursor-not-allowed disabled:opacity-50 ${autoRunning?'bg-red-400 text-slate-950':'bg-[#16ea37] text-slate-950'}`}>{autoRunning?`Stop Auto Bet · ${remaining}`:'Start Auto Bet'}</button>}
  <div className="mt-4 flex items-center justify-between border-t border-white/5 pt-4 text-[10px] font-semibold uppercase tracking-wider text-slate-500"><span>{mode==='auto'?`Net ${netGain>=0?'+':''}${netGain.toLocaleString()}`:'Account credits'}</span><span>Server settled</span></div>
 </aside>
}

function AutoField({label,children}:{label:string;children:ReactNode}){return <label className="block"><span className="mb-1.5 block text-xs font-semibold text-slate-400">{label}</span>{children}</label>}
function StrategyRow({label,mode,setMode,percent,setPercent}:{label:string;mode:'reset'|'increase';setMode:(mode:'reset'|'increase')=>void;percent:number;setPercent:(value:number)=>void}){return <div><div className="mb-1.5 text-xs font-semibold text-slate-400">{label}</div><div className="flex overflow-hidden rounded border border-[#365267] bg-[#0b1d2a]"><button onClick={()=>setMode('reset')} className={`px-3 py-2 text-xs font-bold ${mode==='reset'?'bg-[#29465a] text-white':'text-slate-500'}`}>Reset</button><button onClick={()=>setMode('increase')} className={`border-l border-[#365267] px-2 py-2 text-xs font-bold ${mode==='increase'?'bg-[#29465a] text-white':'text-slate-500'}`}>Increase by:</button><NumericInput aria-label={`${label} increase percentage`} value={percent} onCommit={setPercent} min={0} className="min-w-0 flex-1 bg-transparent px-2 text-right font-bold outline-none"/><span className="px-2 py-2 text-slate-500">%</span></div></div>}
function CreditField({label,value,setValue}:{label:string;value:number;setValue:(value:number)=>void}){return <label className="block"><span className="mb-1.5 block text-xs font-semibold text-slate-400">{label}</span><div className="flex items-center rounded border border-[#365267] bg-[#0b1d2a] px-2"><NumericInput aria-label={label} value={value} onCommit={setValue} min={0} integer className="w-full bg-transparent py-2.5 font-bold outline-none"/><span className="text-lime">⬡</span></div></label>}
function Leaderboard(){const rows=[['LunaAce','+⬡ 8,420'],['SCLKing','+⬡ 3,106'],['Maya_22','+⬡ 1,944'],['RioWins','+⬡ 870']];return <div className="my-4 overflow-hidden rounded border border-white/5 bg-[#0b1d2a]"><div className="grid grid-cols-[34px_1fr_auto] px-3 py-2 text-[10px] font-bold uppercase tracking-wider text-slate-500"><span>#</span><span>Player</span><span>Profit</span></div>{rows.map((row,index)=><div key={row[0]} className="grid grid-cols-[34px_1fr_auto] border-t border-white/5 px-3 py-3 text-xs"><b className="text-slate-500">{index+1}</b><b>{row[0]}</b><b className="text-lime">{row[1]}</b></div>)}</div>}
