import { useEffect, useRef, useState } from 'react'
import BetController from '../components/BetController'
import GameShell from '../components/GameShell'
import ResultPopup, { RoundResult } from '../components/ResultPopup'
import { BetStatus } from '../types'
import { useCasinoWallet } from '../wallet'

type CashoutNotice={id:number;username:string;multiplier:number;profit:number;isYou?:boolean}

const usernames=['LunaAce','diamondhand','SCLKing','Maya_22','LuckyNova','crashpilot','RioWins','greenlight','Jax_91','pixelbet']
function crashPoint(){const r=Math.random();return Math.max(1,Math.floor((.99/(1-r))*100)/100)}

export default function Crash({onBack}:{onBack:()=>void}){
 const {debit,credit,balance}=useCasinoWallet()
 const canvas=useRef<HTMLCanvasElement>(null)
 const raf=useRef(0)
 const threshold=useRef(2)
 const liveMulti=useRef(1)
 const betCashedOut=useRef(false)
 const nextNoticeAt=useRef(1.08)
 const noticeId=useRef(0)
 const [amount,setAmount]=useState(10)
 const [status,setStatus]=useState<BetStatus>('idle')
 const [multi,setMulti]=useState(1)
 const [crashed,setCrashed]=useState(false)
 const [roundResult,setRoundResult]=useState<RoundResult|null>(null)
 const [cashouts,setCashouts]=useState<CashoutNotice[]>([])

 const draw=(m:number)=>{const c=canvas.current;if(!c)return;const dpr=devicePixelRatio||1,w=c.clientWidth,h=c.clientHeight;c.width=w*dpr;c.height=h*dpr;const x=c.getContext('2d')!;x.scale(dpr,dpr);x.clearRect(0,0,w,h);x.strokeStyle='#30445a';x.lineWidth=1;x.beginPath();for(let i=1;i<5;i++){x.moveTo(0,h*i/5);x.lineTo(w,h*i/5)}x.stroke();const p=Math.min(.94,(m-1)/Math.max(1,m));x.strokeStyle='#b7f34a';x.shadowColor='#b7f34a';x.shadowBlur=14;x.lineWidth=5;x.beginPath();for(let i=0;i<=80;i++){const t=i/80;x.lineTo(20+t*w*.9,h-28-Math.pow(t,2.4)*(h-65)*Math.min(1,p*1.8))}x.stroke()}
 const addCashout=(notice:Omit<CashoutNotice,'id'>)=>setCashouts(current=>[...current.slice(-3),{...notice,id:++noticeId.current}])
 const addBotCashout=(m:number)=>{const stake=10+Math.floor(Math.random()*490);addCashout({username:usernames[Math.floor(Math.random()*usernames.length)],multiplier:m,profit:Math.floor(stake*(m-1))});nextNoticeAt.current=m+Math.max(.08,m*(.08+Math.random()*.2))}
 const start=()=>{
  if(!debit(amount))return
  setRoundResult(null);setCashouts([]);threshold.current=crashPoint();nextNoticeAt.current=1.05+Math.random()*.12;betCashedOut.current=false;liveMulti.current=1;setCrashed(false);setMulti(1);setStatus('active')
  const begun=performance.now()
  const tick=(now:number)=>{const m=Math.exp((now-begun)/8500);liveMulti.current=m;draw(m);setMulti(m);if(m>=nextNoticeAt.current&&m<threshold.current)addBotCashout(m);if(m>=threshold.current){liveMulti.current=threshold.current;setMulti(threshold.current);setCrashed(true);setStatus('idle');if(!betCashedOut.current)setRoundResult({profit:-amount});draw(threshold.current);return}raf.current=requestAnimationFrame(tick)}
  raf.current=requestAnimationFrame(tick)
 }
 const cashout=()=>{
  if(status!=='active'||betCashedOut.current)return
  betCashedOut.current=true
  const at=liveMulti.current
  const payout=Math.floor(amount*at)
  credit(payout);setStatus('locked');addCashout({username:'You',multiplier:at,profit:payout-amount,isYou:true});setRoundResult({profit:payout-amount,title:'Cash-out profit'})
 }
 useEffect(()=>{draw(1);return()=>cancelAnimationFrame(raf.current)},[])
 const panel=<BetController amount={amount} setAmount={setAmount} status={status} onAction={status==='active'?cashout:start} canCashOut={status==='active'} disabled={amount>balance} potential={amount*multi}><div className="rounded-lg bg-[#0c1623] p-3 text-xs text-slate-400">Cash out before the crash. Your cash-out settles immediately while the shared round keeps running.</div></BetController>
 return <><GameShell title="Crash" onBack={onBack} panel={panel}><div className="relative h-[430px] w-full max-w-[900px] overflow-hidden rounded-xl"><canvas ref={canvas} className="h-full w-full"/><div className="pointer-events-none absolute right-3 top-3 z-10 flex w-[min(320px,82%)] flex-col items-end gap-2">{cashouts.map(item=><div key={item.id} className={`animate-pop rounded-lg border px-3 py-2 text-xs shadow-xl backdrop-blur ${item.isYou?'border-lime/40 bg-lime/15':'border-white/10 bg-[#132235]/90'}`}><span className={item.isYou?'font-bold text-lime':'font-bold text-white'}>{item.username}</span><span className="text-slate-300"> cashed out at </span><b className="text-lime">{item.multiplier.toFixed(2)}×</b><span className="ml-1 font-bold text-lime">(+⬡ {item.profit.toLocaleString()})</span></div>)}</div><div className={`pointer-events-none absolute inset-0 flex items-center justify-center font-display text-6xl font-extrabold sm:text-8xl ${crashed?'text-red-400':'text-lime'}`}>{crashed?'CRASHED':`${multi.toFixed(2)}×`}</div></div></GameShell><ResultPopup result={roundResult} onClose={()=>setRoundResult(null)}/></>
}
