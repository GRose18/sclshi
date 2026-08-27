import { useEffect, useRef, useState } from 'react'
import BetController from '../components/BetController'
import GameShell from '../components/GameShell'
import ResultPopup, { RoundResult } from '../components/ResultPopup'
import { useCasinoWallet } from '../wallet'

function crashPoint(){const r=Math.random();return Math.max(1,Math.floor((.99/(1-r))*100)/100)}
export default function Crash({onBack}:{onBack:()=>void}){
 const {debit,credit,balance}=useCasinoWallet(); const canvas=useRef<HTMLCanvasElement>(null);const raf=useRef(0);const [amount,setAmount]=useState(10);const [status,setStatus]=useState<'idle'|'active'>('idle');const [multi,setMulti]=useState(1);const [crashed,setCrashed]=useState(false);const [roundResult,setRoundResult]=useState<RoundResult|null>(null);const threshold=useRef(2)
 const draw=(m:number)=>{const c=canvas.current;if(!c)return;const dpr=devicePixelRatio||1,w=c.clientWidth,h=c.clientHeight;c.width=w*dpr;c.height=h*dpr;const x=c.getContext('2d')!;x.scale(dpr,dpr);x.clearRect(0,0,w,h);x.strokeStyle='#30445a';x.lineWidth=1;x.beginPath();for(let i=1;i<5;i++){x.moveTo(0,h*i/5);x.lineTo(w,h*i/5)}x.stroke();const p=Math.min(.94,(m-1)/Math.max(1,m));x.strokeStyle='#b7f34a';x.shadowColor='#b7f34a';x.shadowBlur=14;x.lineWidth=5;x.beginPath();for(let i=0;i<=80;i++){const t=i/80;x.lineTo(20+t*w*.9,h-28-Math.pow(t,2.4)*(h-65)*Math.min(1,p*1.8))}x.stroke()}
 const start=()=>{if(!debit(amount))return;setRoundResult(null);threshold.current=crashPoint();setCrashed(false);setMulti(1);setStatus('active');const begun=performance.now();const tick=(now:number)=>{const m=Math.exp((now-begun)/8500);draw(m);setMulti(m);if(m>=threshold.current){setMulti(threshold.current);setCrashed(true);setStatus('idle');setRoundResult({profit:-amount});draw(threshold.current);return}raf.current=requestAnimationFrame(tick)};raf.current=requestAnimationFrame(tick)}
 const cashout=()=>{cancelAnimationFrame(raf.current);const payout=Math.floor(amount*multi);credit(payout);setStatus('idle');setCrashed(false);setRoundResult({profit:payout-amount,title:'Cash-out profit'})}
 useEffect(()=>{draw(1);return()=>cancelAnimationFrame(raf.current)},[])
 const panel=<BetController amount={amount} setAmount={setAmount} status={status} onAction={status==='active'?cashout:start} canCashOut={status==='active'} disabled={amount>balance} potential={amount*multi}><div className="rounded-lg bg-[#0c1623] p-3 text-xs text-slate-400">The curve accelerates over time. Cash out before it disappears.</div></BetController>
 return <><GameShell title="Crash" onBack={onBack} panel={panel}><div className="relative h-[430px] w-full max-w-[900px]"><canvas ref={canvas} className="h-full w-full"/><div className={`pointer-events-none absolute inset-0 flex items-center justify-center font-display text-6xl font-extrabold sm:text-8xl ${crashed?'text-red-400':'text-lime'}`}>{crashed?'CRASHED':`${multi.toFixed(2)}×`}</div></div></GameShell><ResultPopup result={roundResult} onClose={()=>setRoundResult(null)}/></>
}
