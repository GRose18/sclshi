import { useEffect, useMemo, useRef, useState } from 'react'
import BetController from '../components/BetController'
import GameShell from '../components/GameShell'
import ResultPopup, { RoundResult } from '../components/ResultPopup'
import { Risk } from '../types'
import { useCasinoWallet } from '../wallet'
import { postCasino } from '../casinoApi'
import NumericInput from '../components/NumericInput'

type PlinkoResponse={path:number[];slotIndex:number;multiplier:number;payout:number;profit:number;balanceAfterBet:number;newBalance:number}

const profiles:Record<Risk,{floor:number;power:number}>={Low:{floor:0.5,power:2},Medium:{floor:0.3,power:3.5},High:{floor:0.2,power:5}}
function combination(n:number,k:number){let result=1;for(let i=1;i<=k;i++)result=result*(n-k+i)/i;return result}
function payouts(rows:number,risk:Risk){
 const {floor,power}=profiles[risk]
 const expectation=Array.from({length:rows+1},(_,i)=>combination(rows,i)/2**rows*Math.abs((i-rows/2)/(rows/2))**power).reduce((sum,value)=>sum+value,0)
 const peak=floor+(0.99-floor)/expectation
 return Array.from({length:rows+1},(_,i)=>Math.floor((floor+(peak-floor)*Math.abs((i-rows/2)/(rows/2))**power)*100)/100)
}
export default function Plinko({onBack}:{onBack:()=>void}){
 const {syncBalance,balance,recordRound}=useCasinoWallet(); const [amount,setAmount]=useState(10); const [rows,setRows]=useState(12); const [risk,setRisk]=useState<Risk>('Medium'); const [ball,setBall]=useState<{x:number;y:number}|null>(null); const [status,setStatus]=useState<'idle'|'locked'>('idle'); const [result,setResult]=useState<string>('Drop a ball to play'); const [roundResult,setRoundResult]=useState<RoundResult|null>(null); const [landingIndex,setLandingIndex]=useState<number|null>(null); const intervalRef=useRef(0); const ballHideRef=useRef(0); const settleRef=useRef(0)
 const bins=useMemo(()=>payouts(rows,risk),[rows,risk]); const pegs=useMemo(()=>Array.from({length:rows},(_,r)=>Array.from({length:r+3},(_,c)=>({x:250+(c-(r+2)/2)*(310/(rows+2)),y:40+r*(315/rows)}))).flat(),[rows])
 const play=async()=>{if(status!=='idle'||amount>balance)return;setRoundResult(null);setLandingIndex(null);setStatus('locked');setResult('Preparing ball…');try{const response=await postCasino<PlinkoResponse>('/plinko',{betAmount:amount,rows,risk:risk.toLowerCase()});syncBalance(response.balanceAfterBet);setResult('Ball in play…');let r=0,x=250;const step=155/(rows+1);const path=response.path.map(direction=>(x+=(direction?1:-1)*step));setBall({x:250,y:15});intervalRef.current=window.setInterval(()=>{if(r<rows){setBall({x:path[r],y:50+r*(315/rows)});r++}else{clearInterval(intervalRef.current);const idx=response.slotIndex;const multi=response.multiplier;const binX=92+idx*(316/bins.length)+(Math.max(8,310/bins.length)/2);setBall({x:binX,y:368});setLandingIndex(idx);setResult(`${multi.toLocaleString()}× landed`);ballHideRef.current=window.setTimeout(()=>setBall(null),420);settleRef.current=window.setTimeout(()=>{syncBalance(response.newBalance);recordRound(amount,response.profit);setResult(`${multi.toLocaleString()}× · ⬡ ${response.payout.toLocaleString()}`);setRoundResult({profit:response.profit});setStatus('idle')},650)}},135)}catch(error){setBall(null);setResult(error instanceof Error?error.message:'Unable to place bet');setStatus('idle')}}
 useEffect(()=>()=>{clearInterval(intervalRef.current);clearTimeout(ballHideRef.current);clearTimeout(settleRef.current)},[])
 const panel=<BetController amount={amount} setAmount={setAmount} status={status} onAction={play} disabled={amount>balance} lastResult={roundResult}>{<><Field label="Risk"><select disabled={status!=='idle'} value={risk} onChange={e=>setRisk(e.target.value as Risk)} className="control"><option>Low</option><option>Medium</option><option>High</option></select></Field><Field label="Rows"><NumericInput aria-label="Rows" disabled={status!=='idle'} value={rows} onCommit={setRows} min={8} max={16} integer className="control"/></Field></>}</BetController>
 return <><GameShell title="Plinko" onBack={onBack} panel={panel}><div className="w-full max-w-[650px]"><div className="mb-3 text-center text-sm font-bold text-lime">{result}</div><svg viewBox="0 0 500 410" className="w-full overflow-visible"><defs><filter id="glow"><feGaussianBlur stdDeviation="4" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter></defs>{pegs.map((p,i)=><circle key={i} cx={p.x} cy={p.y} r={rows>13?3:4} fill="#dbe7f3" opacity=".85"/>)}{ball&&<circle cx={ball.x} cy={ball.y} r="7" fill="#ff456c" filter="url(#glow)" style={{transition:'all 135ms ease-in'}}/>}{bins.map((m,i)=><g key={i} className={landingIndex===i?'bin-hit':''}><rect x={92+i*(316/bins.length)} y="377" width={Math.max(8,310/bins.length)} height="27" rx="3" fill={i===0||i===bins.length-1?'#ff365f':Math.abs(i-bins.length/2)>bins.length*.3?'#ff922f':'#f6d849'}/><text x={97+i*(316/bins.length)} y="394" fill="#101827" fontSize={rows>12?'6':'8'} fontWeight="800">{m}×</text></g>)}</svg></div></GameShell><ResultPopup result={roundResult} onClose={()=>setRoundResult(null)}/></>
}
function Field({label,children}:{label:string;children:React.ReactNode}){return <label className="block"><span className="mb-2 block text-xs font-semibold text-slate-400">{label}</span>{children}</label>}
