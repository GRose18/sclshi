import { useEffect, useState } from 'react'
import { Bell, Menu, Search, ShieldCheck, Wallet, X } from 'lucide-react'
import Lobby from './Lobby'
import Plinko from './games/Plinko'
import Mines from './games/Mines'
import Crash from './games/Crash'
import Limbo from './games/Limbo'
import { GameId } from './types'
import { CasinoWalletProvider, useCasinoWallet } from './wallet'

const EMBEDDED = window.location.pathname.startsWith('/casino-embed')
const CASINO_BASE = EMBEDDED ? '/casino-embed' : '/casino'

function Header(){const {balance,loading}=useCasinoWallet();const [menu,setMenu]=useState(false);return <><div className="bg-lime py-1.5 text-center text-[10px] font-extrabold uppercase tracking-[.18em] text-slate-950">Sclshi credits · no cash deposits or prizes</div><header className="sticky top-0 z-50 border-b border-white/5 bg-[#0d1522]/90 backdrop-blur-xl"><div className="mx-auto flex h-16 max-w-[1500px] items-center justify-between px-4 sm:px-7"><button onClick={()=>setMenu(!menu)} className="mr-3 text-slate-400 lg:hidden">{menu?<X/>:<Menu/>}</button><a href="/" className="font-display text-xl font-extrabold tracking-[-.06em] sm:text-2xl">SCLSHI<span className="text-lime">°</span></a><nav className="ml-10 hidden items-center gap-7 text-sm font-bold text-slate-400 lg:flex"><a className="text-white" href="/">Casino</a><a href="/">Originals</a><a href="#">Promotions</a><a href="#">Live</a></nav><div className="ml-auto flex items-center gap-2 sm:gap-3"><button className="hidden rounded-lg p-2.5 text-slate-400 hover:bg-white/5 sm:block"><Search size={18}/></button><div className="flex h-10 items-center rounded-lg border border-white/5 bg-[#172334]"><div className="flex h-full items-center gap-2 px-3"><span className="font-bold text-lime">⬡</span><span className="text-xs font-bold tabular-nums sm:text-sm">{loading?'—':balance.toLocaleString()}</span></div></div><button className="hidden h-10 items-center gap-2 rounded-lg bg-lime px-4 text-xs font-extrabold text-slate-950 sm:flex"><Wallet size={15}/> Credits</button><button className="rounded-lg p-2.5 text-slate-400 hover:bg-white/5"><Bell size={18}/></button></div></div>{menu&&<nav className="flex flex-col gap-4 border-t border-white/5 px-5 py-5 text-sm font-bold text-slate-300 lg:hidden"><a href="/">Originals</a><a href="#">Promotions</a><a href="#">Live casino</a></nav>}</header></>}

function gameFromPath():GameId|null{const value=window.location.pathname.split('/')[2];return ['plinko','mines','crash','limbo'].includes(value)?value as GameId:null}
function Casino(){const [game,setGame]=useState<GameId|null>(gameFromPath);const open=(next:GameId)=>{setGame(next);history.pushState({},'',`${CASINO_BASE}/${next}`)};const back=()=>{setGame(null);history.pushState({},'',CASINO_BASE)};useEffect(()=>{const onPop=()=>setGame(gameFromPath());addEventListener('popstate',onPop);return()=>removeEventListener('popstate',onPop)},[]);return <div className="min-h-screen bg-ink text-white">{!EMBEDDED&&<Header/>}{game==='plinko'?<Plinko onBack={back}/>:game==='mines'?<Mines onBack={back}/>:game==='crash'?<Crash onBack={back}/>:game==='limbo'?<Limbo onBack={back}/>:<Lobby open={open}/>} {!EMBEDDED&&<footer className="border-t border-white/5 px-5 py-8 text-center text-xs text-slate-600"><div className="mb-2 flex justify-center gap-2"><ShieldCheck size={15}/> Local simulation only</div>For entertainment and interface demonstration. No deposits, withdrawals, or prizes.</footer>}</div>}
export default function App(){return <CasinoWalletProvider><Casino/></CasinoWalletProvider>}
