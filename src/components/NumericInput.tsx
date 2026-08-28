import { InputHTMLAttributes, useEffect, useRef, useState } from 'react'

type Props=Omit<InputHTMLAttributes<HTMLInputElement>,'type'|'value'|'onChange'|'min'|'max'> & {
 value:number
 onCommit:(value:number)=>void
 min?:number
 max?:number
 integer?:boolean
}

export default function NumericInput({value,onCommit,min,max,integer=false,onBlur,onFocus,onKeyDown,...props}:Props){
 const [draft,setDraft]=useState(String(value))
 const focused=useRef(false)
 useEffect(()=>{if(!focused.current)setDraft(String(value))},[value])
 const commit=()=>{
  let next=Number(draft)
  if(!Number.isFinite(next))next=value
  if(integer)next=Math.floor(next)
  if(min!==undefined)next=Math.max(min,next)
  if(max!==undefined)next=Math.min(max,next)
  setDraft(String(next))
  onCommit(next)
 }
 return <input {...props} type="text" inputMode={integer?'numeric':'decimal'} value={draft} onChange={event=>setDraft(event.target.value)} onFocus={event=>{focused.current=true;event.currentTarget.select();onFocus?.(event)}} onBlur={event=>{focused.current=false;commit();onBlur?.(event)}} onKeyDown={event=>{if(event.key==='Enter')event.currentTarget.blur();if(event.key==='Escape'){setDraft(String(value));event.currentTarget.blur()}onKeyDown?.(event)}}/>
}
