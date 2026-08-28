export class CasinoApiError extends Error {
  status:number
  data:Record<string,unknown>
  constructor(message:string,status:number,data:Record<string,unknown>={}){
    super(message)
    this.status=status
    this.data=data
  }
}

export async function casinoApi<T>(path:string,options:RequestInit={}):Promise<T>{
  const token=localStorage.getItem('ew_token')
  if(!token) throw new CasinoApiError('Sign in to use the casino.',401)
  const response=await fetch(`/api/casino${path}`,{
    ...options,
    headers:{
      'Content-Type':'application/json',
      Authorization:`Bearer ${token}`,
      ...(options.headers||{}),
    },
  })
  const data=await response.json().catch(()=>({})) as Record<string,unknown>
  if(!response.ok) throw new CasinoApiError(String(data.error||'Casino request failed'),response.status,data)
  return data as T
}

export function postCasino<T>(path:string,body:Record<string,unknown>):Promise<T>{
  return casinoApi<T>(path,{method:'POST',body:JSON.stringify(body)})
}
