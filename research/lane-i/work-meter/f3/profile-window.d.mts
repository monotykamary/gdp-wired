export type ProfileWindow = {stack: Array<{functionName:string,scriptId:string,url:string,lineNumber:number,columnNumber:number}>,timing:{valid:boolean,[key:string]:unknown}}
export function selectProfileWindow(profile:unknown,quietWindowMs:number):ProfileWindow
