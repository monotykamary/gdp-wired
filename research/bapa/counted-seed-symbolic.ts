// Small symbolic fixture only: this is not the toy consensus protocol.
// Its count definition and supporting candidate are read from the sealed toy capture.
import {writeFileSync} from 'node:fs'
import type {E,Machine,Law} from '../../core/machine.ts'
import {proveCountedCandidateSeeds} from '../../core/counted-candidate-seeds.ts'
import {checkCountedLaws} from '../../kernel/kernel.ts'
import {loadCandidateSeedManifest} from './candidate-seed-manifest.ts'
const n=(value:number):E=>({op:'const',value})
const target:Machine={name:'small retained counted fixture',params:['size','values'],inputs:[],state:{},maps:{Vote:0,Decided:0},step:{}}
const loaded=loadCandidateSeedManifest('research/bapa/counted-seed-toy.manifest.json',target)
if(loaded.kind!=='counted')throw Error('not a counted family')
const item=loaded.audit.laws[3]
if(!item || item.status!=='candidate')throw Error(`retained count law refused: ${JSON.stringify(item)}`)
const publicLaw:Law={name:'zero equals zero',holds:{op:'=',a:n(0),b:n(0)}}
const machine={...target,counts:loaded.counts}
// Admission may legitimately prune an unused true proposal. Check the actual
// retained formula as a protected goal of this separate small fixture as well.
const out=proveCountedCandidateSeeds(machine,[item.law],[publicLaw],30000)
if(out.status!=='checked' || !out.closure.laws.includes(item.law) || !out.closure.proof || !checkCountedLaws(out.closure.m,out.closure.laws,out.closure.proof))throw Error(`counted candidate family not checked: ${JSON.stringify({status:out.status,...(out.status==='inconclusive'?{reason:out.reason}:{laws:out.closure.laws.map(l=>l.name)})})}`)
writeFileSync(`${process.env.SUPERCOMPUTER_OUTPUT_DIR}/counted-seed-symbolic.json`,JSON.stringify({audit:loaded.audit,kept:out.kept.map(l=>l.name),dropped:out.dropped.map(l=>l.name),checked:true},null,2)+'\n')
console.log('retained count law and definition checked in small symbolic fixture')
