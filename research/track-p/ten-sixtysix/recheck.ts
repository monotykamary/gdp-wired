import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {countedObligations,mcGoal,checkMC} from '../../../kernel/kernel.ts';
const bytes=readFileSync('research/track-p/input/family.json'),d=JSON.parse(bytes.toString());
for(const idx of [10,66]){const base='research/track-p/ten-sixtysix/input/c'+idx+'/',g=JSON.parse(readFileSync(base+'goal.json','utf8')),p=JSON.parse(readFileSync(base+'proof.json','utf8')),s=JSON.parse(readFileSync(base+'source.json','utf8')),family=s.familyIndices.map((i:number)=>d.laws[i]),own=d.laws[idx];
const {goal:raw,decls}=countedObligations(d.machine,family,{[own.name]:s.instances},family.indexOf(own))[1]!;
const gg=mcGoal(raw.hyps,decls,p),r={idx,searchCalls:0,fixtureHashMatches:createHash('sha256').update(bytes).digest('hex')===s.fixtureSHA256,originalRawMatches:JSON.stringify(raw)===JSON.stringify(g.raw),originalDeclsMatch:JSON.stringify(decls)===JSON.stringify(g.decls),encodedGoalMatches:JSON.stringify(gg)===JSON.stringify(g.gg),checkMC:checkMC(raw.hyps,decls,p),emptyCount:p.insts.length===0&&p.reads.length===0,hyps:gg?.hyps.length}; console.log(JSON.stringify(r));if(!r.fixtureHashMatches||!r.originalRawMatches||!r.originalDeclsMatch||!r.encodedGoalMatches||!r.checkMC)process.exitCode=1;}
