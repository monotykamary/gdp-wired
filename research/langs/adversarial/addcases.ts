import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
const d=import.meta.dir, f=`${d}/cases.json`, cs=JSON.parse(readFileSync(f,'utf8'))
for (const [id,attack,code] of [
['j03','answered callback handed this',`public class Meter {
  interface Listener { boolean enabled(Meter m); }
  Listener listener; int n;
  public Meter(Listener listener) { this.listener = listener; }
  public void tick() { if (listener.enabled(this)) n = 0; }
}`],
['j04','keyed get extra argument aliases this',`public class Meter {
  interface Repo { Integer get(String key, Meter m); }
  Repo repo; int n;
  public Meter(Repo repo) { this.repo = repo; }
  public void tick() { repo.get("k", this); }
}`]
]) {mkdirSync(`${d}/${id}`,{recursive:true}); writeFileSync(`${d}/${id}/Meter.java`,`// PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))\n${code}\n`); cs.push({id,lang:'Java',attack,pred:'needs a tag',file:`${id}/Meter.java`})}
writeFileSync(f,JSON.stringify(cs,null,2))
