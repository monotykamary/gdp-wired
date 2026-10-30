import {writeFileSync} from 'node:fs'
const dir=import.meta.dir
const items: any[]=[]
function add(id:string,lang:string,attack:string,pred:string,code:string, opts:any={}) {const ext={Python:'py',Ruby:'rb',Java:'java',TypeScript:'ts'}[lang]!; const file=lang==='Java'?`${id}/Meter.java`:`${id}.${ext}`; if(lang==='Java') require('node:fs').mkdirSync(`${dir}/${id}`,{recursive:true}); const comment=lang==='Python'||lang==='Ruby'?'#':'//'; writeFileSync(`${dir}/${file}`,`${comment} PREDICTION: ${pred}; LAW: r.law('n stays zero', ({n}) => n.eq(0))\n${code.trim()}\n`); items.push({id,lang,attack,pred,file,...opts})}
add('p01','Python','listener handed self','needs a tag',`
from typing import Protocol
class Listener(Protocol):
    def emit(self, target: object) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.n = 0
    def tick(self) -> None:
        self.listener.emit(self)
`)
add('p02','Python','listener handed mutable state field','needs a tag',`
from typing import Protocol
class Listener(Protocol):
    def emit(self, data: dict[str, int]) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.data: dict[str, int] = {}
        self.n = 0
    def tick(self) -> None:
        self.listener.emit(self.data)
        self.n = self.data.get('n', 0)
`)
add('p03','Python','alias to self passed to listener','needs a tag',`
from typing import Protocol
class Listener(Protocol):
    def emit(self, x: object) -> None: ...
class Meter:
    def __init__(self, listener: Listener):
        self.listener = listener
        self.n = 0
    def tick(self) -> None:
        alias = self
        self.listener.emit(alias)
`)
add('p04','Python','repository save mutates held record','needs a tag',`
from typing import Protocol
from dataclasses import dataclass
@dataclass
class Row:
    n: int = 0
class Repo(Protocol):
    def save(self, key: str, row: Row) -> None: ...
class Meter:
    def __init__(self, repo: Repo):
        self.repo = repo
        self.row = Row()
        self.n = 0
    def tick(self) -> None:
        self.repo.save('one', self.row)
        self.n = self.row.n
`)
add('p05','Python','store get mutable object alias','refused',`
from typing import Protocol
from dataclasses import dataclass
@dataclass
class Row:
    n: int = 0
class Repo(Protocol):
    def get(self, key: str) -> Row: ...
class Meter:
    def __init__(self, repo: Repo):
        self.repo = repo
        self.n = 0
    def tick(self) -> None:
        row = self.repo.get('one')
        row.n += 1
        self.n = row.n
`)
add('p06','Python','skipped helper mutates global used by rule','refused',`
value = 0
def bump() -> None:
    global value
    value = 1
class Meter:
    def __init__(self):
        self.n = 0
    def tick(self) -> None:
        bump()
        self.n = value
`)
add('p07','Python','truthiness of inferred boolean answer','refuted',`
from typing import Protocol
class Flags(Protocol):
    def enabled(self) -> bool: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        if self.flags.enabled():
            self.n = 1
`)
add('p08','Python','optional None answer truthiness','refuted',`
from typing import Protocol
class Flags(Protocol):
    def value(self) -> int | None: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        value = self.flags.value()
        if value is None:
            self.n = 1
`)
add('p09','Python','untyped Any answer','needs a tag',`
from typing import Protocol, Any
class Flags(Protocol):
    def value(self) -> Any: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        if self.flags.value():
            self.n = 1
`)
add('p10','Python','async answer','refuted',`
from typing import Protocol
class Flags(Protocol):
    async def enabled(self) -> bool: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    async def tick(self) -> None:
        if await self.flags.enabled():
            self.n = 1
`)
add('p11','Python','post-construction field injection','refused',`
from typing import Protocol
class Flags(Protocol):
    def enabled(self) -> bool: ...
class Meter:
    flags: Flags
    def __init__(self):
        self.n = 0
    def tick(self) -> None:
        if self.flags.enabled():
            self.n = 1
`)
add('p12','Python','two dependencies with shared underlying store','refused',`
from typing import Protocol
class Store(Protocol):
    def get(self, key: str) -> int | None: ...
    def set(self, key: str, value: int) -> None: ...
class Meter:
    def __init__(self, a: Store, b: Store):
        self.a = a
        self.b = b
        self.n = 0
    def tick(self) -> None:
        self.a.set('k', 1)
        self.n = self.b.get('k') or 0
`)
add('p13','Python','entry discovery through private helper','refuted',`
class Meter:
    def __init__(self):
        self.n = 0
    def _write(self) -> None:
        self.n = 1
    def tick(self) -> None:
        self._write()
`,{discover:true})
add('p14','Python','overloaded declared result','refuted',`
from typing import Protocol, overload, Literal
class Flags(Protocol):
    @overload
    def value(self, key: Literal['a']) -> int: ...
    @overload
    def value(self, key: str) -> int | None: ...
class Meter:
    def __init__(self, flags: Flags):
        self.flags = flags
        self.n = 0
    def tick(self) -> None:
        self.n = self.flags.value('a')
`)
add('p15','Python','generic return TypeVar','needs a tag',`
from typing import Protocol, TypeVar
T = TypeVar('T')
class Source(Protocol):
    def get_value(self, default: T) -> T: ...
class Meter:
    def __init__(self, source: Source):
        self.source = source
        self.n = 0
    def tick(self) -> None:
        self.n = self.source.get_value(1)
`)
add('p16','Python','exception-only use of external call','refused',`
from typing import Protocol
class Source(Protocol):
    def check(self) -> bool: ...
class Meter:
    def __init__(self, source: Source):
        self.source = source
        self.n = 0
    def tick(self) -> None:
        try:
            self.source.check()
        except ValueError:
            self.n = 1
`)
add('r01','Ruby','listener handed self','needs a tag',`
class Meter
  def initialize(listener)
    @listener = listener
    @n = 0
  end
  def tick
    @listener.emit(self)
  end
end
`)
add('r02','Ruby','call truthiness in condition','needs a tag',`
module Flags
  def self.enabled; true; end
end
class Meter
  def initialize; @n = 0; end
  def tick
    @n = 1 if Flags.enabled
  end
end
`)
add('j01','Java','injected callback handed this','needs a tag',`
public class Meter {
  interface Listener { void emit(Meter m); }
  Listener listener;
  int n;
  public Meter(Listener listener) { this.listener = listener; }
  public void tick() { listener.emit(this); }
}
`)
add('j02','Java','generic return type','refuted',`
public class Meter {
  interface Source { <T> T value(T fallback); }
  Source source;
  int n;
  public Meter(Source source) { this.source = source; }
  public void tick() { n = source.value(1); }
}
`)
add('t01','TypeScript','injected callback handed this','needs a tag',`
export class Meter {
  n = 0
  constructor(private listener: (m: Meter) => void) {}
  tick(): void { this.listener(this) }
}
`)
add('t02','TypeScript','injected boolean result truthiness','refuted',`
export class Meter {
  n = 0
  constructor(private enabled: () => boolean) {}
  tick(): void { if (this.enabled()) this.n = 1 }
}
`)
writeFileSync(`${dir}/cases.json`,JSON.stringify(items,null,2))
writeFileSync(`${dir}/RESULTS.md`, '# Adversarial inferred-boundary results\n\nLaw for every case: `r.law(\'n stays zero\', ({n}) => n.eq(0))`, unless extraction refuses before a law can be constructed. Predictions precede runs. Refusals and explicit tagging requirements are acceptable even when the expected category differed.\n\n| Case | Language | Attack | Predicted | Actual | Verdict |\n|---|---|---|---|---|---|\n')
console.log(`Wrote ${items.length} cases and initial results`)
