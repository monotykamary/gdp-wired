// gdp-wired's check harness: the requests read from the in-pipe, each that may crash first run in a forked child
// (a trap is the step's failure), the answers written to the out-pipe.
#if canImport(Glibc)
import Glibc
#elseif canImport(Darwin)
import Darwin
#endif
import __GDP_MODULE__

func run() {
  let args = CommandLine.arguments
  guard args.count >= 3, let fin = fopen(args[args.count - 2], "r") else { return }
  let fout = open(args[args.count - 1], O_WRONLY)
  typealias Fork = @convention(c) () -> Int32
  let fork = unsafeBitCast(dlsym(dlopen(nil, RTLD_NOW), "fork"), to: Fork.self)
  var line: UnsafeMutablePointer<CChar>? = nil
  var cap = 0
  while getline(&line, &cap, fin) > 0 {
    let req = String(cString: line!)
    let op = __gdpOp(req)
    var res: String
    if op == "new" || op == "at" || op == "call" {
      let pid = fork()
      if pid == 0 { if getenv("GDP_SWIFT_DEBUG") == nil { dup2(open("/dev/null", O_WRONLY), 2) }; _ = __gdpHandle(req); _exit(0) }
      var st: Int32 = 0
      _ = waitpid(pid, &st, 0)
      let sig = st & 0x7f, code = (st >> 8) & 0xff
      if sig != 0 || code != 0 { res = __gdpCrash(op, sig != 0 ? "signal \(sig)" : "exit \(code)") } else { res = __gdpHandle(req) }
    } else { res = __gdpHandle(req) }
    res += "\n"
    _ = res.withCString { write(fout, $0, strlen($0)) }
  }
}
run()
