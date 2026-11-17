// Go probe: uint64 WRAP arithmetic uses real Go unsigned operations.
// Width reduction, signed policy, SATURATE/TRAP, division-mode adjustments,
// and MIN/-1 pair trapping are explicitly labeled adapters, not native coverage.
package main
import("bufio";"fmt";"math/big";"os";"strings")
func z(x int64)*big.Int{return big.NewInt(x)}
func parse(s string)*big.Int{v,ok:=new(big.Int).SetString(s,10);if !ok{panic("invalid decimal")};return v}
func bound(n *big.Int,w uint,signed bool,p string)(*big.Int,string){
 mod:=new(big.Int).Lsh(z(1),w); lo:=z(0);hi:=new(big.Int).Sub(mod,z(1))
 if signed{lo.Neg(new(big.Int).Rsh(mod,1));hi.Sub(new(big.Int).Rsh(mod,1),z(1))}
 if n.Cmp(lo)>=0&&n.Cmp(hi)<=0{return n,""}
 switch p{case "TRAP":return nil,"overflow";case "SATURATE":if n.Cmp(lo)<0{return lo,""};return hi,""
 case "WRAP":v:=new(big.Int).Mod(n,mod);if signed&&v.Cmp(new(big.Int).Rsh(mod,1))>=0{v.Sub(v,mod)};return v,""}
 panic("invalid policy")
}
func eval(w uint,signed bool,op,p,mode string,a,b *big.Int)(*big.Int,string){
 if op=="div"||op=="rem"{
  if b.Sign()==0{return nil,"division_by_zero"}
  lo:=new(big.Int).Neg(new(big.Int).Lsh(z(1),w-1))
  if signed&&a.Cmp(lo)==0&&b.Cmp(z(-1))==0&&p=="TRAP"{return nil,"overflow"}
  q,r:=new(big.Int),new(big.Int);q.QuoRem(a,b,r) // Go big.Int QuoRem truncates toward zero.
  if mode=="FLOOR"&&r.Sign()!=0&&(r.Sign()<0)!=(b.Sign()<0){q.Sub(q,z(1));r.Add(r,b)}
  if mode=="EUCLIDEAN"&&r.Sign()<0{if b.Sign()>0{q.Sub(q,z(1));r.Add(r,b)}else{q.Add(q,z(1));r.Sub(r,b)}}
  if mode!="FLOOR"&&mode!="EUCLIDEAN"&&mode!="TRUNCATING"{panic("invalid mode")}
  if op=="div"{return bound(q,w,signed,p)};return bound(r,w,signed,p)
 }
 if op=="cast"{return bound(a,w,signed,p)}
 if !signed&&p=="WRAP"{
  x,y:=a.Uint64(),b.Uint64(); var v uint64
  switch op{case "add":v=x+y;case "sub":v=x-y;case "mul":v=x*y;case "neg":v=0-x;default:panic("invalid op")}
  if w<64{v&=(uint64(1)<<w)-1};return new(big.Int).SetUint64(v),""
 }
 n:=new(big.Int)
 switch op{case "add":n.Add(a,b);case "sub":n.Sub(a,b);case "mul":n.Mul(a,b);case "neg":n.Neg(a);default:panic("invalid op")}
 return bound(n,w,signed,p)
}
func main(){s:=bufio.NewScanner(os.Stdin);s.Buffer(make([]byte,4096),1024*1024);out:=bufio.NewWriter(os.Stdout);defer out.Flush()
 for s.Scan(){t:=strings.Fields(s.Text());if len(t)!=7{panic("protocol")};var w,si uint;if _,e:=fmt.Sscan(t[0],&w);e!=nil{panic(e)};if _,e:=fmt.Sscan(t[1],&si);e!=nil{panic(e)}
  if w!=8&&w!=16&&w!=32&&w!=64{panic("width")}
  v,err:=eval(w,si==1,t[2],t[3],t[4],parse(t[5]),parse(t[6]));if err!=""{fmt.Fprintln(out,"ERR",err)}else{fmt.Fprintln(out,"OK",v.String())}
 };if e:=s.Err();e!=nil{panic(e)}
}
