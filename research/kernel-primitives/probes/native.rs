// Rust probe: typed checked_*, wrapping_*, saturating_* for add/sub/mul/neg.
// Cast, division-mode adjustment, and division-pair overflow policy are explicit adapters.
use std::io::{self, BufRead};
macro_rules! arithmetic {
    ($t:ty,$a:expr,$b:expr,$op:expr,$policy:expr) => {{
        let x=$a as $t; let y=$b as $t;
        match ($op,$policy) {
            ("add","WRAP") => Some(x.wrapping_add(y) as i128),
            ("sub","WRAP") => Some(x.wrapping_sub(y) as i128),
            ("mul","WRAP") => Some(x.wrapping_mul(y) as i128),
            ("neg","WRAP") => Some(x.wrapping_neg() as i128),
            ("add","SATURATE") => Some(x.saturating_add(y) as i128),
            ("sub","SATURATE") => Some(x.saturating_sub(y) as i128),
            ("mul","SATURATE") => Some(x.saturating_mul(y) as i128),
            ("neg","SATURATE") => Some((0 as $t).saturating_sub(x) as i128),
            ("add","TRAP") => x.checked_add(y).map(|v|v as i128),
            ("sub","TRAP") => x.checked_sub(y).map(|v|v as i128),
            ("mul","TRAP") => x.checked_mul(y).map(|v|v as i128),
            ("neg","TRAP") => x.checked_neg().map(|v|v as i128),
            _ => panic!("unknown operation/policy"),
        }
    }};
}
fn eval(w:u32,s:bool,op:&str,p:&str,mode:&str,a:i128,b:i128)->Result<i128,&'static str> {
    let lo=if s {-(1_i128<<(w-1))} else {0};
    let hi=if s {(1_i128<<(w-1))-1} else {(1_i128<<w)-1};
    if op=="div" || op=="rem" {
        if b==0 { return Err("division_by_zero"); }
        if s && a==lo && b==-1 && p=="TRAP" { return Err("overflow"); }
        let (q,r)=match mode {
            "TRUNCATING" => (a/b,a%b),
            "FLOOR" => { let mut q=a/b; let mut r=a%b; if r!=0 && (r<0)!=(b<0) {q-=1;r+=b;} (q,r) },
            "EUCLIDEAN" => (a.div_euclid(b),a.rem_euclid(b)),
            _=>panic!("unknown division mode"),
        };
        return bound(if op=="div" {q} else {r},w,s,p);
    }
    if op=="cast" {return bound(a,w,s,p);}
    let v=match (w,s) {
        (8,true)=>arithmetic!(i8,a,b,op,p), (16,true)=>arithmetic!(i16,a,b,op,p),
        (32,true)=>arithmetic!(i32,a,b,op,p), (64,true)=>arithmetic!(i64,a,b,op,p),
        (8,false)=>arithmetic!(u8,a,b,op,p), (16,false)=>arithmetic!(u16,a,b,op,p),
        (32,false)=>arithmetic!(u32,a,b,op,p), (64,false)=>arithmetic!(u64,a,b,op,p),
        _=>panic!("unsupported width"),
    };
    v.ok_or("overflow")
}
fn bound(n:i128,w:u32,s:bool,p:&str)->Result<i128,&'static str> {
    let lo=if s {-(1_i128<<(w-1))} else {0};
    let hi=if s {(1_i128<<(w-1))-1} else {(1_i128<<w)-1};
    if n>=lo && n<=hi {return Ok(n);}
    match p {
        "TRAP"=>Err("overflow"),
        "SATURATE"=>Ok(n.clamp(lo,hi)),
        "WRAP"=>{let bits=n & ((1_i128<<w)-1); Ok(if s && bits >=(1_i128<<(w-1)) {bits-(1_i128<<w)} else {bits})},
        _=>panic!("unknown policy"),
    }
}
fn main() {
    for line in io::stdin().lock().lines() {
        let line=line.expect("stdin"); let t:Vec<_>=line.split_whitespace().collect();
        assert_eq!(t.len(),7,"protocol");
        let (w,s,a,b)=(t[0].parse::<u32>().unwrap(),t[1]=="1",t[5].parse::<i128>().unwrap(),t[6].parse::<i128>().unwrap());
        match eval(w,s,t[2],t[3],t[4],a,b) {
            Ok(v)=>println!("OK {v}"),Err(e)=>println!("ERR {e}"),
        }
    }
}
