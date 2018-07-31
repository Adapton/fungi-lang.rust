use ast::*;
use std::rc::Rc;
use normal::NmSetTm;
use normal::NmSetCons;
use normal::NmSet;
use bitype::Ctx;
use decide::RelCtx;
use decide::DecError;
use bitype::NmTmRule;
use std::fmt;
use std::result;
use dynamics::RtVal;

macro_rules! string_constant {
    { $t:ident, $string:expr } => {
        pub struct $t {}
        impl fmt::Display for $t {
            fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
                write!(f,$string)
            }
        }
    }
}
macro_rules! vt100_escape {
    { $t:ident, $escape:expr } => {
        pub struct $t ;
        impl fmt::Display for $t {
            fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
                write!(f,"\x1B[{}m", $escape)
            }
        }
    }
}
vt100_escape!{HiBlue, "1;36"}
vt100_escape!{HiGreen, "1;32"}
vt100_escape!{Normal, "0;0"}  
//vt100_escape!{RuleColor, "37;1"}
vt100_escape!{RuleColor, "0;33"}
//vt100_escape!{HiYellowBlue, "44;33;1"}
string_constant!{CheckMark, "\x1B[1;32m✔\x1B[0;0m"}
//string_constant!{RuleLine, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"}
string_constant!{RuleLine, "───────────────────────────────────────────────────────────────────────────────"}


pub struct Result<X,Y> {
    pub result:
    result::Result<X, Y>
}

pub struct ParenIdxTm(Rc<IdxTm>);
impl fmt::Display for ParenIdxTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match &*self.0 {
            IdxTm::App(_,_) |
            IdxTm::Lam(_,_,_) |
            IdxTm::Map(_,_)   |
            IdxTm::MapStar(_,_)  |
            IdxTm::FlatMap(_,_)  |
            IdxTm::FlatMapStar(_,_) => write!(f, "({})", self.0),
            _ => self.0.fmt(f)
        }
    }
}

pub struct ParenNmTm(Rc<NameTm>);
impl fmt::Display for ParenNmTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match &*self.0 {
            NameTm::Lam(_,_,_) => write!(f, "({})", self.0),
            _ => self.0.fmt(f)
        }
    }
}

impl fmt::Display for Decls {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")
    }
}

impl fmt::Display for PrimApp {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &PrimApp::NameBin(ref v1, ref v2) => write!(f, "{} * {}", v1, v2),
            &PrimApp::RefThunk(ref v) => write!(f, "refthunk {}", v),
            &PrimApp::NatEq(ref v1, ref v2) => write!(f, "{} == {}", v1, v2),
            &PrimApp::NatLt(ref v1, ref v2) => write!(f, "{} < {}", v1, v2),
            &PrimApp::NatLte(ref v1, ref v2) => write!(f, "{} <= {}", v1, v2),
            &PrimApp::NatPlus(ref v1, ref v2) => write!(f, "{} + {}", v1, v2),
        }
    }
}


impl fmt::Display for Exp {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Exp::Doc(ref s, ref e) => write!(f, "///{}\n{}", s, e),
            &Exp::UseAll(ref m, ref e) => write!(f, "use {}::*; {}", m.path, e),
            &Exp::Decls(ref d, ref e) => write!(f, "{{{}}}; {}", d, e),
            &Exp::AnnoE(ref e,ref ce) => write!(f, "{} : {}", e, ce),
            &Exp::AnnoC(ref e,ref ct) => write!(f, "{} : {}", e, ct),
            &Exp::Force(ref v) => write!(f, "force {}", v),
            &Exp::Thunk(ref v, ref e) => write!(f, "thunk {} {}", v, e),
            &Exp::Unroll(ref v,ref x,ref e) => write!(f, "unroll({}, {}.{})",v,x,e),
            &Exp::Unpack(ref v,ref x,ref y,ref e) => write!(f, "unpack({}, {}.{}.{})",v,x,y,e),
            &Exp::Fix(ref x,ref e) => write!(f, "fix {}. {}", x, e),
            &Exp::Ret(ref v) => write!(f, "ret {}", v),
            &Exp::DefType(ref x,ref t,ref e) => write!(f, "type {} = {}; {}", x, t, e),
            &Exp::Let(ref x,ref e1,ref e2) => write!(f, "let {} = {{{}}}; {}", x, e1, e2),
            &Exp::Lam(ref x, ref e) => write!(f, "𝞴{}. {}", x, e),
            &Exp::HostFn(ref hf) => write!(f, "(hostfn {})", hf.path),
            &Exp::App(ref e, ref v) => write!(f, "({}) {}", e, v),
            &Exp::IdxApp(ref e, ref i) => write!(f, "{}[{}]", e, i),
            &Exp::Split(ref v, ref x, ref y, ref e) => write!(f, "split({}, {}.{}.{})", v, x, y, e),
            &Exp::Case(ref v, ref x, ref e1, ref y, ref e2) => write!(f, "case({}, {}.{}, {}.{})", v, x, e1, y, e2),
            &Exp::IfThenElse(ref v, ref e1, ref e2) => write!(f, "if {} {{ {} }} else {{ {} }}", v, e1, e2),
            &Exp::RefAnon(ref v) => write!(f, "ref 0 {}", v),
            &Exp::Ref(ref v1, ref v2) => write!(f, "ref {} {}", v1, v2),
            &Exp::Get(ref v) => write!(f, "get {}", v),
            &Exp::WriteScope(ref v, ref e) => write!(f, "ws {} {{ {} }}", v, e),
            &Exp::NameFnApp(ref v1, ref v2) => write!(f, "{} {}", v1, v2),
            &Exp::PrimApp(ref pa) => write!(f, "{}", pa),
            &Exp::Unimp => write!(f, "umimp"),
            &Exp::DebugLabel(ref n,ref s,ref e) =>
                // This syntax doesn't match the one in parse.rs; FIXME.
                write!(f, "{}{}{}",
                       match n {
                           None    => format!(""),
                           Some(n) => format!("{}: ", n)
                       },
                       match s {
                           None    => format!(""),
                           Some(s) => format!("{}: ", s)
                       },
                       e),
            &Exp::NoParse(ref s) => write!(f, "«Exp::Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Val::Anno(ref v, ref t) => write!(f, "{} : {}", v, t),
            &Val::Bool(ref b) => write!(f, "{}", b),
            &Val::Inj1(ref v) => write!(f, "inj1 {}", v),
            &Val::Inj2(ref v) => write!(f, "inj2 {}", v),
            &Val::Name(ref n) => write!(f, "name {}", n),
            &Val::NameFn(ref n) => write!(f, "nmfn {}", n),
            &Val::Nat(ref n) => write!(f, "{}", n),
            &Val::NoParse(ref s) => write!(f, "«Val::Parse error: `{}`»", s),
            &Val::Pack(ref i, ref v) => write!(f, "pack[{}] {}", i, v),
            &Val::Pair(ref v1, ref v2) => write!(f, "({}, {})", v1, v2),
            &Val::Roll(ref v) => write!(f, "roll {}", v),
            &Val::Str(ref s) => write!(f, "{}", s),
            &Val::ThunkAnon(ref e) => write!(f, "thunk {}", e),
            &Val::Unit => write!(f, "()"),
            &Val::Var(ref x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for RtVal {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &RtVal::Bool(ref b) => write!(f, "{}", b),
            &RtVal::Inj1(ref v) => write!(f, "inj1 {}", v),
            &RtVal::Inj2(ref v) => write!(f, "inj2 {}", v),
            &RtVal::Name(ref n) => write!(f, "name {}", n),
            &RtVal::NameFn(ref n) => write!(f, "nmfn {}", n),
            &RtVal::Nat(ref n) => write!(f, "{}", n),
            &RtVal::Pack(ref v) => write!(f, "pack {}", v),
            &RtVal::Pair(ref v1, ref v2) => write!(f, "({}, {})", v1, v2),
            &RtVal::Ref(ref a) => write!(f, "<ref {:?}>", a),
            &RtVal::Roll(ref v) => write!(f, "roll {}", v),
            &RtVal::Str(ref s) => write!(f, "{}", s),
            &RtVal::Thunk(ref a) => write!(f, "<thunk {:?}>", a),
            &RtVal::ThunkAnon(ref _env, ref e) => write!(f, "thunk ... {}", e),
            &RtVal::Unit => write!(f, "()"),
        }
    }
}

impl fmt::Display for DecError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl<X:fmt::Display, Y:fmt::Display> fmt::Display for Result<X, Y> {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self.result {
            Err(ref x) => write!(f, "Error: {}", x),
            Ok(ref y)  => write!(f, "{}", y),
        }
    }
}

impl fmt::Display for Ctx {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}


impl fmt::Display for RelCtx {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}


impl fmt::Display for NmTmRule {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl fmt::Display for NmSetTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            NmSetTm::Single(ref n) => write!(f, "{{{}}}", n),
            NmSetTm::Subset(ref i) => write!(f, "{}", i),
        }
    }
}

impl fmt::Display for NmSetCons {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            NmSetCons::Union => write!(f, "∪"),
            NmSetCons::Apart => write!(f, "⊥"),
        }
    }
}

impl fmt::Display for NmSet {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        //println!("****** {:?}", self);
        if self.cons == None && self.terms.len() == 0 {            
            write!(f, "Ø")
        } else {
            let mut is_first = true;
            for tm in self.terms.iter() {
                if is_first {
                    write!(f, "{}", tm).unwrap();
                    is_first = false;                
                } else {
                    // XXX indicates a malformed NmSet --- we print 'XXX" instead of panicking
                    write!(f, " {} {}",
                           match &self.cons {
                               &None => "XXX",
                               &Some(NmSetCons::Union) => "∪",
                               &Some(NmSetCons::Apart) => "⊥",
                           }, tm).unwrap();
                }
            }
            write!(f, "")
        }
    }
}


impl fmt::Display for Sort {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Sort::Nm => write!(f, "Nm"),
            &Sort::NmSet => write!(f, "NmSet"),
            &Sort::NmArrow(ref g1, ref g2) => write!(f, "{} → {}", g1, g2),
            &Sort::IdxArrow(ref g1, ref g2) => write!(f, "{} → {}", g1, g2),
            &Sort::Unit => write!(f, "1"),
            &Sort::Prod(ref g1, ref g2) => write!(f, "{} ⨉ {}", g1, g2),
            &Sort::NoParse(ref s) => write!(f, "«Sort::Parse error: `{}`»", s),
            
        }
    }
}

impl fmt::Display for IdxTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            IdxTm::Var(ref x) => write!(f, "{}", x),
            IdxTm::Ident(ref x) => write!(f, "{}", x),
            IdxTm::Sing(ref n) => write!(f, "{{{}}}", n),
            IdxTm::Empty => write!(f, "0"),
            IdxTm::Apart(ref i, ref j) => write!(f, "{} ⊥ {}", i, j),
            IdxTm::Union(ref i, ref j) => write!(f, "{} ∪ {}", i, j),
            IdxTm::Unit => write!(f, "1"),
            IdxTm::Bin(ref i, ref j) => write!(f, "{}∙{}", ParenIdxTm(i.clone()), ParenIdxTm(j.clone())),
            IdxTm::Pair(ref i, ref j) => write!(f, "({},{})", i, j),
            IdxTm::Proj1(ref i) => write!(f, "{}.1", i),
            IdxTm::Proj2(ref i) => write!(f, "{}.2", i),
            IdxTm::WriteScope => write!(f, "@!"),
            IdxTm::NmSet(ref ns) => write!(f, "{}", ns),
            IdxTm::Lam(ref x, ref g, ref i) => write!(f, "𝞴{}:{}.{}", x, g, i),
            IdxTm::App(ref i, ref j) => write!(f, "{}({})", ParenIdxTm(i.clone()), j),
            IdxTm::Map(ref n, ref j) => write!(f, "{}⦗{}⦘", ParenNmTm(n.clone()), j),
            IdxTm::MapStar(ref n, ref j) => write!(f, "{}^*⦗{}⦘", ParenNmTm(n.clone()), j),
            IdxTm::FlatMap(ref i, ref j) => write!(f, "{}⦗{}⦘", ParenIdxTm(i.clone()), j),
            IdxTm::FlatMapStar(ref i, ref j) => write!(f, "{}^*⦗{}⦘", ParenIdxTm(i.clone()), j),
            IdxTm::NmTm(ref n) => write!(f, "{}", n),
            IdxTm::NoParse(ref s) => write!(f, "«IdxTm::Parse error: `{}`»", s),
            IdxTm::Unknown => write!(f, "?"),
        }
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            //Name::Leaf => write!(f, "[]"),
            Name::Leaf => write!(f, "▲"),
            Name::Bin(ref n, ref m) => write!(f, "{}⋅{}", n, m),
            Name::Sym(ref s) => write!(f, "@@{}", s),
            Name::Num(ref n) => write!(f, "@{}", n),
            Name::NoParse(ref s) => write!(f, "«Name::Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for NameTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            NameTm::Var(ref x) => write!(f, "{}", x),
            NameTm::Ident(ref x) => write!(f, "{}", x),
            NameTm::ValVar(ref x) => write!(f, "{}", x),
            NameTm::Name(ref n) => write!(f, "{}", n),
            NameTm::Bin(ref n, ref m) => write!(f, "{}∙{}", n, m),
            NameTm::Lam(ref x, ref g, ref m) => write!(f, "𝞴{}:{}.{}", x, g, m),
            NameTm::App(ref n, ref m) => write!(f, "{}({})", n, m),
            NameTm::WriteScope => write!(f, "@@"),
            NameTm::NoParse(ref s) => write!(f, "«NameTm::Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Effect::WR(ref w, ref r) => write!(f, "〈{};{}〉", w, r),
            &Effect::NoParse(ref s) => write!(f, "«Effect::Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for Prop {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Prop::Tt => write!(f, "⊤"),
            &Prop::Equiv(ref i, ref j, ref g) => write!(f, "{} ≡ {} : {}", i, j, g),
            &Prop::Apart(ref i, ref j, ref g) => write!(f, "{} ⊥ {} : {}", i, j, g),
            &Prop::Conj(ref i, ref j) => write!(f, "{} ∧ {}", i, j),
            &Prop::NoParse(ref s) => write!(f, "«Prop::Parse error: `{}`»", s),
        }
    }
}


impl fmt::Display for Kind {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Kind::Type => write!(f, "﹡"),
            &Kind::TypeParam(ref k) => write!(f, "﹡ ⇒ {}", k),
            &Kind::IdxParam(ref g, ref k) => write!(f, "{} → {}", g, k),
            &Kind::NoParse(ref s) => write!(f, "«Kind::Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Type::Unit => { write!(f, "Unit") }
            &Type::Var(ref x) => { write!(f, "{}", x) }
            &Type::Ident(ref x) => { write!(f, "{}", x) }
            &Type::Sum(ref t1, ref t2) => { write!(f, "({} ＋ {})", t1, t2) }
            &Type::Prod(ref t1, ref t2) => { write!(f, "{} ⨉ {}", t1, t2) }
            &Type::Ref(ref i, ref a) => { write!(f, "Ref[{}]({})", i, a) }
            &Type::Thk(ref i, ref ce) => { write!(f, "Thk[{}]({})", i, ce) }
            &Type::IdxApp(ref t, ref i) => { write!(f, "{}[{}]", t, i) }
            &Type::TypeApp(ref t1, ref t2) => { write!(f, "{}({})", t1, t2) }
            &Type::Nm(ref i) => { write!(f, "Nm[{}]", i) }
            &Type::NmFn(ref n) => { write!(f, "NmFn[{}]", n) }
            &Type::TypeFn(ref x, ref k, ref t) => { write!(f, "∀{}:{}.{}", x, k, t) }
            &Type::IdxFn(ref x, ref g, ref t) => { write!(f, "∀{}:{}.{}", x, g, t) }
            &Type::Rec(ref x, ref t) => { write!(f, "(rec {}. {})", x, t) }
            &Type::Exists(ref x, ref g, ref prop, ref t) if prop == &Prop::Tt => { write!(f, "∃{}:{}. {}", x, g, t) }
            &Type::Exists(ref x, ref g, ref prop, ref t) => { write!(f, "∃{}:{} | {}. {}", x, g, prop, t) }
            &Type::NoParse(ref s) => { write!(f, "«Type::Parse error: `{}`»", s) }
        }
    }
}

impl fmt::Display for CType {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &CType::Lift(ref t) => { write!(f, "F {}", t) }
            &CType::Arrow(ref t, ref ce) => { write!(f, "{} → {}", t, ce) }
            &CType::NoParse(ref s) => { write!(f, "«CType::Parse error: `{}`»", s) }
        }
    }
}

impl fmt::Display for CEffect {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &CEffect::Cons(ref ct, ref eff)  => { write!(f, "{}{}", eff, ct) }
            &CEffect::ForallType(ref x, ref k, ref ce) => { write!(f, "∀{}:{}.{}", x, k, ce) }
            &CEffect::ForallIdx(ref x, ref g, ref prop, ref ce) => { write!(f, "∀{}:{}|{}.{}", x, g, prop, ce) }
            &CEffect::NoParse(ref s) => { write!(f, "«CEffect::Parse error: `{}`»", s) }
        }
    }
}
