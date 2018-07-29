use ast::*;
use normal::NmSetTm;
use normal::NmSet;
use bitype::Ctx;
use decide::DecError;
use bitype::NmTmRule;
use bitype::TypeError;
use std::fmt;
use std::result;

pub struct Result {
    pub result:
    result::Result<CEffect, TypeError>
}

impl fmt::Display for DecError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl fmt::Display for Result {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self.result {
            Err(ref e) => write!(f, "Error: {}", e),
            Ok(ref ce) => write!(f, "{}", ce),
        }
    }
}

impl fmt::Display for Ctx {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl fmt::Display for NmSetTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl fmt::Display for NmTmRule {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}


impl fmt::Display for NmSet {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
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
            &Sort::NoParse(ref s) => write!(f, "«Parse error: `{}`»", s),
            
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
            IdxTm::Bin(ref i, ref j) => write!(f, "{} * {}", i, j),
            IdxTm::Pair(ref i, ref j) => write!(f, "({},{})", i, j),
            IdxTm::Proj1(ref i) => write!(f, "{}.1", i),
            IdxTm::Proj2(ref i) => write!(f, "{}.2", i),
            IdxTm::WriteScope => write!(f, "@!"),
            IdxTm::NmSet(ref ns) => write!(f, "{}", ns),            
            IdxTm::Lam(ref x, ref g, ref i) => write!(f, "#{}:{}.{}", x, g, i),
            IdxTm::App(ref i, ref j) => write!(f, "{}({})", i, j),
            IdxTm::Map(ref n, ref j) => write!(f, "{}[{}]", n, j),
            IdxTm::MapStar(ref n, ref j) => write!(f, "{}^*[{}]", n, j),
            IdxTm::FlatMap(ref i, ref j) => write!(f, "{}[{}]", i, j),
            IdxTm::FlatMapStar(ref i, ref j) => write!(f, "{}^*[{}]", i, j),
            IdxTm::NmTm(ref n) => write!(f, "{}", n),
            IdxTm::NoParse(ref s) => write!(f, "«Parse error: `{}`»", s),
            IdxTm::Unknown => write!(f, "?"),
        }
    }
}

impl fmt::Display for NameTm {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")        
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Effect::WR(ref w, ref r) => write!(f, "〈{};{}〉", w, r),
            &Effect::NoParse(ref s) => write!(f, "«Parse error: `{}`»", s),
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
            &Prop::NoParse(ref s) => write!(f, "«Parse error: `{}`»", s),
        }
    }
}


impl fmt::Display for Kind {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Kind::Type => write!(f, "﹡"),
            &Kind::TypeParam(ref k) => write!(f, "﹡ ⇒ {}", k),
            &Kind::IdxParam(ref g, ref k) => write!(f, "{} → {}", g, k),
            &Kind::NoParse(ref s) => write!(f, "«Parse error: `{}`»", s),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &Type::Unit => { write!(f, "Unit") }
            &Type::Var(ref x) => { write!(f, "{}", x) }
            &Type::Ident(ref x) => { write!(f, "{}", x) }
            &Type::Sum(ref t1, ref t2) => { write!(f, "{} ＋ {}", t1, t2) }
            &Type::Prod(ref t1, ref t2) => { write!(f, "{} ⨉ {}", t1, t2) }
            &Type::Ref(ref i, ref a) => { write!(f, "Ref[{}]({})", i, a) }
            &Type::Thk(ref i, ref ce) => { write!(f, "Thk[{}]({})", i, ce) }
            &Type::IdxApp(ref t, ref i) => { write!(f, "{}[{}]", t, i) }
            &Type::TypeApp(ref t1, ref t2) => { write!(f, "{}({})", t1, t2) }
            &Type::Nm(ref i) => { write!(f, "Nm[{}]", i) }
            &Type::NmFn(ref n) => { write!(f, "NmFn[{}]", n) }
            &Type::TypeFn(ref x, ref k, ref t) => { write!(f, "∀{}:{}.{}", x, k, t) }
            &Type::IdxFn(ref x, ref g, ref t) => { write!(f, "∀{}:{}.{}", x, g, t) }
            &Type::Rec(ref x, ref t) => { write!(f, "rec {}. {}", x, t) }
            &Type::Exists(ref x, ref g, ref prop, ref t) if prop == &Prop::Tt => { write!(f, "∃{}:{}. {}", x, g, t) }
            &Type::Exists(ref x, ref g, ref prop, ref t) => { write!(f, "∃{}:{} | {}. {}", x, g, prop, t) }
            &Type::NoParse(ref s) => { write!(f, "«Parse error: `{}`»", s) }
        }
    }
}

impl fmt::Display for CType {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &CType::Lift(ref t) => { write!(f, "F {}", t) }
            &CType::Arrow(ref t, ref ce) => { write!(f, "{} → {}", t, ce) }
            &CType::NoParse(ref s) => { write!(f, "«Parse error: `{}`»", s) }
        }
    }
}

impl fmt::Display for CEffect {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        match self {
            &CEffect::Cons(ref ct, ref eff)  => { write!(f, "{}{}", eff, ct) }
            &CEffect::ForallType(ref x, ref k, ref ce) => { write!(f, "∀{}:{}.{}", x, k, ce) }
            &CEffect::ForallIdx(ref x, ref g, ref prop, ref ce) => { write!(f, "∀{}:{}|{}.{}", x, g, prop, ce) }
            &CEffect::NoParse(ref s) => { write!(f, "«Parse error: `{}`»", s) }
        }
    }
}
