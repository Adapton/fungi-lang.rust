use ast::*;
use std::fmt;
use std::rc::Rc;

// Move this to the enum definition?
impl TCtxt {
    pub fn lookup_var(&self, x:&Var) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Var(ref c,ref v,ref t) => {
                if x == v { Some(t.clone()) } else { c.lookup_var(x) }
            },
            TCtxt::Cell(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_var(x) },
        }
    }
    pub fn lookup_cell(&self, ptr:&Pointer) -> Option<Type> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Cell(ref c,ref p,ref t) => {
                if p == ptr { Some(t.clone()) } else { c.lookup_cell(ptr) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Thunk(ref c,_,_) => { c.lookup_cell(ptr) },
        }
    }
    pub fn lookup_thunk(&self, ptr:&Pointer) -> Option<CType> {
        match *self {
            TCtxt::Empty => None,
            TCtxt::Thunk(ref c,ref p,ref t) => {
                if p == ptr { Some(t.clone()) } else { c.lookup_thunk(ptr) }
            },
            TCtxt::Var(ref c,_,_)
            | TCtxt::Cell(ref c,_,_) => { c.lookup_thunk(ptr) },
        }
    }
}

enum TypeError {
    AnnoMism,
    NoSynthRule,
    NoCheckRule,
    InvalidPtr,
    ParamMism,
    ParamNoSynth,
    AppNotArrow,
    BadCheck,
    DSLiteral,
    EmptyDT,
}
impl fmt::Display for TypeError {
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            TypeError::AnnoMism => "annotation mismatch",
            TypeError::NoSynthRule => "no synth rule found",
            TypeError::NoCheckRule => "no check rule found",
            TypeError::InvalidPtr => "invalid pointer",
            TypeError::ParamMism => "parameter type incorrect",
            TypeError::ParamNoSynth => "unknown parameter type",
            TypeError::AppNotArrow => "application of non-arrow type",
            TypeError::BadCheck => "checked type inappropriate for value",
            TypeError::DSLiteral => "data structure litterals not allowed",
            TypeError::EmptyDT => "ambiguous empty data type",
        };
        write!(f,"{}",s)
    }
}

impl Val {
    fn short(&self) -> &str {
        match *self {
            Val::Var(_) => "var",
            Val::Unit => "unit",
            Val::Pair(_,_) => "pair",
            Val::Injl(_) => "injl",
            Val::Injr(_) => "injr",
            Val::Ref(_) => "ref",
            Val::Thunk(_) => "thunk",
            Val::Anno(_,_) => "annotation",
            Val::Nat(_) => "nat",
            Val::Str(_) => "string",
            Val::Seq(_) => "sequence",
            Val::Stack(_) => "stack",
        }
    }
}

impl Exp {
    fn short(&self) -> &str {
        match *self {
            Exp::Anno(_,_) => "annotation",
            Exp::Force(_) => "force",
            Exp::Thunk(_) => "thunk",
            Exp::Fix(_,_) => "fix",
            Exp::Ret(_) => "ret",
            Exp::Let(_,_,_,_) => "let",
            Exp::Lam(_, _) => "lam",
            Exp::App(_, _) => "app",
            Exp::Split(_, _, _, _) => "split",
            Exp::Case(_, _, _, _, _) => "case",
            Exp::Ref(_) => "ref",
            Exp::Get(_) => "get",
            Exp::TrHint(_,_) => "translation hint",
            Exp::Label(_,_) => "label",
            Exp::PrimApp(ref p) => p.short(),
        }
    }
}

impl PrimApp {
    fn short(&self) -> &str {
        match *self {
            PrimApp::NatAdd(_, _) => "NatAdd",
            PrimApp::NatLte(_, _) => "NatLte",
            PrimApp::BoolAnd(_, _) => "BoolAnd",
            PrimApp::NatOfChar(_) => "NatOfChar",
            PrimApp::CharOfNat(_) => "CharOfNat",
            PrimApp::StrOfNat(_) => "StrOfNat",
            PrimApp::NatOfStr(_) => "NatOfStr",
            PrimApp::SeqEmpty => "SeqEmpty",
            PrimApp::SeqGetFirst(_) => "SeqGetFirst",
            PrimApp::SeqIsEmpty(_) => "SeqIsEmpty",
            PrimApp::SeqSingleton(_) => "SeqSingleton",
            PrimApp::SeqDup(_) => "SeqDup",
            PrimApp::SeqAppend(_, _) => "SeqAppend",
            PrimApp::SeqFoldSeq(_, _, _) => "SeqFoldSeq",
            PrimApp::SeqFoldUp(_, _, _, _) => "SeqFoldUp",
            PrimApp::SeqIntoStack(_) => "SeqIntoStack",
            PrimApp::SeqIntoQueue(_) => "SeqIntoQueue",
            PrimApp::SeqIntoHashmap(_) => "SeqIntoHashmap",
            PrimApp::SeqIntoKvlog(_) => "SeqIntoKvlog",
            PrimApp::SeqMap(_, _) => "SeqMap",
            PrimApp::SeqFilter(_, _) => "SeqFilter",
            PrimApp::SeqSplit(_, _) => "SeqSplit",
            PrimApp::SeqReverse(_) => "SeqReverse",
            PrimApp::StackEmpty => "StackEmpty",
            PrimApp::StackIsEmpty(_) => "StackIsEmpty",
            PrimApp::StackDup(_) => "StackDup",
            PrimApp::StackPush(_, _) => "StackPush",
            PrimApp::StackPop(_) => "StackPop",
            PrimApp::StackPeek(_) => "StackPeek",
            PrimApp::StackIntoSeq(_) => "StackIntoSeq",
            PrimApp::QueueEmpty => "QueueEmpty",
            PrimApp::QueueIsEmpty(_) => "QueueIsEmpty",
            PrimApp::QueueDup(_) => "QueueDup",
            PrimApp::QueuePush(_, _) => "QueuePush",
            PrimApp::QueuePop(_) => "QueuePop",
            PrimApp::QueuePeek(_) => "QueuePeek",
            PrimApp::QueueIntoSeq(_) => "QueueIntoSeq",
            PrimApp::KvlogDup(_) => "KvlogDup",
            PrimApp::KvlogEmpty => "KvlogEmpty",
            PrimApp::KvlogIsEmpty(_) => "KvlogIsEmpty",
            PrimApp::KvlogGet(_, _) => "KvlogGet",
            PrimApp::KvlogPut(_, _, _) => "KvlogPut",
            PrimApp::KvlogIntoSeq(_) => "KvlogIntoSeq",
            PrimApp::KvlogIntoHashmap(_) => "KvlogIntoHashmap",
        }
    }
}

fn fail_synth_val(scope:Option<&Name>, err:TypeError, v:&Val) -> Option<Type> {
    if let Some(nm) = scope {print!("Within {}, ", nm)}
    println!("Failed to synthesize {} value, error: {}", v.short(), err);
    None
}

fn fail_check_val(scope:Option<&Name>, err:TypeError, v:&Val) -> bool {
    if let Some(nm) = scope {print!("Within {}, ", nm)}
    println!("Failed to check {} value, error: {}", v.short(), err);
    false
}

fn fail_synth_exp(scope:Option<&Name>, err:TypeError, e:&Exp) -> Option<CType> {
    if let Some(nm) = scope {print!("Within {}, ", nm)}
    println!("Failed to synthesize {} expression, error: {}", e.short(), err);
    None
}

fn fail_check_exp(scope:Option<&Name>, err:TypeError, e:&Exp) -> bool {
    if let Some(nm) = scope {print!("Within {}, ", nm)}
    println!("Failed to check {} expression, error: {}", e.short(), err);
    false
}

pub fn synth_val(scope:Option<&Name>, ctxt:&TCtxt, val:&Val) -> Option<Type> {
    match val {
        /* Note for implementers:
            one or both of `synth_val` or `check_val` should be implemented
            for your new Val variant
            (check_val defaults to synth_val)
        */
        &Val::Var(ref v) => { ctxt.lookup_var(v) },
        &Val::Unit => { Some(Type::Unit) },
        &Val::Pair(ref x, ref y) => {
            if let Some(a) = synth_val(scope, ctxt, x) {
                if let Some(b) = synth_val(scope, ctxt, y) {
                    Some(make_type![(outerctx a x outerctx b)])
                } else { fail_synth_val(scope, TypeError::ParamNoSynth, val) }
            } else { fail_synth_val(scope, TypeError::ParamNoSynth, val) }
        },
        &Val::Injl(_) => { fail_synth_val(scope, TypeError::NoSynthRule, val) },
        &Val::Injr(_) => { fail_synth_val(scope, TypeError::NoSynthRule, val) },
        &Val::Ref(ref p) => {
            if let Some(t) = ctxt.lookup_cell(p) {
                Some(make_type![ref outerctx t])
            } else { fail_synth_val(scope, TypeError::InvalidPtr, val) }
        },
        &Val::Thunk(ref p) => {
            if let Some(t) = ctxt.lookup_thunk(p) {
                Some(make_type![U outerctx t])
            } else { fail_synth_val(scope, TypeError::InvalidPtr, val) }
        },
        &Val::Anno(ref v,ref t) => {
            if check_val(scope, ctxt, v, t) {
                Some(t.clone())
            } else { fail_synth_val(scope, TypeError::AnnoMism, val) }
        },
        &Val::Nat(_) => { Some(make_type![nat]) },
        &Val::Str(_) => { Some(make_type![string]) },
        &Val::Seq(_) => { fail_synth_val(scope, TypeError::DSLiteral, val) },
        &Val::Stack(_) => { fail_synth_val(scope, TypeError::DSLiteral, val) },
    }
}


pub fn check_val(scope:Option<&Name>, ctxt:&TCtxt, val:&Val, typ:&Type) -> bool {
    match (val, typ) {
        (&Val::Unit, &Type::Unit) => true,
        (&Val::Pair(ref v1, ref v2), &Type::Pair(ref t1, ref t2)) => {
            check_val(scope, ctxt, v1, t1 )
            & check_val(scope, ctxt, v2, t2 )
        },
        (&Val::Injl(ref v), &Type::Sum(ref t1, _)) => {
            check_val(scope, ctxt, v, t1 )
        },
        (&Val::Injr(ref v), &Type::Sum(_, ref t2)) => {
            check_val(scope, ctxt, v, t2 )
        },
        (&Val::Ref(ref p), &Type::Ref(ref t1)) => {
            if let Some(t2) = ctxt.lookup_cell(p) {
                **t1 == t2
            } else { fail_check_val(scope, TypeError::InvalidPtr,val) }
        },
        (&Val::Thunk(ref p), &Type::U(ref ct)) => {
            if let Some(t) = ctxt.lookup_thunk(p) {
                **ct == t
            } else { fail_check_val(scope, TypeError::InvalidPtr,val) }
        },
        (&Val::Nat(_), &make_type![nat]) => true,
        (&Val::Str(_), &make_type![string]) => true,
        (v, t2) => {
            if let Some(ref t1) = synth_val(scope, ctxt, v) {
                t2 == t1
            } else { fail_check_val(scope, TypeError::NoCheckRule,val) }
        },

    }
}

pub fn synth_exp(scope:Option<&Name>, ctxt:&TCtxt, exp:&Exp) -> Option<CType> {
    // TODO: synth rules for all capable expressions
    match exp {
        /* Note for implementers:
            one or both of `synth_exp` or `check_exp` should be implemented
            for your new Exp variant
            (check_exp defaults to synth_exp)
        */
        &Exp::Anno(ref e, ref ct) => {
            if check_exp(scope, ctxt, e, ct) {
                Some(ct.clone())
            } else { fail_synth_exp(scope, TypeError::AnnoMism, exp) }
        },
        &Exp::Force(ref v) => {
            if let Some(Type::U(ct)) = synth_val(scope, ctxt, v) {
                Some((*ct).clone())
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::Thunk(_) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Fix(_,_) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Ret(_) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Let(_,_,_,_) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Lam(_, _) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::App(ref e, ref v) => {
            if let Some(CType::Arrow(t,ct)) = synth_exp(scope, ctxt, e) {
                if check_val(scope, ctxt, v, &t) {
                    Some((*ct).clone())
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::AppNotArrow, exp) }
        },
        &Exp::Split(_, _, _, _) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Case(_, _, _, _, _) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Ref(_) => { fail_synth_exp(scope, TypeError::NoSynthRule, exp) },
        &Exp::Get(ref v) => {
            if let Some(Type::Ref(t)) = synth_val(scope, ctxt, v) {
                Some(CType::F(t))
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::Label(ref nm, ref e) => {
            synth_exp(Some(nm), ctxt, e)
        },
        &Exp::TrHint(ref h, ref e) => {
            synth_exp(scope, ctxt, e)
        }
        &Exp::PrimApp(PrimApp::NatAdd(ref n1, ref n2)) => {
            if check_val(scope, ctxt, n1, &Type::PrimApp(PrimTyApp::Nat))
            & check_val(scope, ctxt, n2, &Type::PrimApp(PrimTyApp::Nat)) {
                Some(CType::F(Rc::new(Type::PrimApp(PrimTyApp::Nat))))
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::NatLte(ref n1, ref n2)) => {
            if check_val(scope, ctxt, n1, &make_type![nat])
            & check_val(scope, ctxt, n2, &make_type![nat]) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::BoolAnd(ref b1, ref b2)) => {
            if check_val(scope, ctxt, b1, &make_type![bool])
            & check_val(scope, ctxt, b2, &make_type![bool]) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::NatOfChar(ref c)) => {
            if check_val(scope, ctxt, c, &make_type![char]) {
                Some(make_ctype![F nat])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::CharOfNat(ref n)) => {
            if check_val(scope, ctxt, n, &make_type![nat]) {
                Some(make_ctype![F char])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StrOfNat(ref n)) => {
            if check_val(scope, ctxt, n, &make_ctype![nat]) {
                Some(make_ctype![F string])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::NatOfStr(ref s)) => {
            if check_val(scope, ctxt, s, &make_ctype![string]) {
                Some(make_ctype![F nat])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqEmpty) => {
            fail_synth_exp(scope, TypeError::EmptyDT, exp)
        },
        &Exp::PrimApp(PrimApp::SeqGetFirst(ref s)) => {
            unimplemented!("SeqGetFirst")
        },
        &Exp::PrimApp(PrimApp::SeqIsEmpty(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(_))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqSingleton(ref s)) => {
            unimplemented!("SeqSingleton")
        },
        &Exp::PrimApp(PrimApp::SeqDup(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Seq(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqAppend(ref s, ref v)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                let a = (*a).clone();
                if check_val(scope, ctxt, v, &a) {
                    Some(make_ctype![F Seq(outerctx a)])
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqFoldSeq(ref v_seq, ref v_accum, ref e_body)) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum ==> B
            Ctx |- e_body <== (A -> B -> F(B))
            ----------------------------------------------------- :: synth-seq-fold-seq
            Ctx |- seq_fold_seq(v_seq, v_accum, e_body) ==> F(B)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                if let Some(b) = synth_val(scope, ctxt, v_accum) {
                    let bt = CType::Arrow(a,Rc::new(CType::Arrow(
                        Rc::new(b.clone()),
                        Rc::new(CType::F(Rc::new(b.clone())))
                    )));
                    if check_exp(scope, ctxt, e_body, &bt) {
                        Some(CType::F(Rc::new(b)))
                    } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_synth_exp(scope, TypeError::ParamNoSynth, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqFoldUp(ref v_seq, ref v_init, ref e_first, ref e_combine)) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_init ==> B
            Ctx |- e_first <== (A -> F(B))
            Ctx |- e_combine <== (B -> B -> F(B))
            --------------------------------- :: synth-seq-fold-up
            Ctx |- seq_fold_up(v_seq, v_init, e_first, e_combine) ==> F(B)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                if let Some(b) = synth_val(scope, ctxt, v_init) {
                    let fa = CType::Arrow(a,Rc::new(
                        CType::F(Rc::new(b.clone()))
                    ));
                    if check_exp(scope, ctxt, e_first, &fa) {
                        let ca = CType::Arrow(Rc::new(b.clone()),Rc::new(CType::Arrow(
                            Rc::new(b.clone()),
                            Rc::new(CType::F(Rc::new(b.clone())))
                        )));
                        if check_exp(scope, ctxt, e_combine, &ca) {
                            Some(CType::F(Rc::new(b)))
                        } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                    } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_synth_exp(scope, TypeError::ParamNoSynth, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqIntoStack(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Stack(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqIntoQueue(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Queue(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqIntoHashmap(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Hashmap(nat, outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqIntoKvlog(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Kvlog(nat, outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqMap(_,_)) => {
            fail_synth_exp(scope, TypeError::NoSynthRule, exp)
        },
        &Exp::PrimApp(PrimApp::SeqFilter(ref v_seq, ref e_filt)) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            Ctx |- e_filt <== (A -> F bool)
            --------------------------------- :: synth-seq-filter
            Ctx |- seq_filter(v_seq, e_filt) ==> F Seq(A)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                let a = (*a).clone();
                // let ft = CType::Arrow(a.clone(),Rc::new(CType::F(
                //     Rc::new(Type::PrimApp(PrimTyApp::Bool))
                // )));
                let ft = make_ctype![(outerctx a.clone()) -> F bool];
                if check_exp(scope, ctxt, e_filt, &ft) {
                    // Some(CType::F(Rc::new(Type::PrimApp(PrimTyApp::Seq(a)))))
                    Some(make_ctype![F Seq(outerctx a)])
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqSplit(ref v_seq, ref e_filt)) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            Ctx |- e_filt <== (A -> F bool)
            -------------------------------------------------------- :: synth-seq-split
            Ctx |- seq_filter(v_seq, e_filt) ==> F (Seq(A) x Seq(A))
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                let a = (*a).clone();
                let a2 = a.clone();
                // let ft = CType::Arrow(a.clone(),Rc::new(CType::F(
                //     Rc::new(Type::PrimApp(PrimTyApp::Bool))
                // )));
                let ft = make_ctype![(outerctx a.clone()) -> F bool];
                if check_exp(scope, ctxt, e_filt, &ft) {
                    // Some(CType::F(Rc::new(Type::PrimApp(PrimTyApp::Seq(a)))))
                    Some(make_ctype![F (Seq(outerctx a) x Seq(outerctx a2))])
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::SeqReverse(ref v_seq)) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            --------------------------------- :: synth-seq-filter
            Ctx |- seq_reverse(v_seq) ==> F Seq(A)
            */
            if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                Some(make_ctype![F Seq(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackEmpty) => {
            fail_synth_exp(scope, TypeError::EmptyDT, exp)
        },
        &Exp::PrimApp(PrimApp::StackIsEmpty(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(_))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackDup(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Stack(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackPush(ref s, ref v)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(a))) = synth_val(scope, ctxt, s) {
                let a = (*a).clone();
                if check_val(scope, ctxt, v, &a) {
                    Some(make_ctype![F Stack(outerctx a)])
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackPop(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(a))) = synth_val(scope, ctxt, s) {
                let a = (*a).clone();
                Some(make_ctype![F ((outerctx a.clone()) x Stack(outerctx a))])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackPeek(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F (outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::StackIntoSeq(ref s)) => {
            if let Some(Type::PrimApp(PrimTyApp::Stack(a))) = synth_val(scope, ctxt, s) {
                Some(make_ctype![F Seq(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueueEmpty) => {
            fail_synth_exp(scope, TypeError::EmptyDT, exp)
        },
        &Exp::PrimApp(PrimApp::QueueIsEmpty(ref q)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(_))) = synth_val(scope, ctxt, q) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueueDup(ref q)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(a))) = synth_val(scope, ctxt, q) {
                Some(make_ctype![F Queue(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueuePush(ref q, ref v)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(a))) = synth_val(scope, ctxt, q) {
                let a = (*a).clone();
                if check_val(scope, ctxt, v, &a) {
                    Some(make_ctype![F Queue(outerctx a)])
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueuePop(ref q)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(a))) = synth_val(scope, ctxt, q) {
                let a = (*a).clone();
                Some(make_ctype![F ((outerctx a.clone()) x Queue(outerctx a))])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueuePeek(ref q)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(a))) = synth_val(scope, ctxt, q) {
                Some(make_ctype![F (outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::QueueIntoSeq(ref q)) => {
            if let Some(Type::PrimApp(PrimTyApp::Queue(a))) = synth_val(scope, ctxt, q) {
                Some(make_ctype![F Seq(outerctx (*a).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogEmpty) => {
            fail_synth_exp(scope, TypeError::EmptyDT, exp)
        },
        &Exp::PrimApp(PrimApp::KvlogIsEmpty(ref l)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(_,_))) = synth_val(scope, ctxt, l) {
                Some(make_ctype![F bool])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogDup(ref l)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(a,b))) = synth_val(scope, ctxt, l) {
                Some(make_ctype![F Kvlog(outerctx (*a).clone(),outerctx (*b).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogPut(ref l, ref k, ref v)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(a,b))) = synth_val(scope, ctxt, l) {
                let a = (*a).clone();
                let b = (*b).clone();
                if check_val(scope, ctxt, k, &a) {
                    if check_val(scope, ctxt, v, &b) {
                        Some(make_ctype![F Kvlog(outerctx a, outerctx b)])
                    } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogGet(ref l, ref k)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(a,b))) = synth_val(scope, ctxt, l) {
                let a = (*a).clone();
                if check_val(scope, ctxt, k, &a) {
                    let b = (*b).clone();
                    Some(make_ctype![F ((outerctx b.clone()) x Kvlog(outerctx a, outerctx b))])         
                } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogIntoSeq(ref l)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(_,b))) = synth_val(scope, ctxt, l) {
                Some(make_ctype![F Seq(outerctx (*b).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
        &Exp::PrimApp(PrimApp::KvlogIntoHashmap(ref l)) => {
            if let Some(Type::PrimApp(PrimTyApp::Kvlog(a,b))) = synth_val(scope, ctxt, l) {
                Some(make_ctype![F Hashmap(outerctx (*a).clone(),outerctx (*b).clone())])
            } else { fail_synth_exp(scope, TypeError::ParamMism, exp) }
        },
    }
}

pub fn check_exp(scope:Option<&Name>, ctxt:&TCtxt, exp:&Exp, ctype:&CType) -> bool {
    // TODO: remove ctype from match, check it in body and maybe give type error
    match (exp, ctype) {
        (&Exp::Label(ref nm, ref e), ct) => {
            check_exp(Some(nm), ctxt, e, ct)
        },
        (&Exp::Thunk(ref e), &CType::F(ref t)) => {
            if let Type::U(ref ct) = **t {
                check_exp(scope, ctxt, e, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Ret(ref v), &CType::F(ref t)) => {
            check_val(scope, ctxt, v, t)
        },
        (&Exp::Let(_,ref x, ref e1, ref e2), ct) => {
            if let Some(CType::F(t)) = synth_exp(scope, ctxt, e1) {
                check_exp(scope, &ctxt.var(x.clone(), (*t).clone()), e2, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Lam(ref x, ref e), &CType::Arrow(ref t, ref ct)) => {
            check_exp(scope, &ctxt.var(x.clone(),(**t).clone()), e, ct)
        },
        (&Exp::Split(ref v, ref x1, ref x2, ref e), ct) => {
            if let Some(Type::Pair(t1, t2)) = synth_val(scope, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(scope, &ctxt.var(x1.clone(),t1).var(x2.clone(),t2), e, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Case(ref v, ref x1, ref e1, ref x2, ref e2), ct) => {
            if let Some(Type::Sum(t1, t2)) = synth_val(scope, ctxt, v) {
                let t1 = (*t1).clone();
                let t2 = (*t2).clone();
                check_exp(scope, &ctxt.var(x1.clone(),t1), e1, ct)
                & check_exp(scope, &ctxt.var(x2.clone(),t2), e2, ct)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Ref(ref v), &CType::F(ref t)) => {
            if let Type::Ref(ref t) = **t {
                check_val(scope, ctxt, v, t)
            } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
        },
        (&Exp::Fix(ref f, ref e), ct) => {
            /*
            Ctx, f: U(C) |- e <== C
            -----------------------
            Ctx |- fix(f.e) <== C
            */
            check_exp(scope, &ctxt.var(f.clone(), Type::U(Rc::new(ct.clone()))), e, ct)
        },
        (&Exp::PrimApp(PrimApp::SeqFoldSeq(ref v_seq, ref v_accum, ref e_body)), ct) => {
            /* 
            Ctx |- v_seq ==> Seq(A)
            Ctx |- v_accum <== B
            Ctx |- e_body <== (A -> B -> F B)
            ----------------------------------------------------- :: check-seq-fold-seq
            Ctx |- seq_fold_seq(v_list, v_accum, e_body) <== F B
            */
            if let CType::F(ref b) = *ct {
                if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                    if check_val(scope, ctxt, v_accum, b) {
                        let bt = CType::Arrow(a,Rc::new(CType::Arrow(
                            b.clone(), Rc::new(CType::F(b.clone()))
                        )));
                        check_exp(scope, ctxt, e_body, &bt)
                    } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
            } else { fail_check_exp(scope, TypeError::BadCheck, exp) }
        },
        (&Exp::PrimApp(PrimApp::SeqMap(ref v_seq, ref e_map)), ct) => {
            /*
            Ctx |- v_seq ==> Seq(A)
            Ctx |- e_map <== (A -> F(B))
            --------------------------------- :: synth-seq-map
            Ctx |- seq_map(v_seq, e_map) <== F Seq(B)
            */
            if let CType::F(ref s) = *ct {
                if let Type::PrimApp(PrimTyApp::Seq(ref b)) = **s {
                    if let Some(Type::PrimApp(PrimTyApp::Seq(a))) = synth_val(scope, ctxt, v_seq) {
                        let mt = CType::Arrow(a, Rc::new(CType::F(b.clone())));
                        check_exp(scope, ctxt, e_map, &mt)
                    } else { fail_check_exp(scope, TypeError::ParamMism, exp) }
                } else { fail_check_exp(scope, TypeError::BadCheck, exp) }
            } else { fail_check_exp(scope, TypeError::BadCheck, exp) }
        },
        (e, ct2) => {
            if let Some(ref ct1) = synth_exp(scope, ctxt, e) {
                ct2 == ct1
            } else { fail_check_exp(scope, TypeError::NoSynthRule, exp) }
        },
    }
}
