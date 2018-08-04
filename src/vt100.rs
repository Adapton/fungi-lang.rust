// use ast::*;
// use std::rc::Rc;
// use normal::NmSetTm;
// use normal::NmSetCons;
// use normal::NmSet;
// use bitype::Ctx;
// use decide::RelCtx;
// use decide::DecError;
// use bitype::NmTmRule;
use std::fmt;
//use std::result;
// use dynamics::RtVal;

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

pub enum Bracket { Open, Indent, Close }
trait FromBracket {
    fn from_bracket (b:Bracket) -> Self;
}
    
macro_rules! vt100_bracket {
    { $t:ident, $open:expr, $indent:expr, $close:expr } => {
        pub enum $t { Open, Indent, Close }
        impl FromBracket for $t {
            fn from_bracket (b:Bracket) -> Self {
                match b {
                    Bracket::Open   => $t::Open,
                    Bracket::Indent => $t::Indent,
                    Bracket::Close  => $t::Close,
                }
            }
        }
        impl fmt::Display for $t {
            fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result {
                write!(f,"{}", match self {
                    $t::Open   => $open,
                    $t::Indent => $indent,
                    $t::Close  => $close,
                })
            }
        }
    }
}


vt100_escape!{Normal, "0;0"}
vt100_escape!{Lo, "0;2"}
vt100_escape!{Hi, "0;1"}
vt100_escape!{HiBlue, "0;1;36"}
vt100_escape!{HiGreen, "0;1;32"}

vt100_escape!{SeamBegin, "0;1;33"}
vt100_escape!{SeamEnd, "0;1;35"}
string_constant!{SeamLineBegin, "───────────────────────────────────────────────────────────────────────────────"}
string_constant!{SeamLineEnd,   "═══════════════════════════════════════════════════════════════════════════════"}

vt100_escape!{Kw, "0;1;33"}
vt100_escape!{ValVar, "0;1;36"}
vt100_escape!{Exp, "0;0"}
vt100_escape!{Val, "0;0"}
vt100_escape!{RtVal, "0;0;35"}
vt100_escape!{ExpTerm, "0;1;35"}
vt100_escape!{DocOut,"0;1;4;37"}
vt100_escape!{AdaptonEngine,"0;1;37"}
vt100_escape!{FgiReduceEngine,"0;1;37"}

vt100_escape!{CheckType, "0;1;35"}
vt100_escape!{SynthType, "0;1;34"}

vt100_escape!{VDash, "0;1;33"}
vt100_escape!{ParamBegin, "0;33"}
vt100_escape!{ParamSep, "0;33"}
vt100_escape!{ParamEnd, "0;33"}
vt100_escape!{BigStep, "0;1;33"}
vt100_escape!{PathSep, "0;1;33"}
vt100_escape!{RuleColor, "0;33"}
vt100_bracket!{NormBracket,
               "┌᚜",
               "│ ",
               "└᚜"
}
vt100_bracket!{BoldBracket,
               "\x1B[1;37m▟░",
               "\x1B[1;37m█░",
               "\x1B[1;37m▜░"
}
vt100_bracket!{SeamEnterBracketOld,
               "\x1B[1;33m╭\x1B[1;35m╭",
               "\x1B[1;33m║\x1B[1;35m║",
               "\x1B[1;33m╰\x1B[1;35m╰"
}
vt100_bracket!{SeamEnterBracket,
               "\x1B[1;33m╭\x1B[1;35m╭",
               "\x1B[1;33m│\x1B[1;35m│",
               "\x1B[1;33m╰\x1B[1;35m╰"
}
string_constant!{RuleLine, "\x1B[1;33m───────────────────────────────────────────────────────────────────────────────"}

string_constant!{CheckMark, "\x1B[1;32m✔\x1B[0;0m"}

//string_constant!{RuleLine, "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"}
//vt100_escape!{VDash, "37;1"}
//vt100_escape!{RuleColor, "37;1"}
//vt100_escape!{HiYellowBlue, "44;33;1"}
