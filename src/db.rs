//use vt100;
use std::cell::RefCell;
use std::fmt::Write as FmtWrite;
use std::fmt::Display;

pub struct Frame {
    pub module_path: String,
    pub line: usize,
    pub bracket_indent: Box<Display>,
    pub bracket_close: Box<Display>,
}

thread_local!(pub static INDENT:
              RefCell<Vec<Frame>> =
              RefCell::new(vec![]));

macro_rules! fgi_db {
    ( $fmt_string:expr ) => {{
        use regex::Regex;
        use db::*;
        let re1 = Regex::new(r"\n").unwrap();
        let re2 = Regex::new(r"\^").unwrap();
        let s = format!( $fmt_string );
        let adjust = if re2.is_match(s.as_str()) { -1 } else { 0 };
        let s = format!("{}{}{}",
                        indent_string(adjust),
                        if adjust == -1 { "├᚜" } else { "" },
                        re1.replace_all(s.as_str(), newline_indent_string(0).as_str()));
        let s = format!("{}", re2.replace_all(s.as_str(), ""));
        println!("{}", s);            
    }};
    ( $fmt_string:expr, $( $arg:expr ),* ) => {{
        use regex::Regex;
        use db::*;
        let re1 = Regex::new(r"\n").unwrap();
        let re2 = Regex::new(r"\^").unwrap();
        let s = format!( $fmt_string, $( $arg ),* );
        let adjust = if re2.is_match(s.as_str()) { -1 } else { 0 };
        let s = format!("{}{}{}",
                        indent_string(adjust),
                        if adjust == -1 { "├᚜\x1B[1m" } else { "" },
                        re1.replace_all(s.as_str(), newline_indent_string(0).as_str()));
        let s = format!("{}", re2.replace_all(s.as_str(), ""));
        println!("{}\x1B[0;0m", s);
    }}
}

macro_rules! db_region_open {
    () => {{
        use db;
        use vt100;
        fgi_db!("{}{}{}{}:{}",
                vt100::Normal{},
                vt100::NormBracket::Open,
                vt100::Lo{},
                module_path!(), line!());
        db::INDENT.with(
            |x| (*x.borrow_mut()).push(
                db::Frame{
                    bracket_indent:Box::new(vt100::NormBracket::Indent),
                    bracket_close:Box::new(vt100::NormBracket::Close),
                    module_path:module_path!().to_owned(),
                    line:line!() as usize,
                }));
    }}
    ;
    // Custom bracket style
    ($($br:tt)+) => {{
        use db;
        use vt100;
        fgi_db!("{}{}{}{}:{}",
                vt100::Normal{},
                $($br)+::Open,
                vt100::Lo{},
                module_path!(), line!());
        db::INDENT.with(
            |x| (*x.borrow_mut()).push(
                db::Frame{
                    bracket_indent:Box::new($($br)+::Indent),
                    bracket_close:Box::new($($br)+::Close),
                    module_path:module_path!().to_owned(),
                    line:line!() as usize,
                }));
    }}
}

macro_rules! db_region_close {
    () => {{
        use db;
        use vt100;
        let frame = db::INDENT.with(|x| (*x.borrow_mut()).pop().unwrap() );
        //fgi_db!("└᚜═╸╸╸╸᚜\x1B[2m{}:{}\x1B[0;0m", module_path!(), line!());
        fgi_db!("{}{}{}{}:{}",
                vt100::Normal{},
                frame.bracket_close,
                vt100::Lo{},
                module_path!(), line!());
    }}
}

pub fn write_indent<Wr:FmtWrite>(wr: &mut Wr, adjust:i64) {
    use vt100;
    INDENT.with(|x| for fr in (*x.borrow()).iter() {
        write!(wr, "{}{}", vt100::Normal{}, fr.bracket_indent).unwrap();
    });
}

pub fn newline_indent_string(adjust:i64) -> String {
    let mut s = String::new();
    write!(s, "\n").unwrap();
    write_indent(&mut s, adjust);
    s
}

pub fn indent_string(adjust:i64) -> String {
    let mut s = String::new();
    write_indent(&mut s, adjust);
    s
}
