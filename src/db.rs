use std::cell::RefCell;
use std::fmt::Write as FmtWrite;

thread_local!(pub static INDENT:
              RefCell<usize> =
              RefCell::new(0));

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

pub fn db_indent() -> usize {
    INDENT.with(|x| *x.borrow() )
}

macro_rules! db_region_open {
    () => {{
        use db;
        //fgi_db!("┌᚜═╸╸╸╸᚜\x1B[2m{}:{}\x1B[0;0m", module_path!(), line!());
        fgi_db!("┌᚜\x1B[2m{}:{}\x1B[0;0m", module_path!(), line!());
        db::INDENT.with(|x| (*x.borrow_mut()) += 1 );
    }}
}

macro_rules! db_region_close {
    () => {{
        use db;
        db::INDENT.with(|x| (*x.borrow_mut()) -= 1 );
        //fgi_db!("└᚜═╸╸╸╸᚜\x1B[2m{}:{}\x1B[0;0m", module_path!(), line!());
        fgi_db!("└᚜\x1B[2m{}:{}\x1B[0;0m", module_path!(), line!());
    }}
}

pub fn write_indent<Wr:FmtWrite>(wr: &mut Wr, adjust:i64) {
    for _ in 0..((db_indent() as i64) + adjust) {
        write!(wr, "│ ").unwrap();
    }
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
