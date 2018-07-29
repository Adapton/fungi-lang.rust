use std::cell::RefCell;
use std::fmt::Write as FmtWrite;

thread_local!(static INDENT:
              RefCell<usize> =
              RefCell::new(0));

pub fn db_indent() -> usize {
    INDENT.with(|x| *x.borrow() )
}

pub fn db_region_open() {
    INDENT.with(|x| (*x.borrow_mut()) += 1 )
}

pub fn db_region_close() {
    INDENT.with(|x| (*x.borrow_mut()) -= 1 )
}

pub fn write_indent<Wr:FmtWrite>(wr: &mut Wr) {
    for _ in 0..db_indent() {
        write!(wr, "│ ").unwrap();
    }
}

pub fn newline_indent_string() -> String {
    let mut s = String::new();
    write!(s, "\n").unwrap();
    write_indent(&mut s);
    s
}

pub fn indent_string() -> String {
    let mut s = String::new();
    write_indent(&mut s);
    s
}

macro_rules! fgi_db {
    ( $fmt_string:expr ) => {{
        use db::*;
        print!("{}", indent_string());
        println!( $fmt_string );
    }};
    ( $fmt_string:expr, $( $arg:expr ),* ) => {{
        use regex::Regex;
        use db::*;
        let re = Regex::new(r"\n").unwrap();
        let s = format!( $fmt_string, $( $arg ),* );        
        let s = format!("{}{}",
                        indent_string(),
                        re.replace_all(s.as_str(), newline_indent_string().as_str()));
        println!("{}", s);            
    }}
}
