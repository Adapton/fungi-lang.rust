use regex::Regex;
use std::fmt;

// Aside: I'd really, really prefer to use the function name (not line
// number), but this path name, but this issue has been open for two
// years: https://github.com/rust-lang/rfcs/issues/1743
//
// Also, can't use `::` on Windows, so using `.` instead:
// https://msdn.microsoft.com/en-us/library/aa365247
//

// Convert a Rust module path into an acceptable file name (as a string)
pub fn filename_of_module_path_(module_path:&str) -> String {
    // Module paths (via module_path!()) in Rust contain the token
    // `::`, but we cannot use `::` on Windows for the names of files,
    // so we will use period (`.`) instead:
    //
    // https://msdn.microsoft.com/en-us/library/aa365247
    //
    let re = Regex::new(r"::").unwrap();
    format!("{}", re.replace_all(module_path, "."))
}

// A file name (as a string) from the current module path
#[macro_export]
macro_rules! filename_of_module_path {
    () => {{
        use util::filename_of_module_path_;
        filename_of_module_path_(module_path!())
    }}
}

// Convert rust doc "raw" strings into strings without double quotes or 'r' prefix
pub fn string_of_rust_raw_str(s:&str) -> String {
    let re1 = Regex::new("^r\" ").unwrap();
    let re2 = Regex::new("\"$").unwrap();
    format!("{}", re2.replace_all(format!("{}", re1.replace_all(s, "")).as_str(), ""))
}

pub fn debug_truncate<X:fmt::Debug>(x: &X) -> String {
    let x = format!("{:?}", x);
    format!("{:.80}{}", x, if x.len() > 80 { " ..." } else { "`" } )
}

pub fn display_truncate<X:fmt::Display>(x: &X) -> String {
    let x = format!("{}", x);
    format!("{:.80}{}", x, if x.len() > 80 { " ..." } else { "" } )
}

// pub fn vt100_debug_truncate<X:fmt::Debug>(x: &X, color_code:usize) -> String {
//     let x = format!("{:?}", x);
//     format!("\x1B[1;{}m{:.80}{}\x1B[0;0m",
//             color_code,
//             x,
//             if x.len() > 80 { "\x1B[2m..." } else { "" }
//     )
// }

// pub fn vt100_display_truncate<X:fmt::Display>(x: &X, color_code:usize) -> String {
//     let x = format!("{}", x);
//     format!("\x1B[1;{}m{:.80}{}\x1B[0;0m",
//             color_code,
//             x,
//             if x.len() > 80 { "\x1B[2m..." } else { "" }
//     )
// }
