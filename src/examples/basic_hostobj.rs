/// A simple illustration of Rust values within a Fungi program
///
/// Rust side:
/// ------------
///
///  The following two functions permit Rust to transform colors
///  (as Rust values) into Fungi runtime values, and back again:
/// 
/// - `rtval_of_color`
/// - `color_of_rtval`
///
/// Fungi side:
/// --------------
///
///  The [Fungi module]() here wraps the Rust constructors and
///  functions over Colors with Fungi functions.
///
pub mod color {
    use dynamics::RtVal;
    use hostobj;


    /// Example of a user-defined datatype in Rust, to inject into
    /// Fungi.
    #[derive(Eq,PartialEq,Clone,Debug,Hash)]
    pub enum Color {
        Red, Green, Gold,
    }

    
    /// Inject a Color into a Val.
    pub fn rtval_of_color(c:Color) -> RtVal {
        hostobj::rtval_of_obj(c)
    }

    /// Un-inject the Color from a Val, if it exists.
    pub fn color_of_rtval (x:&RtVal) -> Option<Color> {
        hostobj::obj_of_rtval(x)
    }    

    fgi_mod!{hostuse{ hostobj::val_of_obj }
        // TODO:
        //  - Some way to declare new abstract types
        //
        //type Color = HostType(Color);
        val color_red   : (Color) = (^val_of_obj(Color::Red))
        val color_green : (Color) = (^val_of_obj(Color::Green))
        val color_gold  : (Color) = (^val_of_obj(Color::Gold))
        fn color_next : (Thk[0] 0 Color -> 0 F Color) = {
            unsafe (1) trapdoor::color_next
        }
    }

    #[test]
    pub fn docolors() {
        fgi_dynamic_trace!
        {[Expect::Success]
         use self::*; // import color_next
         let red   = {ret color_red}
         let green = {ret color_green}
         let gold  = {ret color_gold}
         let triple = {ret (red, green, gold)}
         let red_next = {{force color_next} red}
         let green_next = {{force color_next} green}
         let gold_next = {{force color_next} gold}
         let triple_next = {ret (red_next, green_next, gold_next)}
         ret (triple, triple_next)
        }
    }
    
    pub mod trapdoor {
        // This code essentially extends the Fungi evaluator
        use dynamics::{RtVal,ExpTerm,ret};
        use super::*;
    
        pub fn color_next(args:Vec<RtVal>) -> ExpTerm {
            match color_of_rtval(&args[0]) {
                None => panic!("expected a single color, not {:?}", args),
                Some(Color::Red)   => ret(rtval_of_color(Color::Green)),
                Some(Color::Green) => ret(rtval_of_color(Color::Gold)),
                Some(Color::Gold)  => ret(rtval_of_color(Color::Red)),
            }
        }
    }
    
}
