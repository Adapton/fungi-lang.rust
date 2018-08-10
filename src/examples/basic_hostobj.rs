pub mod color {
    use ast::Val;
    use hostobj;
    
    #[derive(Eq,PartialEq,Clone,Debug,Hash)]
    pub enum Color {
        Red, Green, Gold,
    }

    /// Inject a Color into a Val.
    pub fn val_of_color(c:Color) -> Val {
        hostobj::val_of_obj(c)
    }

    /// Project the Color from a Val, if it exists.
    pub fn color_of_val (x:&Val) -> Option<Color> {
        hostobj::obj_of_val(x)
    }    
}
