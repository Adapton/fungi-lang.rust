//use std::fs;
//use std::io;
use std::io::prelude::*;
//use std::io::BufWriter;
//use std::fs::File;
use std::collections::HashMap;

use adapton::engine::Name;
use adapton::reflect::*;
use adapton::reflect::trace::EffectEdge;

//use adapton::engine::reflect::{trace, string_of_name, string_of_loc};
//use labdef::{LabParams,Lab,LabResults, Sample};

/// The `Div` struct represents a restricted form of a `<div>` element
/// in HTML.  The field `tag` is a string, which corresponds to a
/// distinguished `tag` CSS class that indicates the Rust datatype
/// reflected into this `Div`.  The other CSS `classes` hold bits that
/// signal various subcases (e.g., of `enum`s in the `reflect`
/// module).  For Rust structures that have subfields and/or
/// substructure, the `Div`'s `extent` field lists their reflections
/// into `Div`s.  In principle, the produced `Div` structure has an
/// equivalent amount of information to the corresponding Rust
/// datatype, and could be "parsed" back into this Rust datatype later
/// (let's not do that, though!).  The text field is useful for `Div`
/// versions of `Name`s, for giving the text of the name.
#[derive(Debug,Clone)]
pub struct Div {
  pub tag:     String,
  pub classes: Vec<String>,
  pub extent:  Box<Vec<Div>>,
  pub text:    Option<String>,
}

// Questions:
// Reflections of names? 
// Do we expose their internal structure as `div`s, or stringify them?
// For paths, clearly we wanted to expose their structure.
// Perhaps for forked names such as `11.L.r.L` we'll want something similar?

// Thoughts:

// Both: We want names to be like strings when they are used as CSS
// classes that control when, during user interaction, certain div
// elements highlight, focus or toggle between hide/show.  On the
// other hand, we may also want the user to be able to see and inspect
// the internal structure of names, e.g., to select/highlight related
// names in the lineage.  E.g., `11.L.r.L` is likely related to
// `11.L.r.r` since a single `fork` operation produced them both.

pub fn div_of_name (n:&Name) -> Div {
  Div{ tag: String::from("name"),
       // TODO: Remove illegal chars for CSS classes (check spec)
       // classes: vec![ format!("{:?}", n) ],
       classes: vec![ string_of_name(n) ],
       extent: Box::new( vec![ ] ),
       text: Some( format!("{}", string_of_name(n) ) ) }
}

pub fn div_of_path (p:&Path) -> Div {
  Div{ tag: String::from("path"),
       //classes: vec![ format!("{:?}", p) ],
       classes: vec![ ],
       extent: Box::new(
         p.iter().map( div_of_name ).collect()
       ),
       text: None }
}

pub fn div_of_loc (l:&Loc) -> Div {
  Div{ tag: String::from("loc"),
       // TODO: Remove illegal chars for CSS classes (check spec)
       //classes: vec![ format!("{:?}", l) ],
       classes: vec![ ],       
       extent: Box::new(vec![ div_of_path(&l.path), div_of_name(&l.name) ]),
       //text: Some( format!("{:?}",l) )
       text:None,
  }
}

pub fn div_of_oploc (ol:&Option<Loc>) -> Div {
  if true {
    Div{ tag: String::from("oploc"), 
         classes: vec![],
         extent: Box::new(vec![]),
         text: None,
    }
  } else {
    Div{ tag: String::from("oploc"),
         classes: vec![],
         extent: Box::new(match *ol { 
           None => vec![],
           Some(ref l) => vec![ div_of_loc(l)]}),
         text: None
    }
  }
}

pub fn div_of_succ (s:&Succ) -> Div {
  Div{ tag: String::from("succ"),
       classes: vec![
         String::from(match s.effect {
           Effect::Alloc => "succ-alloc",
           Effect::Force => "succ-force"
         }),
         String::from(match s.dirty {
           true  => "succ-dirty",
           false => "succ-not-dirty"
         }),
       ],
       text: None,
       extent: Box::new(vec![
         div_of_loc(&s.loc),
       ])}
}

pub fn div_of_edge (e:&trace::Edge) -> Div {
  Div{ tag: String::from("edge"),
       classes: vec![],
       text: None,
       extent: Box::new(
         vec![ div_of_oploc(&e.loc),
               div_of_succ(&e.succ) ]) }
}

pub fn div_of_effect_edge (e:&trace::EffectEdge) -> Div {
    match e {
        EffectEdge::Fwd(e) => {
            Div{ tag: String::from("edge"),
                 classes: vec![],
                 text: None,
                 extent: Box::new(
                     vec![ div_of_oploc(&e.loc),
                           div_of_succ(&e.succ) ]) }
        }
        // TODO: Distinguish this case?
        EffectEdge::Bwd(e) => {
            Div{ tag: String::from("edge"),
                 classes: vec![],
                 text: None,
                 extent: Box::new(
                     vec![ div_of_oploc(&e.loc),
                           div_of_succ(&e.succ) ]) }
        }
        EffectEdge::None => {
            Div{ tag: String::from("none"),
                 classes: vec![],
                 text: None,
                 extent: Box::new(vec![ ]) }
        }
    }
}

pub fn div_of_value_tree (dcg:&DCG, visited:&mut HashMap<Loc, ()>, val:&Val) -> Div {
  let div = Div {
    tag: match *val {
      Val::Constr(ref n, _) => { format!("val-constr constr-{}", string_of_name(n) ) },
      Val::Struct(ref n, _) => { format!("val-struct struct-{}", string_of_name(n) ) },
      Val::Const( ref c )     => { format!("val-const  const-{}" , match *c {
        Const::Nat( ref n ) => format!("{}", n),
        Const::Num( ref n ) => format!("{}", n),
        Const::String( ref s ) => s.clone(),
      })},
      Val::Tuple(ref vs) => { format!("val-tuple tuple-{}", vs.len()) },
      Val::Vec(ref vs) => { format!("val-vec vec-{}", vs.len()) },
      Val::Art(ref loc, _) => { format!("val-art {}", string_of_loc( loc ) ) },
      Val::ValTODO => { format!("val-TODO") },
      Val::Name(ref n) => { format!("name val-name {}", string_of_name(n)) },
    },
    classes: vec![],
    text: 
      match *val {
        Val::Constr(ref n, _) => { Some(string_of_name(n)) },
        Val::Struct(ref n, _) => { Some(string_of_name(n)) },
        Val::Const( ref c )     => Some(match *c {
          Const::Nat( ref n ) => format!("{}", n),
          Const::Num( ref n ) => format!("{}", n),
          Const::String( ref s ) => format!("{:?}", s),
        }),
        Val::Tuple( _ ) => None,
        Val::Vec( _ ) => None,
        Val::ValTODO => None,
        Val::Art( ref l, _ ) => {
          Some(format!("{}", string_of_loc(l)))
        }
        Val::Name(ref n) => {
          Some(format!("{}", string_of_name(n)))
        }
      },
    
    extent: Box::new(
      match *val {
        Val::Constr(_, ref vs) => { let ds : Vec<_> = vs.iter().map( |v| div_of_value_tree(dcg, visited,  v) ).collect() ; ds },
        Val::Struct(_, ref fs) => { let ds : Vec<_> = fs.iter().map(  |&(ref _f, ref v) | 
                                                                         div_of_value_tree(dcg, visited, &v) ).collect() ; ds },
        Val::Tuple(ref vs) =>     { let ds : Vec<_> = vs.iter().map( |v| div_of_value_tree(dcg, visited,  v) ).collect() ; ds },
        Val::Vec(ref vs) =>       { let ds : Vec<_> = vs.iter().map( |v| div_of_value_tree(dcg, visited,  v) ).collect() ; ds },
        Val::Const( _ ) => vec![],
        Val::ValTODO => vec![],
        Val::Name(_) => vec![],
        Val::Art( ref l, _ ) => vec![
          div_of_loc(l), 
          match dcg.table.get(l) {
            None => Div{ tag: String::from("dangling"), 
                         classes:vec![String::from("no-extent")], 
                         text:Some(String::from("Dangling")), 
                         extent:Box::new(vec![]),
            },
            Some(node) => {
              match *node {
                Node::Pure(ref p) => div_of_value_tree(dcg, visited, &p.value),
                Node::Ref(ref n) => div_of_value_tree(dcg, visited, &n.value),
                Node::Comp(ref n) => match n.value {
                  None => 
                    Div{ tag: String::from("Unevald"), 
                         classes:vec![String::from("no-extent")], 
                         text:Some(String::from("Uneval'd")), 
                         extent:Box::new(vec![]),
                    },
                  Some(ref v) => div_of_value_tree(dcg, visited, v),
                }
              }
            }
          }
        ],
      }
    )
  }
  ;
  div
}

pub fn div_of_force_tree (dcg:&DCG, visited:&mut HashMap<Loc, ()>, loc:&Loc) -> Div {  
  let mut div = Div {
    tag:String::from("force-tree"),
    text:None,
    classes: vec![],
    extent: Box::new(vec![ div_of_loc( loc ) ]),
  };
  visited.insert( loc.clone(), () );
  let no_extent = match dcg.table.get( loc ) {
    None => panic!("dangling pointer in reflected DCG!"),
    Some( nd ) => {
      match succs_of_node( nd ) {
        None => true, // No succs; E.g., ref cells have no succs
        Some( succs ) => {
          let mut no_extent = true;
          for succ in succs {
            if succ.effect == Effect::Force {
              no_extent = false;
              let succ_div = div_of_force_tree (dcg, visited, &succ.loc);
              div.extent.push( succ_div )
            }
          };
          no_extent
        }
      }
    }
  };
  if no_extent {
    div.classes.push(String::from("no-extent"))
  };
  div
}

pub fn div_of_alloc_tree (dcg:&DCG, visited:&mut HashMap<Loc, ()>, loc:&Loc) -> Div {  
  let mut div = Div {
    tag:String::from("alloc-tree"),
    text:None,
    classes: vec![],
    extent: Box::new(vec![ div_of_loc( loc ) ]),
  };
  visited.insert( loc.clone(), () );
  let no_extent = match dcg.table.get( loc ) {
    None => panic!("dangling pointer in reflected DCG!"),
    Some( nd ) => {
      match succs_of_node( nd ) {
        None => true, // No succs; E.g., ref cells have no succs
        Some( succs ) => {
          let mut no_extent = true;
          for succ in succs {
            if succ.effect == Effect::Alloc {
              no_extent = false;
              let succ_div = div_of_alloc_tree (dcg, visited, &succ.loc);
              div.extent.push( succ_div )
            }
          };
          no_extent
        }
      }
    }
  };
  if no_extent {
    div.classes.push(String::from("no-extent"))
  };
  div
}


pub fn class_of_dcg_node (nd:&Node) -> String {
  match *nd {
    Node::Comp(_) => String::from("dcg-node-comp"),
    Node::Ref(_) => String::from("dcg-node-ref"),
    Node::Pure(_) => String::from("dcg-node-pure"),
  }
}

pub fn div_of_dcg_alloc_edge (src:Option<&Loc>, loc:&Loc, nd:&Node, is_dirty:bool) -> Div {
  let div = Div {
    tag:String::from("dcg-alloc-edge"),
    text:None,
    classes: vec![ if is_dirty { String::from("dirty") } else { String::from("clean") },
                   if src == None { String::from("editor-edge") } else { String::from("dcg-edge") },
                   class_of_dcg_node( nd ) ],
    extent: Box::new(vec![ div_of_loc( loc ) ]),
  };
  div
}

pub fn div_of_dcg_succs (dcg:&DCG, visited:&mut HashMap<Loc, ()>, loc:Option<&Loc>, 
                         succs: &Vec<Succ>,
                         extent: &mut Vec<Div>) {  
  for succ in succs {
    match succ.effect {
      Effect::Alloc => {
        let node = dcg.table.get( &succ.loc ).unwrap();
        let succ_div = div_of_dcg_alloc_edge (loc, &succ.loc, &node, succ.dirty);
        extent.push( succ_div )
      },
      Effect::Force => {
        let succ_div = div_of_dcg_force_edge (loc, dcg, visited, &succ.loc, succ.dirty, succ.is_dup);
        extent.push( succ_div )
      }
    }     
  }
}

pub fn div_of_dcg_force_edge (src:Option<&Loc>, dcg:&DCG, visited:&mut HashMap<Loc, ()>, 
                              loc:&Loc, is_dirty:bool, is_dup:bool) -> Div 
{  
  let mut div = Div {
    tag:String::from("dcg-force-edge"),
    text:None,
    classes: vec![ 
      if is_dup   { String::from("dup-edge") } else { String::from("not-dup-edge") },
      if is_dirty { String::from("dirty") } else { String::from("clean") }, 
      if src == None { String::from("editor-edge") } else { String::from("dcg-edge") },
    ],    
    extent: Box::new(vec![ div_of_loc( loc ) ]),
  };
  visited.insert( loc.clone(), () );
  let no_extent = match dcg.table.get( loc ) {
    None => panic!("dangling pointer in reflected DCG!"),
    Some( nd ) => {
      div.classes.push( class_of_dcg_node(nd) );
      match succs_of_node( nd ) {
        None => true, // No succs; E.g., ref cells have no succs
        Some( succs ) => { 
          div_of_dcg_succs(dcg, visited, Some(loc), succs, &mut div.extent);
          false
        }
      }
    }
  };
  if no_extent {
    div.classes.push(String::from("no-extent"))
  };
  div
}

pub fn div_of_trace (tr:&trace::Trace) -> Div {
  // For linking to rustdoc documentation from the output HTML
  let tr_eff_url = "https://docs.rs/adapton/0/adapton/reflect/trace/enum.Effect.html";
  let mut div = 
    Div{ 
      tag: String::from("trace"),
      text: None,
      classes: vec![
          match tr.effect {
          trace::Effect::UserEffect(_, ref s) => format!("tr-user-{}",s),
          trace::Effect::DebugLabel(Some(ref n),_) => format!("tr-db-{:?}",n),
          trace::Effect::DebugLabel(None,_) => "tr-db".to_string(),
          trace::Effect::CleanRec  => "tr-clean-rec".to_string(),
          trace::Effect::CleanEval => "tr-clean-eval".to_string(),
          trace::Effect::CleanEdge => "tr-clean-edge".to_string(),
          trace::Effect::Dirty     => "tr-dirty".to_string(),
          trace::Effect::Remove    => "tr-remove".to_string(),
          trace::Effect::Alloc(trace::AllocCase::LocFresh,_)     => "tr-alloc-loc-fresh".to_string(),
          trace::Effect::Alloc(trace::AllocCase::LocExists(trace::ChangeFlag::ContentSame),_) => "tr-alloc-loc-exists-same".to_string(),
          trace::Effect::Alloc(trace::AllocCase::LocExists(trace::ChangeFlag::ContentDiff),_) => "tr-alloc-loc-exists-diff".to_string(),
          //trace::Effect::Force(_) if tr.edge.succ.is_dup         => "tr-force-dup",
          trace::Effect::Force(trace::ForceCase::CompCacheMiss)  => "tr-force-compcache-miss".to_string(),
          trace::Effect::Force(trace::ForceCase::CompCacheHit)   => "tr-force-compcache-hit".to_string(),
          trace::Effect::Force(trace::ForceCase::RefGet)         => "tr-force-refget".to_string(),
        }
      ],
      extent: Box::new(
        vec![
          Div{ 
            tag: String::from("tr-effect"),
            text: Some(              
              format!("<a href={:?}>{}</a>", tr_eff_url, match tr.effect {
                trace::Effect::UserEffect(_,ref s) => format!("UserEffect({})",s),
                trace::Effect::DebugLabel(None,ref s) => format!("DebugLabel(None,{})",s),
                trace::Effect::DebugLabel(Some(ref n),ref s) => format!("DebugLabel({:?},{})",n,s),
                trace::Effect::CleanRec  => "CleanRec".to_string(),
                trace::Effect::CleanEval => "CleanEval".to_string(),
                trace::Effect::CleanEdge => "CleanEdge".to_string(),
                trace::Effect::Dirty     => "Dirty".to_string(),
                trace::Effect::Remove    => "Remove".to_string(),
                trace::Effect::Alloc(trace::AllocCase::LocFresh,_)     => "Alloc(LocFresh)".to_string(),
                trace::Effect::Alloc(trace::AllocCase::LocExists(trace::ChangeFlag::ContentSame),_) => "Alloc(LocExists(SameContent))".to_string(),
                trace::Effect::Alloc(trace::AllocCase::LocExists(trace::ChangeFlag::ContentDiff),_) => "Alloc(LocExists(DiffContent))".to_string(),
                //trace::Effect::Force(_) if tr.edge.succ.is_dup         => "ForceDup",
                trace::Effect::Force(trace::ForceCase::CompCacheMiss)  => "Force(CompCacheMiss)".to_string(),
                trace::Effect::Force(trace::ForceCase::CompCacheHit)   => "Force(CompCacheHit)".to_string(),
                trace::Effect::Force(trace::ForceCase::RefGet)         => "Force(RefGet)".to_string(),
              })),
            classes: vec![],
            extent: Box::new(vec![]),
          },
          Div{
            tag: String::from("tr-symbols"),
            text: match tr.effect {
              trace::Effect::Alloc(_,trace::AllocKind::RefCell) => Some(String::from("▣")),
              trace::Effect::Alloc(_,trace::AllocKind::Thunk)   => Some(String::from("◯")),
              _ => None,              
            },
            classes:vec![],
            extent: Box::new(vec![]),
          },            
          div_of_effect_edge(&tr.edge)

            /*
          // This is where the location (path and name) are DIV-ified
          // If the effect is a CleanEval, then we should use the
          // location at the *source* of the edge, which is the
          // location we re-evaluate.
          match (tr.effect.clone(), tr.edge.loc.clone()) {            
            (trace::Effect::CleanEval, Some(loc)) => div_of_loc(&loc),
            // TODO: Figure out why/when we get None here; seems like a reflection issue in the Engine
            _ => div_of_edge(&tr.edge)
          }*/
        ])}
  ;
  match tr.effect {
    trace::Effect::Alloc(_,trace::AllocKind::RefCell) => div.classes.push(String::from("alloc-kind-refcell")),
    trace::Effect::Alloc(_,trace::AllocKind::Thunk)   => div.classes.push(String::from("alloc-kind-thunk")),
    _ => ()
  };
  if tr.extent.len() > 0 {
    div.classes.push( String::from("has-extent") );
    div.extent.push(
      Div{ tag: String::from("tr-extent"),
           text: None,
           classes: vec![],
           extent: 
           Box::new(tr.extent.iter().map(div_of_trace).collect())
      }
    )
  } else {
    div.classes.push( String::from("no-extent") );
  };
  return div
}

pub trait WriteHTML {
  fn write_html<Wr:Write>(&self, wr: &mut Wr);
}

impl WriteHTML for Div {
  fn write_html<Wr:Write>(&self, wr: &mut Wr) {    
    writeln!(wr, "<div class=\"{} {}\">", 
             self.tag, 
             self.classes.iter().fold(
               String::new(), 
               |mut cs,c|{cs.push_str(" ");
                          cs.push_str(c.as_str()); cs}
             )
    ).unwrap();
    match self.text {
      None => (),
      Some(ref text) => writeln!(wr, "{}", text).unwrap()
    };
    for div in self.extent.iter() {
      div.write_html(wr);
    };
    writeln!(wr, "</div>").unwrap();
  }
}

impl<T:WriteHTML> WriteHTML for Vec<T> {
  fn write_html<Wr:Write>(&self, wr:&mut Wr) {
    for x in self.iter() {
      x.write_html(wr);
    }
  }
}

// pub fn write_lab_results_summary
//   (_params:&LabParams, 
//    labs:&Vec<Box<Lab>>, 
//    results:&Vec<LabResults>) 
// {
//   // Create directories and files on local filesystem:
//   fs::create_dir_all("lab-results").unwrap();
//   let f = File::create(format!("lab-results/index.html")).unwrap();
//   let mut writer = BufWriter::new(f);

//   writeln!(writer, "{}", style_string()).unwrap();
//   writeln!(writer, "<style> .tool-label-toggles {{ display: none }} </style>").unwrap();

//   assert!( labs.len() == results.len() );

//   writeln!(writer, "<div class={:?}>Lab results summary</div>", "labsum-title").unwrap();

//   for ((_i,lab),(_j,_result)) in 
//     labs.iter().enumerate().zip(results.iter().enumerate()) 
//   {
//     writeln!(&mut writer, "<div class={:?}>", "labsum-row").unwrap();
//     writeln!(&mut writer, "<div class={:?}>", "labsum-name").unwrap();
//     write_lab_name(&mut writer, lab, false);
//     writeln!(&mut writer, "</div>").unwrap();
    
//     writeln!(&mut writer, "<a class={:?} href=./{}/index.html>detailed results</a>", 
//              "lab-details", 
//              string_of_name(&lab.name())
//     ).unwrap();

//     writeln!(&mut writer, "</div>").unwrap();        
//     write_cr(&mut writer);
//   }
// }

// pub fn write_cr<W:Write>(writer:&mut W) {
//   /// We style this with clear:both, and without any appearance
//   writeln!(writer, "<hr/>").unwrap();
// }

// pub fn write_lab_name<W:Write>(writer:&mut W, lab:&Box<Lab>, is_title:bool) {
//   let catalog_url = String::from("http://adapton.org/rustdoc/adapton_lab/catalog/index.html");

//   let labname = string_of_name( &lab.name() );
//   let laburl  = lab.url();

//   writeln!(writer, "<div class={:?}><a href={:?} class={:?}>{}</a></div>", 
//            "lab-name",
//            match *laburl {
//              Some(ref url) => url,
//              None => & catalog_url
//            },
//            format!("lab-name {}", if is_title { "page-title" } else { "" }), 
//            labname
//   ).unwrap();
// }

/*
pub fn write_dcg_tree<W:Write> (writer:&mut W, dcg:&DCG, traces:&Vec<trace::Trace>) {
  let mut visited = HashMap::new();
  let mut extent : Vec<_> = Vec::new();
  let succs : Vec<_> = traces.iter().map(|t| t.edge.succ.clone()).collect();
  div_of_dcg_succs(dcg, &mut visited, None, &succs, &mut extent);
  for d in extent.iter() {
    d.write_html(writer);
  }
}

pub fn write_dcg_edge_tree<W:Write> (writer:&mut W, dcg:&DCG, traces:&Vec<trace::Trace>, effect:Effect) {
  for tr in traces.iter() {
    if tr.edge.succ.effect == effect {
      match effect {
        Effect::Alloc =>
          div_of_alloc_tree(dcg, &mut HashMap::new(), &tr.edge.succ.loc)
          .write_html(writer),
        Effect::Force =>
          div_of_force_tree(dcg,&mut HashMap::new(),  &tr.edge.succ.loc)
          .write_html(writer),
      }
    }
  }
}
*/

// pub fn write_sample_dcg<W:Write>
//   (writer:&mut W,
//    prev_sample:Option<&Sample>,
//    this_sample:&Sample)
// {
//   write_cr(writer)
//     ;
//   match this_sample.dcg_sample.process_input.reflect_dcg {
//     None => { },
//     Some(ref dcg_post_edit) => {
//       match this_sample.dcg_sample.input {
//         None => { },
//         Some(ref input) => {
//           writeln!(writer, "<div class=\"input-value\">").unwrap();
//           writeln!(writer, "<div class=\"label\">{}</div>", "Input:").unwrap();
//           div_of_value_tree(dcg_post_edit, &mut HashMap::new(), input)
//             .write_html( writer );
//           writeln!(writer, "</div>").unwrap();
//         }
//       }
//     }
//   }
//   ;
//   match this_sample.dcg_sample.compute_output.reflect_dcg {
//     None => { },
//     Some(ref dcg_post_update) => {      
//       match this_sample.dcg_sample.output {
//         None => { },
//         Some(ref output) => {
//           writeln!(writer, "<div class=\"output-value\">").unwrap();
//           writeln!(writer, "<div class=\"label\">{}</div>", "Output:").unwrap();
//           div_of_value_tree(dcg_post_update, &mut HashMap::new(), output)
//             .write_html( writer );            
//           writeln!(writer, "</div>").unwrap();            
//         }
//       }
//     }
//   }
//   ;
//   // Separate the input and output from the DCG trees, below
//   write_cr(writer);
//   ;
//   match this_sample.dcg_sample.process_input.reflect_dcg {
//     Some(ref dcg_post_edit) => {
//       match prev_sample {
//         Some(ref prev_sample) => {
        
//           // // 0/4: dcg for compute, after this edit, but before the update
//           writeln!(writer, "<div class=\"archivist-dcg-tree-post-edit\">").unwrap();
//           writeln!(writer, "<div class=\"label\">{}</div>", "DCG, post-edit:").unwrap();
//           write_dcg_tree
//             (writer, 
//              dcg_post_edit,
//              &prev_sample.dcg_sample.compute_output.reflect_traces,
//             );
//           writeln!(writer, "</div>").unwrap();
          
//           if false {
//           // 1/4: alloc tree for compute, after this edit, but before the update
//           writeln!(writer, "<div class=\"archivist-alloc-tree-post-edit\">").unwrap();
//           writeln!(writer, "<div class=\"label\">{}</div>", "Allocs, post-edit:").unwrap();
//           write_dcg_edge_tree
//             (writer, 
//              dcg_post_edit,
//              &prev_sample.dcg_sample.compute_output.reflect_traces,
//              Effect::Alloc
//             );
//           writeln!(writer, "</div>").unwrap();
          
//           // 2/4: force tree for compute, after this edit, but before the update
//           writeln!(writer, "<div class=\"archivist-force-tree-post-edit\">").unwrap();
//           writeln!(writer, "<div class=\"label\">{}</div>", "Forces, post-edit:").unwrap();
//           write_dcg_edge_tree
//             (writer, 
//              dcg_post_edit,
//              &prev_sample.dcg_sample.compute_output.reflect_traces,
//              Effect::Force,         
//             );
//           writeln!(writer, "</div>").unwrap();
//           }

//         },    
//         _ => {
//           writeln!(writer,"<div class=\"archivist-alloc-tree-post-edit\"></div>").unwrap();
//           writeln!(writer,"<div class=\"archivist-force-tree-post-edit\"></div>").unwrap();
//         }}
//     },    
//     _ => {
//       //writeln!(writer,"<div class=\"archivist-alloc-tree-post-edit\"></div>").unwrap();
//       //writeln!(writer,"<div class=\"archivist-force-tree-post-edit\"></div>").unwrap();
//     }
//   }
//   ;
//   writeln!(writer,"<div class=\"archivist-update-sep\"></div>").unwrap();
 
//   match this_sample.dcg_sample.compute_output.reflect_dcg {
//     Some(ref dcg_post_update) => {

//       // // 0/4: dcg for compute, after this edit, but before the update
//       writeln!(writer, "<div class=\"archivist-dcg-tree-post-update\">").unwrap();
//       writeln!(writer, "<div class=\"label\">{}</div>", "DCG, post-compute:").unwrap();
//       write_dcg_tree
//         (writer, 
//          dcg_post_update,
//          &this_sample.dcg_sample.compute_output.reflect_traces,
//         );
//       writeln!(writer, "</div>").unwrap();
      
//       if false {
//       // 3/4: alloc tree for compute, after the update
//       writeln!(writer, "<div class=\"archivist-alloc-tree-post-update\">").unwrap();
//       writeln!(writer, "<div class=\"label\">{}</div>", "Allocs, post-update:").unwrap();
//       write_dcg_edge_tree
//         (writer, 
//          dcg_post_update,
//          &this_sample.dcg_sample.compute_output.reflect_traces,
//          Effect::Alloc
//         );
//       writeln!(writer, "</div>").unwrap();
      
//       // 4/4: force tree for compute, after the update
//       writeln!(writer, "<div class=\"archivist-force-tree-post-update\">").unwrap();
//       writeln!(writer, "<div class=\"label\">{}</div>", "Forces, post-update:").unwrap();
//       write_dcg_edge_tree
//         (writer, 
//          dcg_post_update,
//          &this_sample.dcg_sample.compute_output.reflect_traces,
//          Effect::Force,         
//         );
//       writeln!(writer, "</div>").unwrap();
//       }
      
//       write_cr(writer);
//     },    
//     _ => {
//       //writeln!(writer,"<div class=\"archivist-alloc-tree-post-update\"></div>").unwrap();
//       //writeln!(writer,"<div class=\"archivist-force-tree-post-update\"></div>").unwrap();
//     }
//   };

// }

// pub fn write_lab_results(params:&LabParams, lab:&Box<Lab>, results:&LabResults) {
  
//   // If we are reflecting the trace, do not bother writing out the
//   // times; the purpose was probably visualization.
//   // TODO: Make this logic better.
//   let write_times = if params.sample_params.reflect_trace { false } else { true };    

//   let labname = string_of_name( &lab.name() );
//   //let laburl  = lab.url();

//   // For linking to rustdoc documentation from the output HTML
//   //let trace_url   = "http://adapton.org/rustdoc/adapton/engine/reflect/trace/struct.Trace.html";
  
//   // Create directories and files on local filesystem:
//   fs::create_dir_all(format!("lab-results/{}/", labname)).unwrap();
//   let f = File::create(format!("lab-results/{}/index.html", labname)).unwrap();
//   let mut writer = BufWriter::new(f);
//   writeln!(writer, "{}", style_string()).unwrap();  
//   writeln!(writer, "<a href=\"../index.html\">↰ Results summary</a>").unwrap();
//   write_cr(&mut writer);
//   write_lab_name(&mut writer, lab, true);
//   writeln!(writer, "<div style=\"font-size:12px\" class=\"batch-name\"> step</div>").unwrap();  
//   if write_times {
//     writeln!(writer, "<div style=\"font-size:20px\" class=\"editor\">Editor</div>").unwrap();
//     writeln!(writer, "<div style=\"font-size:20px\" class=\"archivist\">Archivist</div>").unwrap();
//   }  
//   let mut prev_sample = None;
//   for sample in results.samples.iter() {
//     write_cr(&mut writer);
//     // - - - - - - - 
//     // 0. Write batch name (a counter); and write timing information for this edit batch.
//     writeln!(writer, "<div class=\"batch-name-lab\">batch name<div class=\"batch-name\">{:?}</div></div>", 
//              sample.batch_name).unwrap();
    
//     if write_times {
//       writeln!(writer, "<div class=\"editor\">").unwrap();
      
//       writeln!(writer, "<div class=\"time-ns-lab\">time (ns): <div class=\"time-ns\">{:?}</div></div>", 
//                sample.dcg_sample.process_input.time_ns).unwrap();    
//       writeln!(writer, "</div>").unwrap();
      
//       writeln!(writer, "<div class=\"archivist\">").unwrap();
      
//       writeln!(writer, "<div class=\"row\">").unwrap();
      
//       writeln!(writer, "<div class=\"time-ns-lab\">Naive time (ns): <div class=\"time-ns\">{:?}</div></div>", 
//                sample.naive_sample.compute_output.time_ns).unwrap();    
      
//       writeln!(writer, "<div class=\"time-ms-lab\">Naive time (ms): <div class=\"time-ms\">{:.*}</div></div>", 
//                2, (sample.naive_sample.compute_output.time_ns as f64) / (1000_000 as f64)).unwrap();
//       writeln!(writer, "</div>").unwrap();
      
//       writeln!(writer, "<div class=\"row\">").unwrap();
//       writeln!(writer, "<div class=\"time-ns-lab\">DCG time (ns): <div class=\"time-ns\">{:?}</div></div>", 
//                sample.dcg_sample.compute_output.time_ns).unwrap();    
      
//       writeln!(writer, "<div class=\"time-ms-lab\">DCG time (ms): <div class=\"time-ms\">{:.*}</div></div>", 
//                2, (sample.dcg_sample.compute_output.time_ns as f64) / (1000_000 as f64)).unwrap();
//       writeln!(writer, "</div>").unwrap();
      
//       if sample.naive_sample.compute_output.time_ns <
//         sample.dcg_sample.compute_output.time_ns {
//           writeln!(writer, "<div class=\"overhead-lab\">DCG Overhead: <div class=\"overhead\">{:.*}</div></div>", 
//                    2, ( (sample.dcg_sample.compute_output.time_ns  as f64) / 
//                          (sample.naive_sample.compute_output.time_ns as f64) )).unwrap();      
//         } else {      
//           writeln!(writer, "<div class=\"speedup-lab\">DCG Speedup: <div class=\"speedup\">{:.*}</div></div>", 
//                    2, ( (sample.naive_sample.compute_output.time_ns  as f64) / 
//                          (sample.dcg_sample.compute_output.time_ns as f64) )).unwrap();
//         }    
      
//       writeln!(writer, "</div>").unwrap();
//       write_cr(&mut writer);    
//     }

//     // 1. Write input,
//     // 2. Write output,
//     // 3. Write last DCG, after edit but before update.
//     // 4. Write DCG of the update.
//     write_sample_dcg(&mut writer, lab, prev_sample, sample);      
    
//     if sample.dcg_sample.compute_output.reflect_traces.len() == 0 {
//       // 5 & 6. No traces to write.
//     } else {
//       // - - - - - - - 
//       // 5. Write traces of editor
      
//       writeln!(writer, "<div class=\"traces-box\">").unwrap();
//       // writeln!(writer, "<div class=\"time-ns-lab\">time (ns): <div class=\"time-ns\">{:?}</div></div>", 
//       //          sample.dcg_sample.process_input.time_ns).unwrap();    
//       // writeln!(writer, "<div class=\"traces-lab\">Traces (<a href={:?}>doc</a>)</div>", trace_url).unwrap();    
//       writeln!(writer, "<div class=\"label\">{}</div>", "Editor trace:").unwrap();
//       writeln!(writer, "<div class=\"traces\">").unwrap();
//       for tr in sample.dcg_sample.process_input.reflect_traces.iter() {
//         div_of_trace(tr).write_html(&mut writer)
//       }
//       writeln!(writer, "</div>").unwrap();   
//       writeln!(writer, "</div>").unwrap();
      
//       // - - - - - - - 
//       // 6. Write traces of archivist

//       //writeln!(writer, "<div class=\"traces-lab\">Traces (<a href={:?}>doc</a>):</div>", trace_url).unwrap();
//       writeln!(writer, "<div class=\"traces-box\">").unwrap();
//       writeln!(writer, "<div class=\"label\">{}</div>", "Archivist trace:").unwrap();
//       writeln!(writer, "<div class=\"traces\">").unwrap();
//       for tr in sample.dcg_sample.compute_output.reflect_traces.iter() {
//         div_of_trace(tr).write_html(&mut writer)
//       }
//       writeln!(writer, "</div>").unwrap();    
//       writeln!(writer, "</div>").unwrap();
//       write_cr(&mut writer);
//     }    
    
//     // - - - - - - - - - - - - - - -       
//     prev_sample = Some(sample) ; // Must be last!
//   }
//   writer.flush().unwrap();  
// }

pub fn style_string() -> &'static str {
"
<html>
<head>
<script src=\"https://ajax.googleapis.com/ajax/libs/jquery/3.1.1/jquery.min.js\"></script>

<style>
div { 
  display: inline
}
body {
  display: inline;
  color: #aa88cc;
  background: #552266;
  font-family: sans-serif;
  text-decoration: none;
  padding: 0px;
  margin: 0px;
}
body:visited {
  color: #aa88cc;
}
a {
  text-decoration: none;
}
a:hover {
  text-decoration: underline;
}
hr {
  display: block;
  float: left;
  clear: both;
  width: 0px;
  border: none;
}

.lab-name {
  color: #ccaadd;
  margin: 1px;
  padding: 1px;
}
.lab-name:visited {  
  color: #ccaadd;
}
.lab-name:hover {
  color: white;
}

.row {
  display: block;
}

.labsum-title {
  display: block;
  margin: 8px;
  font-size: 20px;
}
.labsum-row {
  display: block;
}
.labsum-name {
  display: table-cell;
  margin: 8px;
  padding: 2px;
  width: 70%;
}
.lab-details {
  display: table-cell;
  font-size: 14px;
  color: #ddbbee;
  border: solid white 1px;
  padding: 2px;
  background-color: #441155;
  margin: 3px;
}

.batch-name-lab {
  font-size: 0px;
  color: black;
}
.batch-name {
  color: black;
  font-size: 16px;
  border: solid;
  display: inline;
  padding: 3px;
  margin: 3px;
  float: left;
  background: #aa88aa;
  width: 32px;
}
.time-ns {
  font-size: 12px;
  display: inline;
}
.time-ms {
  font-size: 20px;
  display: inline;
}
.overhead {
  font-size: 30px;
  display: inline;
  color: #880000;
  background: #ffcccc;
  border: solid 1px red;
}
.speedup {
  font-size: 30px;
  display: inline;
  color: #008800;
  background: #ccffcc;
  border: solid 1px green;
}
.time-ms {
  font-size: 20px;
  display: inline;
}
.editor {
  color: black;
  font-size: 14px;
  border: solid;
  display: block;
  padding: 1px;
  margin: 1px;
  float: left;
  width: 10%;
  background: #aaaaaa;
}
.archivist {
  color: black;
  font-size: 14px;
  border: solid;
  display: block;
  padding: 1px;
  margin: 1px;
  float: left;
  width: 85%;
  background: #dddddd;
}
.traces {
  color: black;
  font-size: 8px;
  border: solid 0px;
  display: block;
  margin: 0px;
  float: left;
  width: 100%;
}
.traces:visited {
  color: black;
}

.input-value, 
.output-value,
.archivist-dcg-tree-post-edit,
.archivist-dcg-tree-post-update,
.traces-box,
.archivist-alloc-tree-post-edit,
.archivist-force-tree-post-edit, 
.archivist-alloc-tree-post-update, 
.archivist-force-tree-post-update  
{
  display: inline;
  float: left;

  padding: 0px;
  margin: 2px;

  color: #dd88ff;
  background: #331144;
  border-radius: 5px;
  border-style: solid;
  border-width: 0px;
  border-color: #dd88ff;
}

.input-value, 
.output-value {
  width: 49%;
}
.traces-box {
  width: 99%;
}
.archivist-dcg-tree-post-edit,
.archivist-dcg-tree-post-update {
  width: 49%;
}
.archivist-alloc-tree-post-edit,
.archivist-force-tree-post-edit, 
.archivist-alloc-tree-post-update, 
.archivist-force-tree-post-update {
  width: 24%;
}
.tool-label-toggles {
  display: block;
  float: right;
}


.trace, .force-tree, .alloc-tree, .dcg-alloc-edge, .dcg-force-edge {
  color: black;
  display: inline-block;
  border-style: solid;
  border-color: red;
  border-width: 1px;
  font-size: 0px;
  padding: 0px;
  margin: 1px;
  border-radius: 5px;
}

.dcg-force-edge {
  border-color: blue;
  border-width: 1px;
}
.dcg-node-comp {
  background: #ccccff;
  padding: 0px;
}
.dcg-node-ref {
  border-radius: 0px;
}
.dcg-alloc-edge {
  border-color: green;
  background: #ccffcc;
  border-width: 1px;
  padding: 3px;
}
.dirty {
  border-width: 2px;
  border-color: red;
  background: #ffcccc;
}
.editor-edge {
  border-width: 2px;
  border-color: black;
}

.tr-effect { 
  display: inline;
  display: none;
  font-size: 10px;
  background-color: white;
  border-radius: 2px;
}
.tr-symbols {  
  font-size: 10px;
  display: inline;
  display: none;
}

.path {  
  display: inline-block;
  display: none;

  margin: 0px;
  padding: 1px;
  border-radius: 1px;
  border-style: solid;
  border-width: 1px;
  border-color: #664466;
  background-color: #664466; 
}

.alloc-kind-thunk {
  border-color: green;
  border-radius:20px;
}
.alloc-kind-refcell {
  border-color: green;
  border-radius:0;
}
.tr-force-compcache-miss {  
  background: #ccccff;
  border-color: blue;
  padding: 0px;
}
.tr-force-compcache-hit {  
  background: #ccccff;
  border-color: blue;
  border-width: 4px;
  padding: 3px;
}
.tr-force-refget {  
  border-radius: 0;
  border-color: blue;
}
.tr-force-dup {  
  border-width: 0px;
  padding: 0px;
  background: #666666;
  display: none;
}
.tr-clean-rec {  
  background: #222244;
  border-color: #aaaaff;
  border-width: 1px; 
}
.tr-clean-eval {  
  background: #8888ff;
  border-color: white;
  border-width: 4px; 
}
.tr-clean-edge {  
  background: white;
  border-color: #aaaaff;
  border-width: 2px; 
  padding: 3px;
}
.tr-alloc-loc-fresh {  
  padding: 3px;
  background: #ccffcc;
}
.tr-alloc-loc-exists-same {  
  padding: 3px;
  background: #ccffcc;
  border-width: 4px;
  border-color: green;
}
.tr-alloc-loc-exists-diff {  
  padding: 3px;
  background: #ffcccc;
  border-width: 4px;
  border-color: red;
}
.tr-dirty {  
  background: #550000;
  border-color: #ffaaaa;
  border-width: 1px;
}
.tr-remove {  
  background: red;
  border-color: black;
  border-width: 2px;
  padding: 2px;
}

.force-tree {
  background: #ccccff;
  border-color: blue;
}
.alloc-tree {
  background: #ccffcc;
  border-color: green;
}

.no-extent {
  padding: 3px;
}
.page-title {
  display: block;
  font-size: 32px;
  color: #ccaadd;
  margin: 8px;
}

.val-name,
.val-constr,
.val-struct,
.val-tuple,
.val-vec,
.val-art
{
  display: inline-block;
  border-style: solid;
  border-width: 1px;
  border-color: #dd88ff;
  background-color: #220033;
  padding: 1px;
  margin: 1px;
  border-radius 2px;  
  font-size: 0px;  
}
.val-constr,
.val-struct,
.val-tuple,
.val-vec {
  border-color: #dd88ff;
  background-color: #773388;
}
.val-art
{
  padding: 2px;
}

.name {
  display: inline;
  display: none;

  font-size: 9px;
  color: black;
  background: white;
  border-style: solid;
  border-width: 1px;
  border-color: #664466; 
  border-radius: 2px;
  padding: 1px;
  margin: 1px;
}

.val-const
{
  display: inline-block;
  border-style: solid;
  border-color: black;
  border-width: 1px;
  color: black;
  background-color: grey;
  padding: 2px;
  margin: 1px;
  border-radius 5px;  
  font-size: 8px;  
}

</style>

<script>
function togglePaths() {
 var selection = document.getElementById(\"checkbox-1\");
 if (selection.checked) {
   $('.path').css('display', 'inline-block')
 } else {
   $('.path').css('display', 'none')
 }
}

function toggleNames() {
 var selection = document.getElementById(\"checkbox-2\");
 if (selection.checked) {
   $('.name').css('display', 'inline')
 } else {
   $('.name').css('display', 'none')
 }
}

function toggleEffects() {
 var selection = document.getElementById(\"checkbox-3\");
 if (selection.checked) {
   $('.tr-effect').css('display', 'inline')
 } else {
   $('.tr-effect').css('display', 'none')
 }
}

function toggleDupForces() {
 var selection = document.getElementById(\"checkbox-4\");
 if (selection.checked) {
   $('.tr-force-dup').css('display', 'inline')
 } else {
   $('.tr-force-dup').css('display', 'none')
 }
}
</script>
</head>

<body>

<fieldset class=\"tool-label-toggles\">
 <legend>Toggle labels: </legend>
 <label for=\"show-paths-checkbox\">paths</label>
 <input type=\"checkbox\" name=\"show-paths-checkbox\" id=\"checkbox-1\" onchange=\"togglePaths()\">
 <label for=\"show-names-checkbox\">names</label>
 <input type=\"checkbox\" name=\"show-names-checkbox\" id=\"checkbox-2\" onchange=\"toggleNames()\">
 <label for=\"show-effects-checkbox\">effects</label>
 <input type=\"checkbox\" name=\"show-effects-checkbox\" id=\"checkbox-3\" onchange=\"toggleEffects()\">
 <label for=\"show-effects-checkbox\">duplicate forces</label>
 <input type=\"checkbox\" name=\"show-effects-checkbox\" id=\"checkbox-4\" onchange=\"toggleDupForces()\">
</fieldset>
"
}
