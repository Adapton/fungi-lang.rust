/*! Serialization for external data structures contained in Fungi's bundle format. */

use std::rc::Rc;
use std::marker::PhantomData;

use adapton;
use adapton::engine;

use serde::Serialize;

// TODO: add custom handling for Rc<> to preserve references

// #[derive(Serialize)]
// #[serde(remote="adapton::reflect::trace::Trace")]
// pub struct TraceDef {
//     // #[serde(skip_serializing)] // temp
//     // pub effect: EffectDef,
//     // #[serde(skip_serializing)] // temp
//     // pub edge: EffectEdgeDef,
//     // #[serde(skip_serializing)] // temp
//     // pub extent: Box<Vec<TraceDef>>,
// }

// #[derive(Serialize)]
// #[serde(remote="adapton::reflect::trace::Effect")]
// pub struct EffectDef {
//     Force,
//     Alloc,
// }

// #[derive(Serialize)]
// #[serde(remote="adapton::reflect::trace::EffectEdge")]
// pub enum EffectEdgeDef {
//     Fwd(EdgeDef),
//     Bwd(EdgeDef),
//     None,
// }

// #[derive(Serialize)]
// #[serde(remote="adapton::reflect::trace::Edge")]
// pub struct EdgeDef {
//     // #[serde(skip_serializing)] // temp
//     // pub loc: Option<LocDef>,
//     // #[serde(skip_serializing)] // temp
//     // pub succ: SuccDef,
// }

// #[derive(Serialize)]
// // #[serde(remote="adapton::engine::Art")]
// pub struct ArtDef {
//     // pub art: EnumArtDef<T>,
// }

// use adapton::engine::Art;
// impl<T> From<Art<T>> for ArtDef {
//     fn from(art: Art<T>) -> ArtDef {
//         ArtDef {}
//     }
// }

// #[derive(Serialize)]
// // #[serde(remote="adapton::engine::EnumArt")]
// pub enum EnumArtDef<T> {
//     Rc(Rc<T>),
//     // Loc(Rc<LocDef>),
//     // Force(Rc<ForceDef<T>>),
// }