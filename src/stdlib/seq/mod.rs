
/// In this variation, sequences are parameterized by two name sets, X
/// and Y, but not by any types.  We assume the sequences consist of
/// natural numbers.  This version isn't particularly useful (unless
/// you _only_ care about sequences of natural numbers), but it is
/// instructive for writing and understanding the other versions.
pub mod seq_nat;

/// simple variation of seq_nat, using vectors of nats.
pub mod seq_vec_nat;

/// more abstract: the element type T is generic, but does not require
/// names for its representation or operations.  We can represent the
/// two versions above as instances of this more generic version.
pub mod seq_poly;

/// most abstract: the element type T is generic, and its
/// representation and operations use names.  To accomodate this, the
/// element type is parametric in the name and pointer indices of the
/// Seq type.  In essence, these indices store the disjoint union of
/// the names/pointers of the elements, and the sequence, in aggregate.
///
/// This representation, but the ones above, would suffice for storing
/// sequences of sequences, and other nested aggregates.
///
pub mod seq_poly_nms;
