//! The bap crate acts as higher level bindings to the BAP `OCaml` library
//!
//! Due to limitations in BAP/OCaml, this library can currently only be
//! used from exactly one thread. For safety's sake, this is checked by
//! the library during creation of `basic::Bap` context objects, this
//! object is required for creation of fresh BAP objects, and none of
//! these are Send or Sync.
//!
//! tl;dr use exactly one thread to interact with this crate
//!
//! For more detailed documentation, see the
//! [BAP Documentation](http://binaryanalysisplatform.github.io/bap/api/v1.4.0/argot_index.html)
//! which this binds.
#![deny(missing_docs)]
extern crate bap_sys;
extern crate bit_vec;
#[macro_use]
extern crate enum_primitive;
#[cfg(feature = "holmes_support")]
#[macro_use]
extern crate holmes;
#[macro_use]
extern crate lazy_static;
extern crate mktemp;
extern crate num;
#[cfg(feature = "holmes_support")]
#[macro_use]
extern crate postgres;
#[cfg(feature = "json")]
extern crate rustc_serialize;

pub mod basic;
pub mod high;
#[cfg(feature = "holmes_support")]
pub mod holmes_support;
mod printers;
