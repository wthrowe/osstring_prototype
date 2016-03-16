#![crate_name = "osstring_prototype"]
#![crate_type = "rlib"]

#![feature(ascii)]
#![feature(box_syntax)]
#![feature(char_internals)]
#![feature(decode_utf16)]
#![feature(iter_arith)]
#![feature(pattern)]
#![feature(slice_patterns)]
#![feature(str_internals)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(copy_from_slice)]

#![cfg_attr(test, feature(osstring_simple_functions))]

// This somewhat silly looking sequence is avoid the automatic prelude
// import so that code behaves more like it does in libstd itself.
#![no_std]
#[macro_use]
extern crate std;

mod sys_common;

pub mod slice_concat_ext;
mod slice_searcher;
mod split_bytes;
pub mod std_integration;
mod str;
pub mod os_str;
pub mod unix;
mod utf8_sections;
pub mod windows;
mod wtf8;

pub use os_str::{OsStr, OsString};
pub use std_integration::{OsStrPrototyping, OsStringPrototyping, OsStrSection};

pub mod prelude {
    pub use super::OsStrSection;
    pub use super::{OsStrPrototyping, OsStringPrototyping};
    pub use super::slice_concat_ext::LocalSliceConcatExt;
}
