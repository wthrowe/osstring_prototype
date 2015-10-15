#![crate_name = "osstring_prototype"]
#![crate_type = "rlib"]

#![feature(ascii)]
#![feature(box_syntax)]
#![feature(char_from_unchecked)]
#![feature(char_internals)]
#![feature(core)]
#![feature(decode_utf16)]
#![feature(iter_arith)]
#![feature(no_std)]
#![feature(pattern)]
#![feature(slice_bytes)]
#![feature(slice_patterns)]
#![feature(str_internals)]
#![feature(unboxed_closures)]
#![feature(utf8_error)]
#![feature(vec_push_all)]

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
pub use std_integration::{OsStrPrototyping, OsStringPrototyping};

pub mod prelude {
    pub use super::{OsStrPrototyping, OsStringPrototyping};
    pub use super::slice_concat_ext::LocalSliceConcatExt;
}
