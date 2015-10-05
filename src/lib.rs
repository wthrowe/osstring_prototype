#![crate_name = "osstring_prototype"]
#![crate_type = "rlib"]

#![feature(ascii)]
#![feature(char_from_unchecked)]
#![feature(char_internals)]
#![feature(decode_utf16)]
#![feature(no_std)]
#![feature(slice_bytes)]
#![feature(slice_patterns)]
#![feature(str_internals)]
#![feature(utf8_error)]
#![feature(vec_push_all)]

// This somewhat silly looking sequence is avoid the automatic prelude
// import so that code behaves more like it does in libstd itself.
#![no_std]
#[macro_use]
extern crate std;

mod sys_common;

pub mod std_integration;
pub mod os_str;
pub mod unix;
pub mod windows;
mod wtf8;

pub use os_str::{OsStr, OsString};
pub use std_integration::{OsStrPrototyping, OsStringPrototyping};

pub mod prelude {
    pub use super::{OsStrPrototyping, OsStringPrototyping};
}
