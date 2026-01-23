#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

use anyhow::{bail, Result};
use libc::free;
use std::ffi::{CStr, CString};
use std::ptr;

/// Read the named key from QubesDB and return its value if set; otherwise error out.
pub fn read(name: &str) -> Result<String> {
    let path = format!("/vm-config/{name}");

    let path_raw = CString::new(path.clone()).unwrap().into_raw();
    let mut len: u32 = 0;
    // SAFETY: path_raw is owned by Rust and passed as read-only to C, then retaken.
    // value_ptr must be freed with libc::free() after use.
    unsafe {
        let db = qdb_open(ptr::null_mut());
        if db.is_null() {
            let _ = CString::from_raw(path_raw); // retake ownership to avoid leak
            bail!("Failed to open QubesDB connection");
        }

        let value_ptr = qdb_read(db, path_raw, &mut len);
        let _ = CString::from_raw(path_raw); // retake ownership

        if len > 0 && !value_ptr.is_null() {
            let value_cstr = CStr::from_ptr(value_ptr);
            let value = value_cstr.to_owned().into_string()?;
            free(value_ptr.cast());
            qdb_close(db);
            Ok(value)
        } else {
            free(value_ptr.cast()); // This could be free(NULL), but that's safe
            qdb_close(db);
            bail!("Could not read from QubesDB: {}", path);
        }
    }
}
