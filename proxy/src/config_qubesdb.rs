#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

use anyhow::{bail, Result};
use std::ffi::{CStr, CString};
use std::ptr;

pub fn read(name: &str) -> Result<String> {
    let path = format!("/vm-config/{name}");

    let path_raw = CString::new(path.clone()).unwrap().into_raw();
    let mut len: u32 = 0;
    // SAFETY: path_raw will owned by the C caller and MUST be retaken.  When
    // len == 0, value_unsafe = NUL and MUST NOT be passed to CStr::from_ptr().
    let value_raw = unsafe {
        let db = qdb_open(ptr::null_mut());
        let value_unsafe = qdb_read(db, path_raw, &mut len);
        qdb_close(db);
        let _ = CString::from_raw(path_raw); // retake

        if len > 0 {
            CStr::from_ptr(value_unsafe)
        } else {
            bail!("Could not read from QubesDB: {}", path);
        }
    };

    let value = value_raw.to_owned().into_string()?;
    Ok(value)
}
