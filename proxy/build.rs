#[cfg(feature = "qubesdb")]
/// When building with the `qubesdb` feature, link against libqubesdb.
fn main() {
    use std::env;
    use std::path::PathBuf;
    // Tell cargo to look for shared libraries in the specified directory
    println!("cargo:rustc-link-search=/usr/lib");

    // Tell cargo to tell rustc to link the system libqubesdb.
    println!("cargo:rustc-link-lib=qubesdb");

    // The bindgen::Builder is the main entry point
    // to bindgen, and lets you build up options for
    // the resulting bindings.
    let bindings = bindgen::Builder::default()
        // The input header we would like to generate
        // bindings for.
        .header_contents("wrapper.h", "#include <qubesdb-client.h>")
        // Tell cargo to invalidate the built crate whenever any of the
        // included header files changed.
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}

#[cfg(not(feature = "qubesdb"))]
/// When building *without* the `qubesdb` feature, this build-script is a no-op.
fn main() {}
