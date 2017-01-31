extern crate pkg_config;
extern crate bindgen;

use std::env;
use std::path::PathBuf;

fn main() {
    let lib_dir = env::var("BAP_LIB_DIR").ok();
    let include_dir = env::var("BAP_INCLUDE_DIR").ok();

    if lib_dir.is_none() && include_dir.is_none() {
        if let Ok(info) = pkg_config::find_library("bap") {
            // avoid empty include paths as they are not supported by GCC
            if info.include_paths.len() > 0 {
                let paths = env::join_paths(info.include_paths).unwrap();
                println!("cargo:include={}", paths.to_str().unwrap());
            }
            return;
        }
    }

    if let Some(lib_dir) = lib_dir {
        println!("cargo:rustc-link-search=native={}", lib_dir);
    }

    if let Some(include_dir) = include_dir {
        println!("cargo:include={}", include_dir);
    }

    // This line should not be necessary, but bindgen seems to be ignoring
    // .link()
    println!("cargo:rustc-link-lib=bap");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindgen::builder()
        .header("bap-sys.h")
        .link("bap")
        .no_unstable_rust()
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(out_path.join("bap.rs"))
        .expect("Unable to write bindings");
}
