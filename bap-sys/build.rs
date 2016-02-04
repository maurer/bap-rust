extern crate pkg_config;

use std::env;

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
}
