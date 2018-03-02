# Bindings to BAP in Rust
## Installation
* Install `libbap` for your distribution (tested against 1.3 and 1.4)

  * For NixOS, just use the package provided in nixpkgs
  * For Debian/Ubuntu, install [these](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/bap_1.4.0.deb) [debs](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/libbap_1.4.0.deb) in [sequence](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/libbap-dev_1.4.0.deb)
  * For RHEL/Fedora, install [these](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/bap-1.4.0-2.x86_64.rpm) [rpms](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/libbap-1.4.0-2.x86_64.rpm) in [sequence](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0/libbap-dev-1.4.0-2.x86_64.rpm)
  * For other linux, you can try the [.tar.gz files](https://mirrors.aegis.cylab.cmu.edu/bap/1.4.0)
  * Otherwise, you're going to have to try to install from source, follow the [instructions](https://github.com/BinaryAnalysisPlatform/bap) to get BAP, then proceed to [bap-bindings](https://github.com/BinaryAnalysisPlatform/bap-bindings) to get libbap.

* `bap-rust` should now work as any other cargo package

## Caveats
* The API is unstable and incomplete
* Bugs will be fixed, but fixes are on a best effort basis.
* Due to interactions between OCaml, threads, and the outside world, all API calls must occur on a single thread. This is enforced by the API

## Feature Requests
* Exported functionality

  * If it's in `bap-bindings` but not here, file an issue here.
  * If it's in `bap` but not in `bap-bindings`, file an issue in `bap-bindings`.
  * If it's not in `bap`, file an issue there.

* High level representation requests can go here, but I'm unlikely to implement them myself unless I need them, so prepeare yourself to write a PR :)
