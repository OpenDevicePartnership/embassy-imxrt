use std::env;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

fn main() {
    // Put `memory.x` in our output directory and ensure it's
    // on the linker search path.
    let out = &PathBuf::from(env::var_os("OUT_DIR").unwrap());
    File::create(out.join("memory.x"))
        .unwrap()
        .write_all(include_bytes!("memory.x"))
        .unwrap();
    println!("cargo:rustc-link-search={}", out.display());

    // By default, Cargo will re-run a build script whenever
    // any file in the project changes. By specifying `memory.x`
    // here, we ensure the build script is only re-run when
    // `memory.x` is changed.
    println!("cargo:rerun-if-changed=memory.x");

    let major = env!("CARGO_PKG_VERSION_MAJOR")
        .parse::<u8>()
        .expect("should have major version");

    let minor = env!("CARGO_PKG_VERSION_MINOR")
        .parse::<u8>()
        .expect("should have minor version");

    let inv_major = !major;
    let inv_minor = !minor;

    // Inject crate version into the .biv section.
    File::create(out.join("biv.rs"))
        .unwrap()
        .write_all(
            format!(
                r##"
#[link_section = ".biv"]
#[used]
static BOOT_IMAGE_VERSION: u32 = 0x{:02x}{:02x}{:02x}{:02x};
"##,
                inv_major, inv_minor, major, minor,
            )
            .as_bytes(),
        )
        .unwrap();
}
