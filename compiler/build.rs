fn main() {
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() == "windows" {
        println!("cargo:rustc-link-arg=/ENTRY:_start");
        println!("cargo:rustc-link-arg=/SUBSYSTEM:CONSOLE");
        println!("cargo:rustc-link-lib=kernel32");
    }
}
