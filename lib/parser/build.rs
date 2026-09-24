use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let ksy_dir = manifest_dir.join("ksy");
    let out_dir = manifest_dir.join("src/ksy");

    std::fs::create_dir_all(&out_dir).unwrap();

    let run_ksc = |ksy_file: &str| {
        let status = Command::new("kaitai-struct-compiler")
            .args([
                "--target",
                "rust",
                "--outdir",
                out_dir.to_str().unwrap(),
                "--import-path",
                ksy_dir.to_str().unwrap(),
                ksy_dir.join(ksy_file).to_str().unwrap(),
            ])
            .status()
            .expect("kaitai-struct-compiler not found in PATH");
        assert!(status.success(), "ksc failed on {ksy_file}");
    };

    run_ksc("vlq_base128_le.ksy");
    run_ksc("hermes_bytecode.ksy");

    // keep mod.rs stable — ksc doesn't generate it
    let mod_path = out_dir.join("mod.rs");
    if !mod_path.exists() {
        std::fs::write(mod_path, "pub mod vlq_base128_le;\npub mod hermes_bytecode;\n").unwrap();
    }

    println!("cargo:rerun-if-changed=../ksy/hermes_bytecode.ksy");
    println!("cargo:rerun-if-changed=../ksy/vlq_base128_le.ksy");
}
