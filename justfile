set windows-shell := ["cmd.exe", "/c"]

kernel_target := if arch() == "x86_64" { "kernel/x86_64-kernel.json" } else if arch() == "aarch64" { "kernel/aarch64-kernel.json" } else { error("unsupported architecture") }
kernel_out := if arch() == "x86_64" { "target/x86_64-kernel/debug/kernel" } else if arch() == "aarch64" { "target/aarch64-kernel/debug/kernel" } else { "" }

bootloader_target := if arch() == "x86_64" { "x86_64-unknown-uefi" } else if arch() == "aarch64" { "aarch64-unknown-uefi" } else { error("unsupported architecture") }

qemu := if arch() == "x86_64" { "qemu-system-x86_64" } else if arch() == "aarch64" { "qemu-system-aarch64 -machine virt -cpu cortex-a72" } else { error("unsupported architecture") }

boot_efi := if arch() == "x86_64" { "BOOTX64.EFI" } else if arch() == "aarch64" { "BOOTAA64.EFI" } else { "" }

ovmf := if os() == "windows" {
    if arch() == "x86_64" { "RELEASEX64_OVMF.fd" } else { "RELEASEAARCH64_QEMU_EFI.fd" }
} else if arch() == "x86_64" {
    "/usr/share/OVMF/OVMF_CODE.fd"
} else if arch() == "aarch64" {
    "/usr/share/AAVMF/AAVMF_CODE.fd"
} else {
    error("unsupported platform")
}

[unix]
build:
    cargo build -p bootloader --target {{ bootloader_target }}
    cargo build -p kernel --target {{ kernel_target }} -Zbuild-std=core,alloc -Zbuild-std-features=compiler-builtins-mem
    mkdir -p esp/EFI/BOOT
    cp -f target/{{ bootloader_target }}/debug/bootloader.efi esp/EFI/BOOT/{{ boot_efi }}
    rust-objcopy -O binary {{ kernel_out }} esp/kernel.bin

[windows]
build:
    cargo build -p bootloader --target {{ bootloader_target }}
    cargo build -p kernel --target {{ kernel_target }} -Zbuild-std=core,alloc -Zbuild-std-features=compiler-builtins-mem
    if not exist esp\EFI\BOOT mkdir esp\EFI\BOOT
    copy /Y target\{{ bootloader_target }}\debug\bootloader.efi esp\EFI\BOOT\{{ boot_efi }}
    rust-objcopy -O binary {{ replace(kernel_out, "/", "\\") }} esp\kernel.bin

qemu_extra := if arch() == "aarch64" { "-m 1024 -device ramfb" } else { "" }

run: build
    {{ qemu }} -bios {{ ovmf }} -drive format=raw,file=fat:rw:esp -serial stdio {{ qemu_extra }}
