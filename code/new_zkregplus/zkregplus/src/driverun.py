#!/usr/bin/env python3
"""
Run ./compile.sh twice, patching the two snark-cache flags inside
`fn small_data` in ./zkp_driver.rs between runs:

  pass 1: b_read_snark_cache=false, b_write_snark_cache=true  -> dump.txt
  pass 2: b_read_snark_cache=true,  b_write_snark_cache=false -> dump2.txt

Each pass waits for compile.sh to finish before continuing.
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DRIVER_RS = HERE / "zkp_driver.rs"
COMPILE_SH = HERE / "compile.sh"

READ_RE = re.compile(
    r"(get_global_config\(\)\.b_read_snark_cache\s*=\s*)"
    r"(?:true|false)(\s*;)"
)
WRITE_RE = re.compile(
    r"(get_global_config\(\)\.b_write_snark_cache\s*=\s*)"
    r"(?:true|false)(\s*;)"
)


def _rust_bool(b: bool) -> str:
    return "true" if b else "false"


def patch_small_data(read_val: bool, write_val: bool) -> None:
    """Replace the two snark-cache flags only inside fn small_data."""
    src = DRIVER_RS.read_text()

    start = src.find("fn small_data<F:PrimeField>")
    if start == -1:
        sys.exit("could not locate `fn small_data` in zkp_driver.rs")

    # end of small_data = start of the next sibling fn (tab-indented)
    end = src.find("\n\tfn ", start + 1)
    if end == -1:
        end = len(src)

    body = src[start:end]
    body, n_read = READ_RE.subn(
        rf"\g<1>{_rust_bool(read_val)}\g<2>", body, count=1
    )
    body, n_write = WRITE_RE.subn(
        rf"\g<1>{_rust_bool(write_val)}\g<2>", body, count=1
    )
    if n_read != 1 or n_write != 1:
        sys.exit(
            f"patch failed in small_data "
            f"(read={n_read}, write={n_write})"
        )

    DRIVER_RS.write_text(src[:start] + body + src[end:])
    print(
        f"[driverun] patched small_data: "
        f"b_read_snark_cache={_rust_bool(read_val)}, "
        f"b_write_snark_cache={_rust_bool(write_val)}"
    )


def run_compile(log_name: str) -> None:
    """Run ./compile.sh in the background, redirect to log_name, wait."""
    if not COMPILE_SH.exists():
        sys.exit(f"compile.sh not found at {COMPILE_SH}")

    cmd = f"./compile.sh > {log_name} 2>&1 & wait $!"
    print(f"[driverun] launching: {cmd}  (cwd={HERE})")
    rc = subprocess.call(["bash", "-c", cmd], cwd=str(HERE))
    print(f"[driverun] compile.sh finished (exit={rc}), log: {log_name}")
    if rc != 0:
        sys.exit(f"compile.sh exited with code {rc}; see {log_name}")


def main() -> None:
    patch_small_data(read_val=False, write_val=True)
    run_compile("dump.txt")

    patch_small_data(read_val=True, write_val=False)
    run_compile("dump2.txt")


if __name__ == "__main__":
    main()
