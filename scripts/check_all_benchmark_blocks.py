#!/usr/bin/env python3
"""Generate and compile supported runtime block summaries under Benchmarks/.

The output and per-shard results live under /tmp/equivm-benchmark-blocks by
default. Successful shards are cached by source hash, so a failed run can resume.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from bytecode_io import read_bytecode


ROOT = Path(__file__).resolve().parent.parent
GENERATOR = ROOT / "scripts" / "generate_rd_blocks.py"


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def benchmark_inputs(path: Path) -> tuple[str, str, Path | None]:
    source = path.read_text(encoding="utf-8")
    names = re.findall(r"^def (\w+Bytecode)\s*:\s*ByteArray", source, re.MULTILINE)
    runtime = next(name for name in names if "Creation" not in name)
    namespace = re.search(r"^namespace ([\w.]+)", source, re.MULTILINE)
    code_term = f"{namespace.group(1)}.{runtime}" if namespace else runtime
    layout = path.with_name("Immutables.lean")
    return code_term, module_name(path), layout if layout.exists() else None


def run(args: list[str], *, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True,
                          timeout=timeout, check=False)


def compile_shard(path: Path) -> tuple[Path, bool, str]:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    marker = path.with_suffix(".ok")
    if marker.exists() and marker.read_text(encoding="utf-8") == digest:
        return path, True, "cached"
    try:
        result = run(["lake", "env", "lean", str(path)], timeout=900)
        log = result.stdout + result.stderr
        passed = result.returncode == 0
    except subprocess.TimeoutExpired as error:
        log = f"Lean timed out after {error.timeout} seconds\n"
        passed = False
    if passed:
        marker.write_text(digest, encoding="utf-8")
    else:
        path.with_suffix(".log").write_text(log, encoding="utf-8")
    return path, passed, log


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path("/tmp/equivm-benchmark-blocks"))
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--shard-size", type=int, default=20)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--only", help="limit to benchmark directory names containing this text")
    selection.add_argument("--contract", action="append", metavar="BENCHMARK",
                           help="exact directory below Benchmarks/ (may be repeated)")
    args = parser.parse_args()
    if args.jobs < 1 or args.shard_size < 1:
        parser.error("--jobs and --shard-size must be positive")

    paths = sorted((ROOT / "Benchmarks").rglob("Bytecode.lean"))
    if args.only:
        paths = [p for p in paths if args.only.lower() in str(p.parent).lower()]
    if args.contract:
        requested = set(args.contract)
        paths = [p for p in paths if
                 p.parent.relative_to(ROOT / "Benchmarks").as_posix() in requested]
        found = {p.parent.relative_to(ROOT / "Benchmarks").as_posix() for p in paths}
        if missing := requested - found:
            parser.error(f"unknown benchmark contract(s): {', '.join(sorted(missing))}")
    if not paths:
        parser.error("no matching benchmark bytecode files")

    build_targets = []
    for path in paths:
        _, bytecode_import, layout = benchmark_inputs(path)
        build_targets.append(bytecode_import)
        if layout:
            build_targets.append(module_name(layout))
    print(f"Building imports for {len(paths)} benchmark runtimes", flush=True)
    build = run(["lake", "build", *build_targets], timeout=3600)
    if build.returncode:
        sys.stderr.write(build.stdout + build.stderr)
        return 1

    shards: list[Path] = []
    for path in paths:
        code_term, bytecode_import, layout = benchmark_inputs(path)
        hex_path = path.with_name("runtime.hex")
        if read_bytecode(path, code_term) != read_bytecode(hex_path):
            raise ValueError(f"Lean bytecode differs from runtime.hex: {path}")
        destination = args.output_dir / path.parent.relative_to(ROOT / "Benchmarks")
        destination.mkdir(parents=True, exist_ok=True)
        output = destination / "Blocks.lean"
        command = [sys.executable, str(GENERATOR), str(hex_path),
                   "--name", "check" + path.parent.name,
                   "--code-term", code_term,
                   "--bytecode-import", bytecode_import,
                   "--shard-size", str(args.shard_size),
                   "--output", str(output)]
        if layout:
            # The declaration namespace in Immutables.lean can differ from its module path.
            layout_source = layout.read_text(encoding="utf-8")
            match = re.search(r"^namespace ([\w.]+)", layout_source, re.MULTILINE)
            assert match is not None
            command += ["--import", module_name(layout),
                        "--layout-term", f"{match.group(1)}.immutableLayout"]
        result = run(command, timeout=900)
        if result.returncode:
            sys.stderr.write(f"Generation failed for {path.parent}:\n"
                             + result.stdout + result.stderr)
            return 1
        generated = sorted(destination.glob("Blocks_*.lean"))
        if not generated:
            raise ValueError(f"generator produced no shards for {path.parent}")
        shards.extend(generated)
        print(f"Generated {path.parent.relative_to(ROOT)}: {len(generated)} shards", flush=True)

    print(f"Compiling {len(shards)} shards with {args.jobs} workers", flush=True)
    failures: list[Path] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(compile_shard, shard) for shard in shards]
        for index, future in enumerate(as_completed(futures), 1):
            path, passed, log = future.result()
            if not passed:
                failures.append(path)
                print(f"FAIL {path} (details in {path.with_suffix('.log')})", flush=True)
                lines = log.splitlines()
                print("\n".join(lines[:40]), file=sys.stderr, flush=True)
                if len(lines) > 40:
                    print(f"... {len(lines) - 40} more lines in {path.with_suffix('.log')}",
                          file=sys.stderr, flush=True)
            elif index % 20 == 0 or index == len(shards):
                print(f"Compiled {index}/{len(shards)} shards", flush=True)
    print(f"Result: {len(shards) - len(failures)}/{len(shards)} compiled", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
