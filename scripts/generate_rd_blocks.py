#!/usr/bin/env python3
"""Generate elaborating Lean RD summaries for EVM basic blocks.

Each output is ordinary Lean source: every summary starts from an ``RD`` cursor
and stacks the framework's opcode lemmas.  ``--shard-size`` spreads summaries
across independently importable files. Deterministic blocks expose exact final
step/gas counters and also get a packed sibling summary whose final step/gas
counters and active-word count are existential. Blocks containing warm/cold
operations existentially package the counters and keep stepping through the
remainder of the block.  Semantic side
conditions required by an opcode are lifted to hypotheses of the whole block
summary, so they do not interrupt symbolic execution.  Unsupported instructions
become explicit boundaries, with independently quantified summaries generated for
every maximal supported segment on either side.

Example:
  scripts/generate_rd_blocks.py contract.hex --name runtime \
    --code-term My.bytecode --bytecode-import My.Bytecode --output RuntimeBlocks.lean
  This also writes a compact theorem index to RuntimeBlocks.index by default.

For creation bytecode, ``--creation-code`` treats ``--code-term`` as the fixed
compiler-produced prefix.  Every summary quantifies an arbitrary ``tail`` and
runs over ``codeTerm ++ tail``; instruction decodes and jump destinations are
lifted from the fixed prefix.

For runtime immutables, pass an imported Lean layout with
``--layout-term MyContract.immutableLayout`` and ``--import MyContract.Immutables``.
The generator evaluates that layout's sites through Lean and checks that they
are complete PUSH20 or PUSH32 payloads in the template. Generated modules refer
to the imported layout and quantify a ``String → UInt256`` value map. PUSH20
sites use the word's low 20 bytes; PUSH32 sites use the whole word. This mode
does not model arbitrary byte patches within the instruction stream.
``--runtime-suffix`` is a separate mode that quantifies arbitrary bytes appended
to the template, as in Vyper's immutable scheme. Its summaries execute
``template ++ suffix``. Only instructions entirely inside the fixed template
receive summaries; suffix bytes still affect CODECOPY and CODESIZE.
Build the imported Lean modules before running this mode.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from bytecode_io import parse_bytecode_text, read_bytecode


TERMINATORS = {0x00, 0x56, 0x57, 0xF3, 0xFD, 0xFE, 0xFF}
MAX_SUMMARY_INSTRUCTIONS = 64


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    name: str
    width: int = 0
    argument: int | None = None
    complete: bool = True

    @property
    def size(self) -> int:
        return self.width + 1


def push_const_zero(ins: Instruction) -> bool:
    return 0x60 <= ins.opcode <= 0x7F and ins.argument == 0


def zero_push(ins: Instruction) -> bool:
    return ins.opcode == 0x5F or push_const_zero(ins)


def match_return_data_copy_full(
    run: list[Instruction], start: int,
) -> bool:
    """Recognize a full copy whose zero offset and size discharge the bounds check."""
    if start < 0 or start + 4 > len(run):
        return False
    first, second, third, fourth = run[start:start + 4]
    return (first.opcode == 0x3D and fourth.opcode == 0x3E
            and zero_push(second) and (zero_push(third) or third.opcode == 0x80))


NAMES = {
    0x00: "stop", 0x01: "add", 0x02: "mul", 0x03: "sub", 0x04: "div", 0x06: "mod",
    0x0A: "exp", 0x10: "lt", 0x11: "gt", 0x12: "slt", 0x13: "sgt",
    0x14: "eq", 0x15: "iszero", 0x16: "and", 0x17: "or", 0x18: "xor",
    0x19: "not", 0x1B: "shl", 0x1C: "shr", 0x20: "keccak256",
    0x05: "sdiv", 0x30: "address", 0x33: "caller", 0x34: "callvalue", 0x35: "calldataload",
    0x36: "calldatasize", 0x37: "calldatacopy", 0x38: "codesize",
    0x39: "codecopy", 0x3B: "extcodesize", 0x3D: "returndatasize",
    0x3E: "returndatacopy", 0x42: "timestamp", 0x43: "number",
    0x44: "prevrandao", 0x45: "gaslimit", 0x46: "chainid", 0x49: "blobhash",
    0x50: "pop", 0x51: "mload", 0x52: "mstore", 0x53: "mstore8", 0x54: "sload",
    0x55: "sstore", 0x56: "jump", 0x57: "jumpi", 0x5A: "gas",
    0x5C: "tload", 0x5D: "tstore",
    0x5B: "jumpdest", 0x5F: "push0", 0xA1: "log1", 0xA2: "log2", 0xA3: "log3",
    0xA4: "log4", 0xF1: "call", 0xF3: "return", 0xFA: "staticcall",
    0xFD: "revert", 0xFE: "invalid", 0xFF: "selfdestruct",
}


def opcode_name(op: int) -> str:
    if 0x60 <= op <= 0x7F:
        return f"push{op - 0x5F}"
    if 0x80 <= op <= 0x8F:
        return f"dup{op - 0x7F}"
    if 0x90 <= op <= 0x9F:
        return f"swap{op - 0x8F}"
    return NAMES.get(op, f"unsupported_{op:02x}")


def lean_operation(ins: Instruction) -> str:
    """The Lean constructor for a supported decoded opcode."""
    if 0x60 <= ins.opcode <= 0x7F:
        return f".Push .PUSH{ins.width}"
    return f".{opcode_name(ins.opcode).upper()}"


def lean_decode_arg(ins: Instruction) -> str:
    """The decoded immediate, if any, for a complete supported instruction."""
    if 0x60 <= ins.opcode <= 0x7F:
        assert ins.argument is not None
        return f"some ({u256_nat(ins.argument)}, {ins.width})"
    return "none"


def validate_immutable_sites(raw: object, code: bytes) -> dict[int, tuple[int, str]]:
    """Validate complete PUSH20/PUSH32 payload sites and return widths and keys."""
    if not isinstance(raw, list):
        raise ValueError("Lean immutable layout must contain a sites list")
    starts = {ins.pc + 1: ins.width for ins in disassemble(code)
              if ins.opcode in (0x73, 0x7F) and ins.complete}
    sites: dict[int, tuple[int, str]] = {}
    for entry in raw:
        if not isinstance(entry, dict):
            raise ValueError("each immutable site must be an object")
        off, length, key = entry.get("offset"), entry.get("length"), entry.get("key")
        if type(off) is not int or not isinstance(key, str) or not key:
            raise ValueError("immutable sites require an integer offset and nonempty key")
        if type(length) is not int or length not in (20, 32):
            raise ValueError(f"immutable site {off} must have length 20 or 32")
        if off in sites or starts.get(off) != length:
            raise ValueError(f"immutable site {off} is repeated or is not a PUSH{length} payload")
        if any(not (off + length <= previous or previous + prev_width <= off)
               for previous, (prev_width, _) in sites.items()):
            raise ValueError(f"immutable site {off} overlaps another site")
        sites[off] = (length, key)
    return sites


def read_lean_layout(layout_term: str, imports: list[str], code: bytes) -> dict[int, tuple[int, str]]:
    """Evaluate one imported Lean Layout, then validate its sites against bytecode."""
    source = ["import Reasoning.Immutables", *(f"import {module}" for module in imports),
              "open Lean Reasoning.Immutables",
              "#eval show IO Unit from do",
              f"  let sites := ({layout_term} : Layout).sites.map fun (off, width, key) =>",
              '    Json.mkObj [("offset", toJson off), ("length", toJson width), ("key", toJson key)]',
              '  IO.println ("IMMUTABLE_LAYOUT_JSON=" ++ (toJson sites).compress)', ""]
    with tempfile.TemporaryDirectory(prefix="equivm-layout-") as directory:
        probe = Path(directory) / "ReadImmutableLayout.lean"
        probe.write_text("\n".join(source), encoding="utf-8")
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(probe)],
                cwd=Path(__file__).resolve().parent.parent,
                text=True, capture_output=True, check=False, timeout=120,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ValueError(f"could not evaluate Lean immutable layout: {error}") from error
    if result.returncode != 0:
        raise ValueError(f"could not evaluate Lean immutable layout:\n{result.stderr or result.stdout}")
    prefix = "IMMUTABLE_LAYOUT_JSON="
    lines = [line[len(prefix):] for line in result.stdout.splitlines()
             if line.startswith(prefix)]
    if len(lines) != 1:
        raise ValueError("Lean immutable layout evaluation produced no unique sites list")
    try:
        return validate_immutable_sites(json.loads(lines[0]), code)
    except json.JSONDecodeError as error:
        raise ValueError("Lean immutable layout evaluation produced invalid JSON") from error


def disassemble(code: bytes) -> list[Instruction]:
    out: list[Instruction] = []
    pc = 0
    while pc < len(code):
        op = code[pc]
        width = op - 0x5F if 0x60 <= op <= 0x7F else 0
        data = code[pc + 1:pc + 1 + width]
        complete = len(data) == width
        if not complete:
            data = data + bytes(width - len(data))
        out.append(Instruction(pc, op, opcode_name(op), width,
                               int.from_bytes(data, "big") if width else None, complete))
        pc += 1 + width
    return out


def blocks(instructions: list[Instruction]) -> list[list[Instruction]]:
    if not instructions:
        return []
    starts = {instructions[0].pc}
    for i, ins in enumerate(instructions):
        if ins.opcode == 0x5B:
            starts.add(ins.pc)
        if ins.opcode in TERMINATORS and i + 1 < len(instructions):
            starts.add(instructions[i + 1].pc)
    result: list[list[Instruction]] = []
    current: list[Instruction] = []
    for ins in instructions:
        if current and ins.pc in starts:
            result.append(current)
            current = []
        current.append(ins)
        if ins.opcode in TERMINATORS:
            result.append(current)
            current = []
    if current:
        result.append(current)
    return result


def strip_solidity_metadata(code: bytes) -> bytes:
    """Remove a standard length-suffixed solc CBOR metadata map for block discovery.

    The full byte array is still emitted/referenced in theorem statements and decode proofs.
    """
    if len(code) < 3:
        return code
    metadata_length = int.from_bytes(code[-2:], "big")
    start = len(code) - metadata_length - 2
    if start < 0 or start >= len(code) - 2:
        return code
    # CBOR major type 5 (map), including the indefinite-length map marker.
    if code[start] & 0xE0 != 0xA0:
        return code
    return code[:start]


def lean_ident(value: str) -> str:
    ident = re.sub(r"[^A-Za-z0-9_]", "_", value)
    if not ident or ident[0].isdigit():
        ident = "rd_" + ident
    return ident


def u256_nat(value: int) -> str:
    return f"(UInt256.ofNat {value})"


WORD32 = "(⟨32⟩ : UInt256)"
WORD1 = "(⟨1⟩ : UInt256)"
WORD0 = "(⟨0⟩ : UInt256)"


def is_static_word(term: str) -> bool:
    return re.fullmatch(r"\(UInt256\.ofNat [0-9]+\)", term) is not None


def stack_term(values: list[str]) -> str:
    return "R" if not values else "(" + " :: ".join(values + ["R"]) + ")"


@dataclass(frozen=True)
class LeanParam:
    name: str
    typ: str


def term_mentions_name(term: str, name: str) -> bool:
    return re.search(rf"(?<![\w']){re.escape(name)}(?![\w'])", term) is not None


def final_value_param_specs(summary: Summary, creation_code: bool,
                            immutable_code: bool = False,
                            runtime_suffix: bool = False) -> list[LeanParam]:
    specs: list[LeanParam] = []
    if creation_code:
        specs.append(LeanParam("tail", "ByteArray"))
    if immutable_code:
        specs.append(LeanParam("immWords", "String → UInt256"))
    if runtime_suffix:
        specs.append(LeanParam("suffix", "ByteArray"))
    specs.extend([
        LeanParam("ee", "ExecutionEnv"),
        LeanParam("g", "Sat256"),
        LeanParam("s0", "State"),
        LeanParam("mem", "ByteArray"),
        LeanParam("aw", "UInt256"),
        LeanParam("rdata", "ByteArray"),
        LeanParam("σ", "AccountMap"),
        LeanParam("k", "ℕ"),
        LeanParam("C", "ℕ"),
    ])
    specs.extend(LeanParam(name, "UInt256") for name in summary.stack_in)
    specs.append(LeanParam("R", "List UInt256"))
    specs.extend(LeanParam(name, "UInt256") for name in summary.existential_words)
    return specs


def final_value_deps(term: str, specs: list[LeanParam],
                     code_dep_names: tuple[str, ...] = ()) -> list[LeanParam]:
    return [spec for spec in specs
            if term_mentions_name(term, spec.name)
            or ("__CODE__" in term and spec.name in code_dep_names)]


def render_def_params(deps: list[LeanParam]) -> str:
    return "".join(f" {{{dep.name} : {dep.typ}}}" for dep in deps)


def render_def_app(name: str, deps: list[LeanParam]) -> str:
    if not deps:
        return name
    args = " ".join(f"({dep.name} := {dep.name})" for dep in deps)
    return f"({name} {args})"


@dataclass(frozen=True)
class FinalValueDefs:
    lines: list[str]
    stack: str
    memory: str


def render_final_value_defs(base_name: str, summary: Summary, effective_code_term: str,
                            creation_code: bool, immutable_code: bool = False,
                            runtime_suffix: bool = False) -> FinalValueDefs:
    specs = final_value_param_specs(summary, creation_code, immutable_code, runtime_suffix)
    stack_name = f"{base_name}_stack"
    memory_name = f"{base_name}_memory"
    raw_input_stack_body = stack_term(summary.stack_in)
    raw_stack_body = stack_term(summary.stack_out)
    raw_memory_body = summary.mem
    stack_body = raw_stack_body.replace("__CODE__", effective_code_term)
    memory_body = raw_memory_body.replace("__CODE__", effective_code_term)
    code_dep_names = (("tail",) if creation_code else
                      ("suffix",) if runtime_suffix else
                      ("immWords",) if immutable_code else ())
    stack_deps = final_value_deps(raw_stack_body, specs, code_dep_names)
    memory_deps = final_value_deps(raw_memory_body, specs, code_dep_names)

    lines: list[str] = []
    stack_ref = stack_body
    memory_ref = memory_body
    if raw_stack_body != raw_input_stack_body:
        lines.extend([
            f"/-- Final stack for bytecode block summary `{base_name}`. -/",
            f"def {stack_name}{render_def_params(stack_deps)} : List UInt256 :=",
            f"  {stack_body}",
        ])
        stack_ref = render_def_app(stack_name, stack_deps)
    if raw_memory_body != "mem":
        if lines:
            lines.append("")
        lines.extend([
            f"/-- Final memory for bytecode block summary `{base_name}`. -/",
            f"def {memory_name}{render_def_params(memory_deps)} : ByteArray :=",
            f"  {memory_body}",
        ])
        memory_ref = render_def_app(memory_name, memory_deps)
    return FinalValueDefs(
        lines,
        stack_ref,
        memory_ref,
    )


def summary_name(prefix: str, block: list[Instruction], branch: str | None) -> str:
    suffix = ""
    if branch == "taken":
        suffix = "_taken"
    elif branch == "fallthrough":
        suffix = "_fallthrough"
    return f"{prefix}_block_{block[0].pc}{suffix}"


@dataclass(frozen=True)
class GeneratedUnit:
    text: str
    theorem_names: tuple[str, ...] = ()
    pcs: tuple[int, ...] = ()


@dataclass(frozen=True)
class IndexEntry:
    theorem: str
    file: str
    start_line: int
    end_line: int
    pcs: tuple[int, ...]


Unit = str | GeneratedUnit


def unit_text(unit: Unit) -> str:
    return unit.text if isinstance(unit, GeneratedUnit) else unit


# (minimum stack depth before the opcode, pop count, push count)
def stack_shape(ins: Instruction) -> tuple[int, int, int]:
    op = ins.opcode
    if op in {0x00, 0x5B, 0xFE}:
        return (0, 0, 0)
    if op == 0x5F or 0x60 <= op <= 0x7F or op in {
        0x30, 0x33, 0x34, 0x36, 0x38, 0x3D, 0x42, 0x43, 0x44, 0x45, 0x46, 0x5A,
    }:
        return (0, 0, 1)
    if 0x80 <= op <= 0x8F:
        depth = op - 0x7F
        return (depth, 0, 1)
    if 0x90 <= op <= 0x9F:
        depth = op - 0x8F + 1
        return (depth, 0, 0)
    if op in {0x15, 0x19, 0x35, 0x3B, 0x51, 0x54, 0x5C}:
        return (1, 1, 1)
    if op in {0x50, 0x56}:
        return (1, 1, 0)
    if op in {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x0A, 0x10, 0x11, 0x12, 0x13,
              0x14, 0x16, 0x17, 0x18, 0x1B, 0x1C, 0x20}:
        return (2, 2, 1)
    if op in {0x52, 0x53, 0x55, 0x57, 0x5D, 0xF3, 0xFD}:
        return (2, 2, 0)
    if op in {0x37, 0x39, 0x3E}:
        return (3, 3, 0)
    if op == 0xA1:
        return (3, 3, 0)
    if op == 0xA2:
        return (4, 4, 0)
    if op == 0xA3:
        return (5, 5, 0)
    if op == 0xA4:
        return (6, 6, 0)
    raise ValueError(f"no RD stepper for opcode 0x{op:02x} ({ins.name}) at pc {ins.pc}")


def required_input_depth(block: list[Instruction]) -> int:
    height = 0
    required = 0
    for ins in block:
        need, pops, pushes = stack_shape(ins)
        required = max(required, need - height)
        height += pushes - pops
    return required


def instruction_is_supported(ins: Instruction) -> bool:
    """Whether ``simulate`` has an RD stepper for this instruction."""
    if not ins.complete:
        return False
    try:
        stack_shape(ins)
        return True
    except ValueError:
        return False


def supported_segments(block: list[Instruction]) -> list[list[Instruction] | Instruction]:
    """Split a basic block into supported runs and unsupported singleton boundaries."""
    result: list[list[Instruction] | Instruction] = []
    current: list[Instruction] = []
    for ins in block:
        if instruction_is_supported(ins):
            current.append(ins)
        else:
            if current:
                result.append(current)
                current = []
            result.append(ins)
    if current:
        result.append(current)
    return result


def bounded_supported_segments(
    block: list[Instruction], max_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
) -> list[list[Instruction] | Instruction]:
    """Split supported runs without cutting through a full return-data copy."""
    if max_instructions <= 0:
        raise ValueError("max summary instruction count must be positive")
    result: list[list[Instruction] | Instruction] = []
    for piece in supported_segments(block):
        if isinstance(piece, Instruction):
            result.append(piece)
            continue
        start = 0
        while start < len(piece):
            end = min(start + max_instructions, len(piece))
            if end < len(piece):
                crossing = [i for i in range(start, end)
                            if match_return_data_copy_full(piece, i)
                            and i + 4 > end]
                if crossing:
                    end = min(crossing)
            if end == start:
                end = start + 4 if match_return_data_copy_full(piece, start) else start + max_instructions
            result.append(piece[start:end])
            start = end
    return result


BINOPS = {
    0x01: lambda a, b: f"({a} + {b})",
    0x02: lambda a, b: f"(UInt256.mul {a} {b})",
    0x03: lambda a, b: f"(UInt256.sub {a} {b})",
    0x04: lambda a, b: f"(UInt256.div {a} {b})",
    0x05: lambda a, b: f"(UInt256.sdiv {a} {b})",
    0x06: lambda a, b: f"(UInt256.mod {a} {b})",
    0x0A: lambda a, b: f"(UInt256.exp {a} {b})",
    0x10: lambda a, b: f"(UInt256.lt {a} {b})",
    0x11: lambda a, b: f"(UInt256.gt {a} {b})",
    0x12: lambda a, b: f"(UInt256.slt {a} {b})",
    0x13: lambda a, b: f"(UInt256.sgt {a} {b})",
    0x14: lambda a, b: f"(UInt256.eq {a} {b})",
    0x16: lambda a, b: f"(UInt256.land {a} {b})",
    0x17: lambda a, b: f"(UInt256.lor {a} {b})",
    0x18: lambda a, b: f"(UInt256.xor {a} {b})",
    0x1B: lambda a, b: f"(UInt256.shiftLeft {b} {a})",
    0x1C: lambda a, b: f"(UInt256.shiftRight {b} {a})",
}


STATIC_COST = {
    0x00: 0, 0x01: 3, 0x02: 5, 0x03: 3, 0x04: 5, 0x05: 5, 0x06: 5, 0x10: 3, 0x11: 3,
    0x12: 3, 0x13: 3, 0x14: 3, 0x15: 3, 0x16: 3, 0x17: 3, 0x18: 3,
    0x19: 3, 0x1B: 3, 0x1C: 3, 0x30: 2, 0x33: 2, 0x34: 2, 0x35: 3,
    0x36: 2, 0x38: 2, 0x3D: 2, 0x42: 2, 0x43: 2, 0x44: 2, 0x45: 2,
    0x46: 2, 0x50: 2,
    0x56: 8, 0x57: 10, 0x5A: 2, 0x5B: 1, 0x5F: 2,
}


def block_cost(costs: Iterable[str | int]) -> str:
    numeric = 0
    symbolic: list[str] = []
    for cost in costs:
        if isinstance(cost, int):
            numeric += cost
        else:
            symbolic.append(cost)
    terms = ([str(numeric)] if numeric else []) + symbolic
    return "0" if not terms else " + ".join(f"({term})" for term in terms)


@dataclass
class Summary:
    stack_in: list[str]
    stack_out: list[str]
    mem: str
    aw: str
    world_map: str
    pc: str
    costs: list[str | int]
    proof: list[str]
    existential_counters: bool
    terminal: str | None
    extra_hypotheses: list[tuple[str, str]]
    branch: str | None
    max_stack_prefix: int
    existential_words: list[str]
    last_cursor: str


def simulate(block: list[Instruction], branch: str | None,
                      decode_proof: str = "(by native_decide)",
             creation_prefix: str | None = None,
             immutable_sites: dict[int, tuple[int, str]] | None = None,
             runtime_suffix: bool = False) -> Summary:
    depth = required_input_depth(block)
    initial = [f"x{i}" for i in range(depth)]
    stack = initial.copy()
    mem = "mem"
    aw = "aw"
    world_map = "σ"
    pc = u256_nat(block[0].pc)
    costs: list[str | int] = []
    proof: list[str] = []
    existential = False
    terminal: str | None = None
    extra_hypotheses: list[tuple[str, str]] = []
    rno = 0
    max_stack_prefix = len(stack)
    existential_words: list[str] = []
    steps_done = 0
    full_copy_pcs = {
        block[i + 3].pc for i in range(len(block) - 3)
        if match_return_data_copy_full(block, i)
    }

    def require(name: str, proposition: str) -> str:
        """Add an opcode side condition to the enclosing block theorem.

        A repeated named condition (currently ``hperm``) is shared by every
        instruction that needs it.  Per-instruction conditions use fresh names.
        Returning the name keeps the generated step invocation tied to the
        hypothesis introduced in the theorem statement.
        """
        existing = next((term for hyp, term in extra_hypotheses if hyp == name), None)
        if existing is not None:
            if existing != proposition:
                raise ValueError(f"conflicting block hypothesis {name}")
            return name
        extra_hypotheses.append((name, proposition))
        return name

    def next_r() -> tuple[str, str]:
        nonlocal rno
        before = f"r{rno}"
        rno += 1
        return before, f"r{rno}"

    def valid_jump(dest: str) -> str:
        """Return the proof term used by JUMP/JUMPI.

        Creation summaries ask callers for membership in the fixed prefix's
        jump table, then lift that fact to the actual prefix-plus-tail code.
        Runtime summaries retain their existing full-code hypothesis.
        """
        if creation_prefix is None:
            return require("hvalid", f"(D_J __CODE__ 0).contains {dest} = true")
        valid = require(
            "hvalid", f"(D_J {creation_prefix} 0).contains {dest} = true"
        )
        return (
            f"(j tail {dest} {valid})"
        )

    index = 0
    narrow_sites = immutable_sites is not None and any(
        width == 20 for width, _ in immutable_sites.values())
    while index < len(block):
        ins = block[index]
        op = ins.opcode
        before, after = next_r()
        decode = decode_proof
        if runtime_suffix:
            decode = (
                "(by append_decode(__TEMPLATE__, suffix, "
                f"(⟨{ins.pc}⟩ : UInt256), {lean_operation(ins)}, "
                f"{lean_decode_arg(ins)}))"
            )
        elif immutable_sites is not None:
            if ins.pc + 1 in immutable_sites:
                decode = (
                    "(by\n"
                    f"    conv_lhs => arg 2; change (⟨{ins.pc}⟩ : UInt256)\n"
                    f"    exact immutableDecode_{ins.pc} immWords)"
                )
            else:
                decode = (
                    f"(by {'immutable_decode_n' if narrow_sites else 'immutable_decode'}(__LAYOUT__, __TEMPLATE__, immWords, "
                    f"(⟨{ins.pc}⟩ : UInt256), UInt8.ofNat {ins.opcode}, "
                    f"{lean_operation(ins)}, {lean_decode_arg(ins)}, "
                    "immutableLayout_inBounds, immutableTemplate_size64))"
                )
        ov = "(by evm_ov)"
        step_pc = ins.size

        if op == 0x5F:
            stack.insert(0, WORD0)
            proof.append(f"  have {after} := {before}.push0 {decode} {ov}")
        elif 0x60 <= op <= 0x7F:
            assert ins.argument is not None
            value = (f"(immWords {json.dumps(immutable_sites[ins.pc + 1][1])})"
                     if immutable_sites is not None and ins.pc + 1 in immutable_sites
                     else u256_nat(ins.argument))
            if narrow_sites and immutable_sites is not None \
                    and ins.pc + 1 in immutable_sites:
                value = f"(Layout.siteWord {ins.width} {value})"
            stack.insert(0, value)
            if ins.width in {1, 2, 4, 20}:
                call = f"{before}.push{ins.width} {value} {decode} {ov}"
            else:
                call = (
                    f"{before}.pushConst {value} (width := {ins.width}) "
                    f"(op := .PUSH{ins.width}) (by decide) {decode} {ov}"
                )
            proof.append(f"  have {after} := {call}")
        elif 0x80 <= op <= 0x8F:
            n = op - 0x7F
            stack.insert(0, stack[n - 1])
            call = f"{before}.dup{n}"
            proof.append(f"  have {after} := {call} {decode} {ov}")
        elif 0x90 <= op <= 0x9F:
            n = op - 0x8F
            stack[0], stack[n] = stack[n], stack[0]
            call = f"{before}.swap{n}"
            proof.append(f"  have {after} := {call} {decode} {ov}")
        elif op in BINOPS:
            a, b = stack.pop(0), stack.pop(0)
            stack.insert(0, BINOPS[op](a, b))
            proof.append(f"  have {after} := {before}.{ins.name} {decode} {ov}")
        elif op == 0x15:
            a = stack.pop(0)
            stack.insert(0, f"(UInt256.isZero {a})")
            proof.append(f"  have {after} := {before}.iszero {decode} {ov}")
        elif op == 0x19:
            a = stack.pop(0)
            stack.insert(0, f"(UInt256.lnot {a})")
            proof.append(f"  have {after} := {before}.not {decode} {ov}")
        elif op == 0x50:
            stack.pop(0)
            proof.append(f"  have {after} := {before}.pop {decode} {ov}")
        elif op in {0x30, 0x33, 0x34, 0x36, 0x38, 0x3D, 0x42, 0x43, 0x44, 0x45, 0x46}:
            pushed = {
                0x30: "(UInt256.ofNat ee.codeOwner.val)",
                0x33: "(UInt256.ofNat ee.source.val)",
                0x34: "ee.weiValue",
                0x36: "(UInt256.ofNat ee.calldata.size)",
                0x38: "(UInt256.ofNat __CODE__.size)",
                0x3D: "(UInt256.ofNat rdata.size)",
                0x42: "(UInt256.ofNat ee.header.timestamp)",
                0x43: "(UInt256.ofNat ee.header.number)",
                0x44: "ee.header.prevRandao",
                0x45: "(UInt256.ofNat ee.header.gasLimit)",
                0x46: "(UInt256.ofNat Ethereum.chainId)",
            }[op]
            stack.insert(0, pushed)
            proof.append(f"  have {after} := {before}.{ins.name} {decode} {ov}")
        elif op == 0x35:
            a = stack.pop(0)
            stack.insert(0, f"(uInt256OfByteArray (ee.calldata.readBytes {a}.toNat 32))")
            proof.append(f"  have {after} := {before}.calldataload {decode} {ov}")
        elif op == 0x51:
            a = stack.pop(0)
            stack.insert(0, f"(memLoad {a} {mem})")
            costs.append(f"memExpansionCost {aw} {a} {WORD32}")
            aw = f"(M {aw} {a} {WORD32})"
            proof.append(f"  have {after} := RD.genMload {before} {decode} {ov}")
        elif op == 0x52:
            a, b = stack.pop(0), stack.pop(0)
            costs.append(f"memExpansionCost {aw} {a} {WORD32}")
            mem = f"({b}.toByteArray.write 0 {mem} {a}.toNat 32)"
            aw = f"(M {aw} {a} {WORD32})"
            proof.append(f"  have {after} := RD.genMstore {before} {decode} {ov}")
        elif op == 0x53:
            a, b = stack.pop(0), stack.pop(0)
            costs.append(f"memExpansionCost {aw} {a} {WORD1}")
            mem = f"((⟨#[UInt8.ofNat {b}.toNat]⟩ : ByteArray).write 0 {mem} {a}.toNat 1)"
            aw = f"(M {aw} {a} {WORD1})"
            proof.append(f"  have {after} := RD.genMstore8 {before} {decode} {ov}")
        elif op == 0x20:
            a, b = stack.pop(0), stack.pop(0)
            stack.insert(0, f"(keccakWord {a} {b} {mem})")
            costs.append(f"memExpansionCost {aw} {a} {b}")
            costs.append(
                f"30 + 6 * (({b}.toNat + 31) / 32)"
            )
            aw = f"(M {aw} {a} {b})"
            proof.append(f"  have {after} := RD.genKeccak256 {before} {decode} {ov}")
        elif op in {0x37, 0x39}:
            a, b, c = stack.pop(0), stack.pop(0), stack.pop(0)
            source = "ee.calldata" if op == 0x37 else "__CODE__"
            mem = f"({source}.write {b}.toNat {mem} {a}.toNat {c}.toNat)"
            costs.append(f"memExpansionCost {aw} {a} {c}")
            costs.append(f"3 + 3 * (({c}.toNat + 31) / 32)")
            aw = f"(M {aw} {a} {c})"
            theorem = "RD.genCalldatacopy" if op == 0x37 else "RD.genCodecopy"
            proof.append(f"  have {after} := {theorem} {before} {decode} {ov}")
        elif op == 0x3E:
            a, b, c = stack.pop(0), stack.pop(0), stack.pop(0)
            mem = f"(rdata.write {b}.toNat {mem} {a}.toNat {c}.toNat)"
            costs.append(f"memExpansionCost {aw} {a} {c}")
            costs.append(f"3 + 3 * (({c}.toNat + 31) / 32)")
            aw = f"(M {aw} {a} {c})"
            guard_name = (
                "(by\n"
                "    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide\n"
                "    simpa only [hz] using returnDataCopyFullGuard rdata)"
                if ins.pc in full_copy_pcs else require(
                    f"hguard{sum(name.startswith('hguard') for name, _ in extra_hypotheses)}",
                    f"{b}.toNat + {c}.toNat ≤ rdata.size",
                )
            )
            proof.append(
                f"  have {after} := RD.genReturndatacopy {before} {decode} {guard_name} {ov}"
            )
        elif op == 0x54:
            slot = stack.pop(0)
            stack.insert(0, f"({world_map}.get? ee.codeOwner |>.option {WORD0} (fun ac => ac.storage.getD {slot} {WORD0}))")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := RD.sload {before} {decode} {ov}")
            existential = True
        elif op == 0x55:
            slot, value = stack.pop(0), stack.pop(0)
            perm = require("hperm", "ee.perm = true")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := RD.sstore {before} {perm} {decode} {ov}")
            world_map = f"(sstoreAccountMap ee.codeOwner {world_map} {slot} {value})"
            existential = True
        elif op == 0x5C:
            slot = stack.pop(0)
            stack.insert(0, f"({world_map}.get? ee.codeOwner |>.option {WORD0} (fun ac => ac.tstorage.getD {slot} {WORD0}))")
            proof.append(f"  have {after} := {before}.tload {decode} {ov}")
        elif op == 0x5D:
            slot, value = stack.pop(0), stack.pop(0)
            perm = require("hperm", "ee.perm = true")
            world_map = f"(tstoreAccountMap ee.codeOwner {world_map} {slot} {value})"
            proof.append(f"  have {after} := {before}.tstore {perm} {decode} {ov}")
        elif op == 0x3B:
            target = stack.pop(0)
            stack.insert(0, f"(extCodeSizeWord {world_map} {target})")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := {before}.extcodesize {decode} {ov}")
            existential = True
        elif op == 0x5A:
            if existential:
                gas_word = f"gasWord{len(existential_words)}"
                existential_words.append(gas_word)
                stack.insert(0, gas_word)
                # Earlier warm/cold operations hide the current counter values
                # behind existential eliminations.  RD.gas still determines the
                # pushed word from that hidden C; leave the theorem's gas-word
                # witness for Lean to infer from the resulting cursor.
                proof.append(f"  have {after} := RD.genGas {before} {decode} {ov}")
            else:
                cumulative = block_cost(costs)
                stack.insert(0, f"((g.subNat (C + ({cumulative}) + 2)).toUInt256)")
                proof.append(
                    f"  have {after} := RD.genGas "
                    f"(RD.normalizeCounters (k' := k + {steps_done}) "
                    f"(C' := C + ({cumulative})) {before} (by omega) (by omega)) "
                    f"{decode} {ov}"
                )
        elif op == 0x5B:
            proof.append(f"  have {after} := {before}.jumpdest {decode} {ov}")
        elif op == 0x56:
            dest = stack.pop(0)
            valid = valid_jump(dest)
            proof.append(f"  have {after} := {before}.jump {decode} {valid} {ov}")
            pc = dest
        elif op == 0x57:
            dest, cond = stack.pop(0), stack.pop(0)
            if branch == "taken":
                cond_hyp = require("hcond", f"{cond} ≠ {u256_nat(0)}")
                valid = valid_jump(dest)
                proof.append(
                    f"  have {after} := {before}.jumpiT {decode} {cond_hyp} {valid} {ov}"
                )
                pc = dest
            elif branch == "fallthrough":
                cond_hyp = require("hcond", f"{cond} = {u256_nat(0)}")
                proof.append(f"  have {after} := {before}.jumpiNT {decode} {cond_hyp} {ov}")
            else:
                raise AssertionError("JUMPI requires a branch")
        elif op == 0x00:
            proof.append(f"  exact {before}.stop {decode} {ov}")
            terminal = "RDret __CODE__ g s0 " + world_map + " ByteArray.empty"
            break
        elif op == 0xFE:
            proof.append(f"  exact RD.invalid {before} {decode}")
            terminal = "RDinvalid __CODE__ g s0"
            break
        elif op in {0xF3, 0xFD}:
            off, length = stack.pop(0), stack.pop(0)
            if op == 0xF3:
                proof.append(f"  exact RD.genRet {before} {decode} {ov}")
                terminal = (
                    f"RDret __CODE__ g s0 {world_map} "
                    f"({mem}.readWithPadding {off}.toNat {length}.toNat)"
                )
            else:
                proof.append(f"  exact RD.genRev {before} {decode} {ov}")
                terminal = "RDrev __CODE__ g s0"
            break
        elif op in {0xA1, 0xA2, 0xA3, 0xA4}:
            count = {0xA1: 3, 0xA2: 4, 0xA3: 5, 0xA4: 6}[op]
            vals = [stack.pop(0) for _ in range(count)]
            off, length = vals[0], vals[1]
            perm = require("hperm", "ee.perm = true")
            costs.append(f"memExpansionCost {aw} {off} {length}")
            topics = count - 2
            costs.append(
                f"375 + 8 * {length}.toNat + {topics} * 375"
            )
            aw = f"(M {aw} {off} {length})"
            theorem = f"RD.gen{ins.name.capitalize()}"
            proof.append(f"  have {after} := {theorem} {before} {decode} {perm} {ov}")
        else:
            raise ValueError(f"no generator rule for {ins.name} at pc {ins.pc}")

        if op not in {0x0A, 0x20, 0x37, 0x39, 0x3B, 0x3E, 0x51, 0x52, 0x53, 0x54,
                      0x55, 0x5C, 0x5D, 0xA1, 0xA2, 0xA3, 0xA4, 0xF3, 0xFD}:
            costs.append(3 if 0x60 <= op <= 0x9F else STATIC_COST.get(op, 0))
        elif op == 0x0A:
            # The exponent is the second popped operand; the generated RD rule carries this term.
            costs.append("expGasCost " + b)
        elif op in {0x51, 0x52, 0x53}:
            costs.append(3)
        elif op == 0x5C:
            costs.append("Ctload")
        elif op == 0x5D:
            costs.append("Ctstore")

        if op not in {0x56} and not (op == 0x57 and branch == "taken"):
            # Every instruction in a discovered block has a concrete byte offset.  Keep
            # fallthrough cursors canonical instead of accumulating a large UInt256 sum.
            pc = u256_nat(ins.pc + step_pc)

        max_stack_prefix = max(max_stack_prefix, len(stack))
        index += 1
        steps_done += 1

    return Summary(initial, stack, mem, aw, world_map, pc, costs, proof, existential,
                   terminal, extra_hypotheses, branch, max_stack_prefix, existential_words,
                   f"r{rno}")


def render_summary(prefix: str, code_term: str, block: list[Instruction], summary: Summary,
                   creation_code: bool = False,
                   creation_code_size: int | None = None,
                   immutable_sites: dict[int, tuple[int, str]] | None = None,
                   layout_term: str | None = None,
                   runtime_suffix: bool = False) -> str:
    name = summary_name(prefix, block, summary.branch)
    xs = " ".join(summary.stack_in)
    xbinder = f" {{{xs} : UInt256}}" if xs else ""
    tail_param = "{tail : ByteArray} " if creation_code else ""
    immutable_param = ("{immWords : String → UInt256} "
                       if immutable_sites is not None else "")
    suffix_param = "{suffix : ByteArray} " if runtime_suffix else ""
    params = (
        f"{tail_param}{immutable_param}{suffix_param}{{ee : ExecutionEnv}} {{g : Sat256}} {{s0 : State}} {{mem : ByteArray}} "
        f"{{aw : UInt256}} {{rdata : ByteArray}} "
        f"{{σ : AccountMap}} "
        f"{{k C : ℕ}}{xbinder} {{R : List UInt256}}"
    )
    effective_code_term = (f"({code_term} ++ suffix)"
                           if runtime_suffix else
                           f"({layout_term}.{'runtimeN' if any(width == 20 for width, _ in immutable_sites.values()) else 'runtime'} {code_term} immWords)"
                           if immutable_sites is not None else
                           f"({code_term} ++ tail)" if creation_code else code_term)
    assumptions: list[str] = []
    if any(ins.opcode != 0xFE for ins in block):
        assumptions.append(f"(hstack : R.length + {summary.max_stack_prefix} ≤ 1024)")
    assumptions.extend(
        f"({name} : {term.replace('__CODE__', effective_code_term).replace('__TEMPLATE__', code_term)})"
        for name, term in summary.extra_hypotheses
    )

    input_rd = (
        f"RD {effective_code_term} ee g s0 {u256_nat(block[0].pc)} {stack_term(summary.stack_in)} "
        f"mem aw rdata σ k C"
    )
    assumptions.append(f"(h : {input_rd})")

    final_defs: FinalValueDefs | None = None
    if summary.terminal:
        result = summary.terminal
    else:
        final_defs = render_final_value_defs(name, summary, effective_code_term,
                                             creation_code, immutable_sites is not None,
                                             runtime_suffix)
        result_rd = (
            f"RD {effective_code_term} ee g s0 {summary.pc} {final_defs.stack} "
            f"{final_defs.memory} {summary.aw} rdata {summary.world_map}"
        )
        if summary.existential_counters:
            word_binders = "" if not summary.existential_words else (
                "(" + " ".join(summary.existential_words) + " : UInt256) "
            )
            result = f"∃ {word_binders}(k' C' : ℕ), {result_rd} k' C'"
        else:
            result = (
                f"{result_rd} (k + {len(block)}) "
                f"(C + ({block_cost(summary.costs)}))"
            )
    result = result.replace("__CODE__", effective_code_term)

    lines = []
    if final_defs is not None:
        lines.extend(final_defs.lines)
        if final_defs.lines:
            lines.append("")
    lines.extend([
        f"/-- Automatically generated RD summary for bytecode block at pc {block[0].pc}. -/",
        f"theorem {name} {params}",
    ])
    lines.extend(f"    {a}" for a in assumptions)
    lines.append(f"    : {result} := by")
    lines.append("  let r0 := h")
    if creation_code:
        if creation_code_size is None:
            raise ValueError("creation code size is required in creation mode")
        lines.append(
            f"  have hcreationCodeSize : {code_term}.size = {creation_code_size} := "
            "by native_decide"
        )
    lines.extend(step.replace("__TEMPLATE__", code_term).replace("__LAYOUT__", layout_term or "")
                 for step in summary.proof)
    if not summary.terminal:
        last = summary.last_cursor
        if is_static_word(summary.pc):
            lines.append(
                f"  have rFinal := RD.normalizePC (pc' := {summary.pc}) "
                f"{last} (by native_decide)"
            )
            last = "rFinal"
        if summary.existential_counters:
            witnesses = ["_"] * len(summary.existential_words) + ["_", "_", last]
            lines.append(f"  exact ⟨{', '.join(witnesses)}⟩")
        else:
            lines.append(f"  exact RD.normalizeCounters {last} (by omega) (by omega)")
    if not summary.terminal:
        lines.append("")
        lines.extend(
            render_packed_summary(name, params, assumptions, effective_code_term, summary,
                                  final_defs)
        )
    return "\n".join(lines)


def render_packed_summary(base_name: str, params: str, assumptions: list[str],
                          effective_code_term: str, summary: Summary,
                          final_defs: FinalValueDefs) -> list[str]:
    packed_name = f"{base_name}_packed"
    result_rd = (
        f"RD {effective_code_term} ee g s0 {summary.pc} {final_defs.stack} "
        f"{final_defs.memory} aw' rdata {summary.world_map}"
    )
    word_binders = "" if not summary.existential_words else (
        "(" + " ".join(summary.existential_words) + " : UInt256) "
    )
    result = f"∃ {word_binders}(aw' : UInt256) (k' C' : ℕ), {result_rd} k' C'"
    result = result.replace("__CODE__", effective_code_term)
    call_args = []
    if any(a.startswith("(hstack :") for a in assumptions):
        call_args.append("hstack")
    call_args.extend(name for name, _ in summary.extra_hypotheses)
    call_args.append("h")
    theorem_call = f"{base_name} {' '.join(call_args)}"

    lines = [
        f"/-- Packed RD summary for bytecode block with abstract final counters and active words. -/",
        f"theorem {packed_name} {params}",
    ]
    lines.extend(f"    {a}" for a in assumptions)
    lines.append(f"    : {result} := by")
    if summary.existential_counters:
        unpacked_witnesses = summary.existential_words + ["k0", "C0", "h0"]
        lines.append(f"  obtain ⟨{', '.join(unpacked_witnesses)}⟩ := {theorem_call}")
        lines.append("  obtain ⟨k', C', h'⟩ := RD.pack h0")
        packed_witnesses = summary.existential_words + ["_", "k'", "C'", "h'"]
        lines.append(f"  exact ⟨{', '.join(packed_witnesses)}⟩")
    else:
        lines.append(f"  obtain ⟨k', C', h'⟩ := RD.pack ({theorem_call})")
        lines.append("  exact ⟨_, k', C', h'⟩")
    return lines


def unsupported_boundary_comment(ins: Instruction, code_size: int) -> str:
    successor = ins.pc + ins.size
    resume = (
        f" Summaries resume at pc {successor} from a fresh symbolic RD state."
        if successor < code_size and ins.opcode not in TERMINATORS else ""
    )
    return (
        f"/- Unsupported instruction boundary at pc {ins.pc}: {ins.name} "
        f"(0x{ins.opcode:02x}). No RD transition is asserted.{resume} -/"
    )


def generate_unit_records(code: bytes, prefix: str, code_term: str,
                          fail_on_unsupported: bool = False, keep_metadata: bool = False,
                          max_summary_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
                          creation_code: bool = False,
                          immutable_sites: dict[int, tuple[int, str]] | None = None,
                          layout_term: str | None = None,
                          runtime_suffix: bool = False) -> list[GeneratedUnit]:
    """Generate theorem/comment units with index metadata and no module wrapper."""
    if runtime_suffix and (creation_code or immutable_sites is not None or layout_term is not None):
        raise ValueError("runtime suffix and other patch modes are separate")
    if immutable_sites is not None and not layout_term:
        raise ValueError("immutable mode requires an imported Lean layout term")
    prefix = lean_ident(prefix)
    analyzed_code = code if keep_metadata else strip_solidity_metadata(code)
    discovered_blocks = blocks(disassemble(analyzed_code))
    unsupported = [
        ins for block in discovered_blocks for ins in block if not instruction_is_supported(ins)
    ]
    if fail_on_unsupported and unsupported:
        listing = ", ".join(
            f"pc {ins.pc}: {ins.name} (0x{ins.opcode:02x})" for ins in unsupported
        )
        raise ValueError(f"unsupported instructions: {listing}")

    units: list[GeneratedUnit] = []
    for block in discovered_blocks:
        for piece in bounded_supported_segments(
            block, max_summary_instructions
        ):
            if isinstance(piece, Instruction):
                units.append(GeneratedUnit(unsupported_boundary_comment(piece, len(analyzed_code))))
                continue
            branches: list[str | None] = (
                ["taken", "fallthrough"] if piece[-1].opcode == 0x57 else [None]
            )
            pcs = tuple(ins.pc for ins in piece)
            for branch in branches:
                decode_proof = "(by native_decide)"
                creation_prefix = None
                if creation_code:
                    creation_prefix = code_term
                    decode_proof = (
                        "(by exact d tail _ _ _ (by native_decide) "
                        "(by rw [hcreationCodeSize]; native_decide) (by native_decide))"
                    )
                summary = simulate(piece, branch,
                                   decode_proof, creation_prefix, immutable_sites,
                                   runtime_suffix)
                name = summary_name(prefix, piece, branch)
                theorem_names = (name,) if summary.terminal else (name, f"{name}_packed")
                units.append(GeneratedUnit(
                    render_summary(prefix, code_term, piece, summary, creation_code,
                                   len(code) if creation_code else None, immutable_sites,
                                   layout_term, runtime_suffix),
                    theorem_names,
                    pcs,
                ))
    return units


def generate_units(code: bytes, prefix: str, code_term: str,
                   fail_on_unsupported: bool = False, keep_metadata: bool = False,
                   max_summary_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
                   creation_code: bool = False,
                   immutable_sites: dict[int, tuple[int, str]] | None = None,
                   layout_term: str | None = None,
                   runtime_suffix: bool = False) -> list[str]:
    """Generate theorem/comment units without a Lean module wrapper."""
    return [
        unit.text for unit in generate_unit_records(
            code, prefix, code_term, fail_on_unsupported, keep_metadata,
            max_summary_instructions, creation_code, immutable_sites, layout_term,
            runtime_suffix
        )
    ]


def render_immutable_helpers(code: bytes, code_term: str, layout_term: str,
                             units: list[Unit], sites: dict[int, tuple[int, str]]) -> list[str]:
    """Emit local decode proofs for the instructions used by this module."""
    if any(width == 20 for width, _ in sites.values()):
        return render_immutable_helpers_n(code, code_term, layout_term, units, sites)
    used_pcs = {pc for unit in units if isinstance(unit, GeneratedUnit)
                for pc in unit.pcs if pc + 1 in sites}
    instructions = {ins.pc: ins for ins in disassemble(code)}
    site_entries = ", ".join(
        f"({off}, {width}, {json.dumps(key)})"
        for off, (width, key) in sites.items()
    )
    output = [
        "theorem immutableLayout_sites :",
        f"    {layout_term}.sites = [{site_entries}] := by native_decide",
        "",
        "theorem immutableLayout_inBounds :",
        f"    {layout_term}.inBounds {code_term} = true := by native_decide",
        "",
        "theorem immutableTemplate_size64 :",
        f"    {code_term}.size < 2 ^ 64 := by native_decide",
        "",
        "theorem immutableRuntime_size (immWords : String → UInt256) :",
        f"    ({layout_term}.runtime {code_term} immWords).size = {code_term}.size := by",
        "  exact Layout.runtime_size_of_bounds immutableLayout_inBounds",
        "",
    ]
    for pc in sorted(used_pcs):
        ins = instructions[pc]
        pc_term = f"(⟨{pc}⟩ : UInt256)"
        is_site = pc + 1 in sites
        if is_site:
            off = pc + 1
            width, key = sites[off]
            site_list = list(sites.items())
            index = next(i for i, (site_off, _) in enumerate(site_list) if site_off == off)
            def writes(entries: list[tuple[int, tuple[int, str]]]) -> str:
                return "[" + ", ".join(
                    f"({site_off}, immWords {json.dumps(site_key)})"
                    for site_off, (_, site_key) in entries
                ) + "]"
            before = writes(site_list[:index])
            after = writes(site_list[index + 1:])
            output += [
                f"theorem immutableDecode_{pc} (immWords : String → UInt256) :",
                f"    decode ({layout_term}.runtime {code_term} immWords) {pc_term} =",
                f"      some (.Push .PUSH{width}, some (immWords {json.dumps(key)}, {width})) := by",
                f"  exact Layout.decodeSite (pc := {pc_term}) (words := immWords)",
                f"    {off} {json.dumps(key)} {before} {after}",
                "    (by native_decide) (immutableRuntime_size immWords)",
                "    (by native_decide) (by native_decide)",
                "    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,",
                "      UInt256.toNat, UInt256.size]; try native_decide)",
                "    (by native_decide) (by rfl)",
                "    (by",
                "      rw [writeCascade_size]",
                "      · simp [writeCascadeSize]; try native_decide",
                "      · simp [WriteGapsOk]; try native_decide)",
                "    (by simp [WindowDisjointFromWrites]; try native_decide)",
                "",
            ]
    return output


def render_immutable_helpers_n(code: bytes, code_term: str, layout_term: str,
                               units: list[Unit],
                               sites: dict[int, tuple[int, str]]) -> list[str]:
    """Emit decode proofs for mixed PUSH20/PUSH32 layouts."""
    used_pcs = {pc for unit in units if isinstance(unit, GeneratedUnit)
                for pc in unit.pcs if pc + 1 in sites}
    entries = list(sites.items())

    def site_list(items: list[tuple[int, tuple[int, str]]]) -> str:
        return "[" + ", ".join(
            f"({off}, {width}, {json.dumps(key)})"
            for off, (width, key) in items
        ) + "]"

    output = [
        "theorem immutableLayout_sites :",
        f"    {layout_term}.sites = {site_list(entries)} := by native_decide",
        "",
        "theorem immutableLayout_inBounds :",
        f"    {layout_term}.inBoundsN {code_term} = true := by native_decide",
        "",
        "theorem immutableTemplate_size64 :",
        f"    {code_term}.size < 2 ^ 64 := by native_decide",
        "",
        "theorem immutableRuntime_size (immWords : String → UInt256) :",
        f"    ({layout_term}.runtimeN {code_term} immWords).size = {code_term}.size := by",
        "  exact Layout.runtimeN_size_of_bounds immutableLayout_inBounds",
        "",
    ]
    for pc in sorted(used_pcs):
        off = pc + 1
        width, key = sites[off]
        index = next(i for i, (site_off, _) in enumerate(entries) if site_off == off)
        before, after = entries[:index], entries[index + 1:]
        pc_term = f"(⟨{pc}⟩ : UInt256)"
        output += [
            f"theorem immutableDecode_{pc} (immWords : String → UInt256) :",
            f"    decode ({layout_term}.runtimeN {code_term} immWords) {pc_term} =",
            f"      some (.Push .PUSH{width}, some (Layout.siteWord {width} (immWords {json.dumps(key)}), {width})) := by",
            f"  exact Layout.decodeSite{width if width == 20 else '32N'}",
            f"    (pc := {pc_term}) (words := immWords) {off} {json.dumps(key)}",
            f"    {site_list(before)} {site_list(after)}",
            "    (by native_decide) immutableLayout_inBounds immutableTemplate_size64",
            "    (by native_decide) (by native_decide)",
            "    (by simpa [immutableLayout_sites]) (by native_decide)",
            "",
        ]
    return output


def render_module(prefix: str, imports: list[str], units: list[Unit],
                  creation_code: bool = False,
                  code_term: str | None = None,
                  immutable_sites: dict[int, tuple[int, str]] | None = None,
                  code: bytes | None = None,
                  layout_term: str | None = None,
                  runtime_suffix: bool = False) -> str:
    """Wrap generated units as an independently elaboratable Lean module."""
    prefix = lean_ident(prefix)
    output = ["import Reasoning.Reach"]
    if creation_code or runtime_suffix:
        output.append("import Reasoning.Initcode")
    if immutable_sites is not None:
        output.append("import Reasoning.Immutables")
    output.extend(f"import {module}" for module in imports)
    output += ["", "open Solm ABI Ethereum Ethereum.EVM",
               "open Reasoning.Theory Reasoning.Reach", "",
               f"namespace {prefix}Blocks", ""]
    if runtime_suffix:
        output += ["set_option maxRecDepth 10000", ""]
    if immutable_sites is not None:
        if code_term is None or code is None or not layout_term:
            raise ValueError("immutable mode requires template code and an imported Lean layout term")
        output += ["open Reasoning.Immutables", "set_option maxRecDepth 10000", ""]
        output += render_immutable_helpers(code, code_term, layout_term, units,
                                           immutable_sites)
    if creation_code:
        if code_term is None:
            raise ValueError("code term is required in creation mode")
        output += [
            f"private abbrev d := Reasoning.Theory.decode_append_left_of_decode {code_term}",
            f"private abbrev j := Reasoning.Theory.D_J_contains_append_left {code_term}",
            "",
        ]
    for unit in units:
        output += [unit_text(unit), ""]
    output += [f"end {prefix}Blocks", ""]
    return "\n".join(output)


def generate(code: bytes, prefix: str, code_term: str, imports: list[str],
             fail_on_unsupported: bool = False, keep_metadata: bool = False,
             max_summary_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
             creation_code: bool = False,
             immutable_sites: dict[int, tuple[int, str]] | None = None,
             layout_term: str | None = None,
             runtime_suffix: bool = False) -> str:
    """Generate a single Lean module. Use ``write_outputs`` for file sharding."""
    units = generate_unit_records(code, prefix, code_term, fail_on_unsupported,
                                  keep_metadata, max_summary_instructions,
                                  creation_code, immutable_sites, layout_term,
                                  runtime_suffix)
    return render_module(prefix, imports, units, creation_code, code_term,
                         immutable_sites, code, layout_term, runtime_suffix)


def top_level_item_start(line: str) -> bool:
    return (
        line.startswith("/--")
        or line.startswith("/- Unsupported")
        or line.startswith("def ")
        or line.startswith("noncomputable def ")
        or line.startswith("theorem ")
        or line.startswith("end ")
    )


def theorem_span(lines: list[str], theorem: str) -> tuple[int, int]:
    start = next(
        index for index, line in enumerate(lines)
        if re.match(rf"^theorem {re.escape(theorem)}\b", line)
    )
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if top_level_item_start(lines[index]):
            end = index
            break
    while end > start + 1 and lines[end - 1] == "":
        end -= 1
    return start + 1, end


def find_unit_start(lines: list[str], unit: Unit, cursor: int) -> tuple[int, int]:
    unit_lines = unit_text(unit).splitlines()
    first_line = unit_lines[0]
    start = next(index for index in range(cursor, len(lines)) if lines[index] == first_line)
    return start + 1, start + len(unit_lines)


def module_index_entries(file_name: str, module_text: str,
                         units: list[Unit]) -> list[IndexEntry]:
    lines = module_text.splitlines()
    entries: list[IndexEntry] = []
    cursor = 0
    for unit in units:
        unit_start, cursor = find_unit_start(lines, unit, cursor)
        if not isinstance(unit, GeneratedUnit):
            continue
        for theorem in unit.theorem_names:
            _, end = theorem_span(lines, theorem)
            entries.append(IndexEntry(theorem, file_name, unit_start, end, unit.pcs))
    return entries


def render_index(entries: list[IndexEntry]) -> str:
    return "\n".join(
        f"{entry.theorem}\t{entry.file}:{entry.start_line}-{entry.end_line}\t"
        f"{' '.join(str(pc) for pc in entry.pcs)}"
        for entry in entries
    ) + ("\n" if entries else "")


def default_index_output(output: Path) -> Path:
    return output.with_suffix(".index")


def shard_units(units: list[Unit], shard_size: int) -> list[list[Unit]]:
    """Group units with at most ``shard_size`` summary theorems per group."""
    if shard_size <= 0:
        raise ValueError("shard size must be positive")
    shards: list[list[Unit]] = []
    current: list[Unit] = []
    summaries = 0
    for unit in units:
        is_summary = "/-- Automatically generated RD summary" in unit_text(unit)
        if is_summary and summaries == shard_size:
            shards.append(current)
            current = []
            summaries = 0
        current.append(unit)
        summaries += int(is_summary)
    if current or not shards:
        shards.append(current)
    return shards


def write_outputs(output: Path, prefix: str, imports: list[str], units: list[Unit],
                  shard_size: int | None, creation_code: bool = False,
                  code_term: str | None = None,
                  index_output: Path | None = None,
                  immutable_sites: dict[int, tuple[int, str]] | None = None,
                  code: bytes | None = None,
                  layout_term: str | None = None,
                  runtime_suffix: bool = False) -> list[Path]:
    index_entries: list[IndexEntry] = []
    if shard_size is None:
        module_text = render_module(prefix, imports, units, creation_code,
                                    code_term, immutable_sites, code, layout_term,
                                    runtime_suffix)
        output.write_text(module_text, encoding="utf-8")
        index_entries.extend(module_index_entries(output.name, module_text, units))
        (index_output or default_index_output(output)).write_text(
            render_index(index_entries), encoding="utf-8"
        )
        return [output]

    shards = shard_units(units, shard_size)
    width = max(3, len(str(len(shards))))
    suffix = output.suffix or ".lean"
    paths: list[Path] = []
    for index, shard in enumerate(shards, 1):
        path = output.with_name(f"{output.stem}_{index:0{width}d}{suffix}")
        module_text = render_module(prefix, imports, shard, creation_code,
                                    code_term, immutable_sites, code, layout_term,
                                    runtime_suffix)
        path.write_text(module_text, encoding="utf-8")
        index_entries.extend(module_index_entries(path.name, module_text, shard))
        paths.append(path)
    (index_output or default_index_output(output)).write_text(
        render_index(index_entries), encoding="utf-8"
    )
    return paths


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("bytecode", nargs="?", type=Path,
                        help="raw binary, hex text, or solc JSON; use - for stdin")
    parser.add_argument("--hex", dest="hex_bytecode", help="bytecode as a hexadecimal string")
    parser.add_argument("--name", required=True, help="Lean-safe prefix for generated declarations")
    parser.add_argument("--code-term", required=True,
                        help="ByteArray term provided by the imported bytecode module")
    parser.add_argument("--bytecode-import", required=True,
                        help="Lean module containing --code-term")
    parser.add_argument("--import", dest="imports", action="append", default=[],
                        help="additional Lean module import")
    parser.add_argument("--output", "-o", type=Path, required=True,
                        help="output .lean file; its stem is used for sharded filenames")
    parser.add_argument("--index-output", type=Path,
                        help="sidecar theorem index path (default: OUTPUT with .index suffix)")
    parser.add_argument("--shard-size", type=int,
                        help="maximum summary theorems per output file")
    parser.add_argument("--fail-on-unsupported", action="store_true",
                        help="reject bytecode containing an instruction without a generator rule")
    parser.add_argument("--allow-unsupported", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--keep-metadata", action="store_true",
                        help="treat length-suffixed solc CBOR metadata bytes as executable code")
    parser.add_argument("--max-summary-instructions", type=int,
                        default=MAX_SUMMARY_INSTRUCTIONS,
                        help="split long supported runs after this many instructions (default: 64)")
    parser.add_argument("--creation-code", action="store_true",
                        help="quantify an arbitrary constructor-argument tail and summarize "
                             "--code-term ++ tail, lifting decodes and jumps from --code-term")
    parser.add_argument("--layout-term",
                        help="imported Lean Layout term for immutable-aware runtime summaries")
    parser.add_argument("--runtime-suffix", action="store_true",
                        help="summarize template ++ arbitrary appended runtime data")
    args = parser.parse_args(argv)
    if (args.bytecode is None) == (args.hex_bytecode is None):
        parser.error("provide exactly one of BYTECODE or --hex")
    if args.creation_code and (args.layout_term is not None or args.runtime_suffix):
        parser.error("--creation-code and runtime patch modes are separate")
    if args.runtime_suffix and args.layout_term is not None:
        parser.error("--runtime-suffix and --layout-term are separate modes")
    try:
        code = (parse_bytecode_text(args.hex_bytecode) if args.hex_bytecode is not None
                else read_bytecode(args.bytecode, args.code_term))
        imports = [args.bytecode_import, *args.imports]
        layout_term = args.layout_term
        immutable_sites = (read_lean_layout(layout_term, imports, code)
                           if layout_term is not None else None)
        units = generate_unit_records(code, args.name, args.code_term,
                                      args.fail_on_unsupported, args.keep_metadata,
                                      args.max_summary_instructions,
                                      args.creation_code, immutable_sites,
                                      layout_term, args.runtime_suffix)
        paths = write_outputs(args.output, args.name, imports, units,
                              args.shard_size, args.creation_code, args.code_term,
                              args.index_output, immutable_sites, code,
                              layout_term, args.runtime_suffix)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    if args.shard_size is not None:
        for path in paths:
            print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
