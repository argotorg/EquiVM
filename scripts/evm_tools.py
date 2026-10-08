#!/usr/bin/env python3
"""Bytecode facts shared by the scaffold builder and the bytecode report.

Everything here is a pure function of the compiled artifact: the JUMPDEST set as the EVM computes
it, solc source maps, the selector dispatcher as compiled, an opcode census, and the internal
routine boundaries the source map records.  Disassembly itself comes from ``generate_rd_blocks``.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from generate_rd_blocks import Instruction, blocks, disassemble, strip_solidity_metadata

PUSH1, PUSH32 = 0x60, 0x7F
JUMPDEST, JUMP, JUMPI = 0x5B, 0x56, 0x57
EQ, LT, GT = 0x14, 0x10, 0x11

CENSUS_OPCODES = {
    0x54: "SLOAD", 0x55: "SSTORE", 0x5C: "TLOAD", 0x5D: "TSTORE", 0x20: "KECCAK256",
    0x31: "BALANCE", 0x3B: "EXTCODESIZE", 0x3C: "EXTCODECOPY", 0x3F: "EXTCODEHASH",
    0x3D: "RETURNDATASIZE", 0x3E: "RETURNDATACOPY",
    0xA0: "LOG0", 0xA1: "LOG1", 0xA2: "LOG2", 0xA3: "LOG3", 0xA4: "LOG4",
    0xF0: "CREATE", 0xF1: "CALL", 0xF2: "CALLCODE", 0xF4: "DELEGATECALL", 0xF5: "CREATE2",
    0xFA: "STATICCALL", 0xFF: "SELFDESTRUCT", 0xFE: "INVALID", 0xFD: "REVERT",
    0xF3: "RETURN", 0x00: "STOP", 0x5A: "GAS", 0x42: "TIMESTAMP", 0x43: "NUMBER",
    0x46: "CHAINID", 0x47: "SELFBALANCE", 0x5E: "MCOPY", 0x0B: "SIGNEXTEND",
}


def is_push(op: int) -> bool:
    return PUSH1 <= op <= PUSH32 or op == 0x5F


def jump_dests(code: bytes) -> list[int]:
    """`D_J code 0`: every JUMPDEST byte that is not inside push data, scanning from pc 0."""
    out: list[int] = []
    pc = 0
    while pc < len(code):
        op = code[pc]
        if op == JUMPDEST:
            out.append(pc)
        if PUSH1 <= op <= PUSH32:
            pc += op - 0x5F
        pc += 1
    return out


def split_metadata(code: bytes) -> tuple[bytes, bytes]:
    """(executable prefix, trailing solc CBOR metadata); metadata is empty when absent."""
    body = strip_solidity_metadata(code)
    return body, code[len(body):]


# --------------------------------------------------------------------------------------------
# Source maps

@dataclass(frozen=True)
class SourceMapEntry:
    start: int
    length: int
    file: int
    jump: str
    modifier_depth: int


def decode_source_map(text: str) -> list[SourceMapEntry]:
    """Decode solc's compressed ``s:l:f:j:m`` source map (one entry per instruction)."""
    entries: list[SourceMapEntry] = []
    start = length = file = depth = 0
    jump = "-"
    for raw in text.split(";"):
        fields = raw.split(":")
        if len(fields) > 0 and fields[0] != "":
            start = int(fields[0])
        if len(fields) > 1 and fields[1] != "":
            length = int(fields[1])
        if len(fields) > 2 and fields[2] != "":
            file = int(fields[2])
        if len(fields) > 3 and fields[3] != "":
            jump = fields[3]
        if len(fields) > 4 and fields[4] != "":
            depth = int(fields[4])
        entries.append(SourceMapEntry(start, length, file, jump, depth))
    return entries


def parse_src(src: str) -> tuple[int, int, int]:
    """An AST ``src`` field ``start:length:file``."""
    start, length, file = (int(part) for part in src.split(":")[:3])
    return start, length, file


@dataclass
class AstFunction:
    name: str
    kind: str
    contract: str
    start: int
    length: int
    file: int
    selector: str | None = None
    visibility: str = ""

    @property
    def end(self) -> int:
        return self.start + self.length

    def contains(self, start: int, length: int) -> bool:
        return self.start <= start and start + length <= self.end

    @property
    def label(self) -> str:
        if self.kind in ("function", "getter", "modifier"):
            return f"{self.contract}.{self.name}"
        if self.kind == "helper":
            return self.name
        return f"{self.contract}.{self.kind}"


def walk(node: object):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def ast_functions(units: list[dict]) -> list[AstFunction]:
    """Every function, constructor, modifier, receive, and fallback definition of the ASTs."""
    out: list[AstFunction] = []
    for unit in units:
        for contract in (n for n in walk(unit) if n.get("nodeType") == "ContractDefinition"):
            for node in walk(contract.get("nodes", [])):
                kind = node.get("nodeType")
                if kind == "FunctionDefinition":
                    start, length, file = parse_src(node["src"])
                    out.append(AstFunction(node.get("name") or node.get("kind", "function"),
                                           node.get("kind", "function"), contract["name"],
                                           start, length, file, node.get("functionSelector"),
                                           node.get("visibility", "")))
                elif kind == "ModifierDefinition":
                    start, length, file = parse_src(node["src"])
                    out.append(AstFunction(node["name"], "modifier", contract["name"],
                                           start, length, file))
                elif kind == "VariableDeclaration" and node.get("functionSelector"):
                    start, length, file = parse_src(node["src"])
                    out.append(AstFunction(node["name"], "getter", contract["name"],
                                           start, length, file, node.get("functionSelector"),
                                           "public"))
    return out


def innermost_function(functions: list[AstFunction], entry: SourceMapEntry) -> AstFunction | None:
    best: AstFunction | None = None
    for fn in functions:
        if fn.file == entry.file and fn.contains(entry.start, entry.length):
            if best is None or fn.length < best.length:
                best = fn
    return best


# --------------------------------------------------------------------------------------------
# Dispatcher recovery

@dataclass(frozen=True)
class SelectorCompare:
    pc: int            # pc of the PUSH4
    selector: int
    kind: str          # "eq" | "gt" | "lt"
    target: int        # JUMPI destination
    jumpi_pc: int


@dataclass
class Dispatcher:
    callvalue_guard: bool
    calldatasize_check: tuple[int, int] | None   # (pc of JUMPI, short-calldata target)
    arms: list[SelectorCompare] = field(default_factory=list)
    pivots: list[SelectorCompare] = field(default_factory=list)
    fallthroughs: list[tuple[int, str]] = field(default_factory=list)


def selector_compares(instructions: list[Instruction]) -> list[SelectorCompare]:
    """``PUSH4 sel … EQ|GT|LT … PUSH t JUMPI`` sequences, the shape of every solc dispatcher."""
    out: list[SelectorCompare] = []
    for i, ins in enumerate(instructions):
        if ins.opcode != 0x63:
            continue
        window = instructions[i + 1:i + 4]
        compare = next(((j, w) for j, w in enumerate(window) if w.opcode in (EQ, GT, LT)), None)
        if compare is None:
            continue
        j, cmp_ins = compare
        after = instructions[i + 2 + j:i + 5 + j]
        push = next((w for w in after if is_push(w.opcode)), None)
        jumpi = next((w for w in after if w.opcode == JUMPI), None)
        if push is None or jumpi is None or push.pc > jumpi.pc or push.argument is None:
            continue
        kind = {EQ: "eq", GT: "gt", LT: "lt"}[cmp_ins.opcode]
        out.append(SelectorCompare(ins.pc, ins.argument or 0, kind, push.argument, jumpi.pc))
    return out


def dispatcher(instructions: list[Instruction]) -> Dispatcher:
    """Recover the compiled dispatcher: guard, size check, selector arms, pivots, fallthroughs."""
    compares = selector_compares(instructions)
    first_compare_pc = compares[0].pc if compares else len(instructions) and instructions[-1].pc
    prologue = [ins for ins in instructions if ins.pc < first_compare_pc]
    callvalue_guard = any(ins.opcode == 0x34 for ins in prologue)
    size_check = None
    for i, ins in enumerate(prologue):
        if ins.opcode == 0x36:  # CALLDATASIZE
            window = prologue[i + 1:i + 6]
            if any(w.opcode == LT for w in window):
                push = next((w for w in window if is_push(w.opcode) and w.argument is not None), None)
                jumpi = next((w for w in window if w.opcode == JUMPI), None)
                if push is not None and jumpi is not None:
                    size_check = (jumpi.pc, push.argument)
                    break
    arms = [c for c in compares if c.kind == "eq"]
    pivots = [c for c in compares if c.kind != "eq"]
    # What each compare chain falls through to: the next terminator after the last compare of a
    # maximal run of compares inside one basic block sequence.
    fallthroughs: list[tuple[int, str]] = []
    by_pc = {ins.pc: k for k, ins in enumerate(instructions)}
    for c in compares:
        k = by_pc[c.jumpi_pc] + 1
        if k < len(instructions) and instructions[k].opcode == 0x80 and k + 1 < len(instructions) \
                and instructions[k + 1].opcode == 0x63:
            continue  # next compare of the same chain
        if k < len(instructions) and instructions[k].opcode in (0x50, 0x80) and k + 1 < len(instructions) \
                and instructions[k + 1].opcode in (0x80, 0x63):
            continue
        tail = instructions[k:k + 6]
        desc = "?"
        for t in tail:
            if t.opcode == 0xFD:
                desc = "REVERT"
                break
            if t.opcode == JUMP:
                prev = instructions[by_pc[t.pc] - 1]
                desc = f"JUMP {prev.argument}" if is_push(prev.opcode) and prev.argument is not None else "JUMP ?"
                break
            if t.opcode == JUMPI or t.opcode == JUMPDEST:
                desc = f"falls into {t.pc}"
                break
        fallthroughs.append((c.jumpi_pc, desc))
    return Dispatcher(callvalue_guard, size_check, arms, pivots, fallthroughs)


# --------------------------------------------------------------------------------------------
# Census and routine boundaries

def census(instructions: list[Instruction]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for ins in instructions:
        name = CENSUS_OPCODES.get(ins.opcode)
        if name:
            counts[name] = counts.get(name, 0) + 1
    return counts


@dataclass
class RoutineCall:
    jump_pc: int
    callee: int | None     # the pushed target when the JUMP is preceded by a PUSH
    function: str | None   # the source function containing the call site


@dataclass
class RoutineInfo:
    calls: list[RoutineCall]
    returns: list[int]
    entries: dict[int, str | None]   # callee pc -> function label at the entry JUMPDEST


def routine_boundaries(instructions: list[Instruction], entries: list[SourceMapEntry],
                       functions: list[AstFunction]) -> RoutineInfo:
    """Internal routine call/return sites from the source map's ``i``/``o`` jump tags."""
    calls: list[RoutineCall] = []
    returns: list[int] = []
    labels: dict[int, str | None] = {}
    for k, ins in enumerate(instructions):
        if k >= len(entries):
            break
        tag = entries[k].jump
        if ins.opcode in (JUMP, JUMPI) and tag == "i":
            prev = instructions[k - 1] if k > 0 else None
            callee = prev.argument if prev is not None and is_push(prev.opcode) else None
            fn = innermost_function(functions, entries[k])
            calls.append(RoutineCall(ins.pc, callee, fn.label if fn else None))
        elif ins.opcode in (JUMP, JUMPI) and tag == "o":
            returns.append(ins.pc)
    by_pc = {ins.pc: k for k, ins in enumerate(instructions)}
    for call in calls:
        if call.callee is not None and call.callee in by_pc and call.callee not in labels:
            k = by_pc[call.callee]
            fn = innermost_function(functions, entries[k]) if k < len(entries) else None
            labels[call.callee] = fn.label if fn else None
    return RoutineInfo(calls, returns, labels)


def function_pcs(instructions: list[Instruction], entries: list[SourceMapEntry],
                 functions: list[AstFunction]) -> dict[str, list[int]]:
    """pcs of the instructions whose source range lies inside each function definition."""
    out: dict[str, list[int]] = {}
    for k, ins in enumerate(instructions):
        if k >= len(entries):
            break
        fn = innermost_function(functions, entries[k])
        if fn is not None:
            out.setdefault(fn.label, []).append(ins.pc)
    return out


# --------------------------------------------------------------------------------------------
# Build metadata

def load_build(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def method_names(method_identifiers: dict[str, str]) -> dict[int, str]:
    """selector value -> canonical signature."""
    return {int(sel, 16): sig for sig, sel in method_identifiers.items()}


def lean_name(signature: str) -> str:
    """A Lean-safe lowerCamel identifier for an ABI signature's function name."""
    name = signature.split("(", 1)[0]
    name = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not name or name[0].isdigit():
        name = "f_" + name
    return name[0].lower() + name[1:]


def overload_names(signatures: list[str]) -> dict[str, str]:
    """Unique Lean names: the function name, suffixed by parameter types for overloads."""
    base: dict[str, list[str]] = {}
    for sig in signatures:
        base.setdefault(lean_name(sig), []).append(sig)
    names: dict[str, str] = {}
    for name, sigs in base.items():
        if len(sigs) == 1:
            names[sigs[0]] = name
            continue
        for sig in sigs:
            params = sig[sig.index("(") + 1:-1]
            suffix = re.sub(r"[^A-Za-z0-9]+", "_", params).strip("_")
            names[sig] = f"{name}_{suffix}" if suffix else f"{name}_"
    return names


def code_and_blocks(code: bytes, keep_metadata: bool = False):
    body = code if keep_metadata else strip_solidity_metadata(code)
    instructions = disassemble(body)
    return body, instructions, blocks(instructions)


# --------------------------------------------------------------------------------------------
# Keccak-256 (dependency-free, for selector checks)

_KECCAK_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
_KECCAK_ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56], [27, 20, 39, 8, 14],
]
_MASK64 = (1 << 64) - 1


def _rol(x: int, n: int) -> int:
    n %= 64
    return ((x << n) | (x >> (64 - n))) & _MASK64 if n else x


def _keccak_f(state: list[int]) -> None:
    for rc in _KECCAK_RC:
        c = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] ^= d[x]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(state[x + 5 * y], _KECCAK_ROT[x][y])
        for x in range(5):
            for y in range(5):
                state[x + 5 * y] = b[x + 5 * y] ^ ((~b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y])
        state[0] ^= rc


def keccak256(data: bytes) -> bytes:
    rate = 136
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate:
        padded.append(0)
    padded[-1] |= 0x80
    state = [0] * 25
    for off in range(0, len(padded), rate):
        block = padded[off:off + rate]
        for i in range(rate // 8):
            state[i] ^= int.from_bytes(block[8 * i:8 * i + 8], "little")
        _keccak_f(state)
    return b"".join(state[i].to_bytes(8, "little") for i in range(4))


def selector(signature: str) -> bytes:
    return keccak256(signature.encode())[:4]


def abi_signatures(abi: list[dict]) -> list[str]:
    """Canonical signatures of the ABI's functions (struct tuples expanded)."""
    def ty(entry: dict) -> str:
        t = entry["type"]
        if t.startswith("tuple"):
            inner = ",".join(ty(c) for c in entry.get("components", []))
            return f"({inner}){t[len('tuple'):]}"
        return t
    return [f"{e['name']}({','.join(ty(i) for i in e.get('inputs', []))})"
            for e in abi if e.get("type") == "function"]
