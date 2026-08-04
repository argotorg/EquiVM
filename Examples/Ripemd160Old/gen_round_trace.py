#!/usr/bin/env python3
"""Generate concrete old-runtime RIPEMD round traces.

The unoptimized Solidity artifact lowers both 80-entry tables to switch trees.
This script follows each concrete round through those trees and emits the
corresponding `evm_run_rfl` certificate skeleton. It never executes or models
the hash arithmetic; symbolic values are retained wherever control flow does
not depend on the round number.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


MOD = 1 << 256


@dataclass(frozen=True)
class Value:
    concrete: int | None

    @staticmethod
    def const(value: int) -> "Value":
        return Value(value % MOD)

    @staticmethod
    def symbolic() -> "Value":
        return Value(None)


def decode(code: bytes, pc: int) -> tuple[int, int | None, int]:
    op = code[pc]
    if 0x5F <= op <= 0x7F:
        width = op - 0x5F
        value = int.from_bytes(code[pc + 1:pc + 1 + width], "big")
        return op, value, 1 + width
    return op, None, 1


MACRO = {
    0x01: "add", 0x02: "mul", 0x04: "div", 0x06: "mod",
    0x10: "lt", 0x11: "gt", 0x14: "eq", 0x15: "iszero",
    0x16: "and", 0x17: "or", 0x18: "xor", 0x19: "not",
    0x1B: "shl", 0x1C: "shr", 0x50: "pop", 0x5B: "jumpdest",
}


def unary(op: int, a: Value) -> Value:
    if a.concrete is None:
        return Value.symbolic()
    x = a.concrete
    if op == 0x15:
        return Value.const(1 if x == 0 else 0)
    if op == 0x19:
        return Value.const(MOD - 1 - x)
    raise AssertionError(hex(op))


def binary(op: int, a: Value, b: Value) -> Value:
    if a.concrete is None or b.concrete is None:
        return Value.symbolic()
    x, y = a.concrete, b.concrete
    operations = {
        0x01: lambda: x + y,
        0x02: lambda: x * y,
        0x03: lambda: x - y,
        0x04: lambda: 0 if y == 0 else x // y,
        0x06: lambda: 0 if y == 0 else x % y,
        0x10: lambda: 1 if x < y else 0,
        0x11: lambda: 1 if x > y else 0,
        0x14: lambda: 1 if x == y else 0,
        0x16: lambda: x & y,
        0x17: lambda: x | y,
        0x18: lambda: x ^ y,
        0x1B: lambda: 0 if x >= 256 else y << x,
        0x1C: lambda: 0 if x >= 256 else y >> x,
    }
    return Value.const(operations[op]())


def macro_for(op: int, value: int | None) -> str:
    if 0x5F <= op <= 0x7F:
        width = op - 0x5F
        if width == 0:
            return "push0"
        return f"push{width} ⟨{value}⟩"
    if 0x80 <= op <= 0x8F:
        return f"dup{op - 0x7F}"
    if 0x90 <= op <= 0x9F:
        return f"swap{op - 0x8F}"
    if op == 0x03:
        return "sub"
    return MACRO[op]


def trace(code: bytes, start: int, stop: int, round_number: int, ret: int) -> list[tuple[str, list[str]]]:
    stack = [Value.symbolic(), Value.symbolic(), Value.const(round_number),
             Value.const(ret)] + [Value.symbolic()] * 64
    pc = start
    segments: list[tuple[str, list[str]]] = []
    straight: list[str] = []
    steps = 0

    def flush(tag: str) -> None:
        nonlocal straight
        if straight:
            segments.append((tag, straight))
            straight = []

    while pc != stop:
        steps += 1
        if steps > 10000:
            raise RuntimeError(f"trace did not terminate at pc {pc}")
        op, immediate, width = decode(code, pc)
        next_pc = pc + width

        if 0x5F <= op <= 0x7F:
            stack.insert(0, Value.const(immediate or 0))
            straight.append(macro_for(op, immediate))
        elif 0x80 <= op <= 0x8F:
            stack.insert(0, stack[op - 0x80])
            straight.append(macro_for(op, immediate))
        elif 0x90 <= op <= 0x9F:
            index = op - 0x8F
            stack[0], stack[index] = stack[index], stack[0]
            straight.append(macro_for(op, immediate))
        elif op in (0x15, 0x19):
            stack[0] = unary(op, stack[0])
            straight.append(macro_for(op, immediate))
        elif op in (0x01, 0x02, 0x03, 0x04, 0x06, 0x10, 0x11, 0x14,
                    0x16, 0x17, 0x18, 0x1B, 0x1C):
            a, b = stack.pop(0), stack.pop(0)
            stack.insert(0, binary(op, a, b))
            straight.append(macro_for(op, immediate))
        elif op == 0x50:
            stack.pop(0)
            straight.append("pop")
        elif op == 0x51:
            stack[0] = Value.symbolic()
            flush(f"pre_mload_{pc}")
            segments.append((f"mload_{pc}", []))
        elif op == 0x52:
            stack.pop(0)
            stack.pop(0)
            flush(f"pre_mstore_{pc}")
            segments.append((f"mstore_{pc}", []))
        elif op == 0x56:
            destination = stack.pop(0).concrete
            if destination is None:
                raise RuntimeError(f"symbolic JUMP destination at pc {pc}")
            straight.append(f"jump jump_{destination}")
            flush(f"jump_{pc}")
            next_pc = destination
        elif op == 0x57:
            destination = stack.pop(0).concrete
            condition = stack.pop(0).concrete
            if destination is None or condition is None:
                raise RuntimeError(f"symbolic JUMPI at pc {pc}")
            if condition == 0:
                straight.append("jumpiNT (by native_decide)")
            else:
                straight.append(f"jumpiT (by native_decide) jump_{destination}")
                next_pc = destination
            flush(f"jumpi_{pc}")
        elif op == 0x5B:
            straight.append("jumpdest")
        else:
            raise RuntimeError(f"unsupported opcode {op:#x} at pc {pc}")
        pc = next_pc

    flush("finish")
    return segments


def render(round_number: int, segments: list[tuple[str, list[str]]], side: str) -> str:
    start = 288 if side == "left" else 4126
    ret = 8991 if side == "left" else 8967
    name = f"runtime_{side}RoundHelper_{round_number}"
    cursor = "oldLeftRoundCursor" if side == "left" else "oldRightRoundCursor"
    lines = [
        f"theorem {name} {{cA σ I}} {{g : Sat256}} {{s0 : State}}",
        "    {t : List UInt256} {c : RuntimeMemCursor} {rdata : ByteArray} {k C : Nat}",
        "    (hov : t.length + 64 ≤ 1024)",
        f"    (rd : RD runtimeBytecode I g s0 ⟨{start}⟩",
        f"      (old{side.capitalize()}HelperStack I {round_number} t) c.mem c.aw rdata (cA, σ) k C) :",
        f"    ∃ k' C', RD runtimeBytecode I g s0 ⟨{ret}⟩ t",
        f"      ({cursor} c (hashScratchPtr I) {round_number // 16} {round_number % 16}).mem",
        f"      ({cursor} c (hashScratchPtr I) {round_number // 16} {round_number % 16}).aw",
        "      rdata (cA, σ) k' C' := by",
        f"  simp only [old{side.capitalize()}HelperStack] at rd",
    ]
    current = "rd"
    serial = 0
    for tag, ops in segments:
        serial += 1
        target = f"rd{serial}"
        if tag.startswith("mload_"):
            pc = int(tag.rsplit("_", 1)[1])
            lines.append(f"  have {target} := RD.runtimeMload {current} (by old_decode) (by simp; omega)")
        elif tag.startswith("mstore_"):
            pc = int(tag.rsplit("_", 1)[1])
            lines.append(f"  have {target} := RD.runtimeMstore {current} (by old_decode) (by simp; omega)")
        else:
            joined = ", ".join(ops)
            lines.append(f"  have {target} := evm_run_rfl {current} with [{joined}]")
        current = target
    lines.extend([
        "  exact ⟨_, _, by",
        f"    simpa [old{side.capitalize()}HelperStack, {cursor}, runtimeRoundPreludeCursor,",
        "      runtimePreludeB, runtimePreludeC, runtimePreludeD, runtimeRightPreludeCursor,",
        "      runtimeRightPreludeB, runtimeRightPreludeC, runtimeRightPreludeD,",
        "      runtimeRoundCursor, runtimeRoundNext, runtimeRoundSum, runtimeRol32,",
        "      runtimeRoundX, runtimeRoundAwX, runtimeRoundMessageAddr, runtimeRowEntry,",
        "      runtimeRoundA, runtimeRoundAwA, runtimeRoundB, runtimeRoundAwB,",
        "      runtimeRoundC, runtimeRoundAwC, runtimeRoundD, runtimeRoundAwD,",
        "      runtimeRoundE, runtimeRoundAwE, runtimeStoreCursor, runtimeLeftF,",
        "      runtimeRightF, leftWordRowWord, leftRotationRowWord, leftConstantWord,",
        "      rightWordRowWord, rightRotationRowWord, rightConstantWord, mask32Word,",
        f"      Model.leftWordRow, Model.leftRotationRow, Model.leftConstant,",
        f"      Model.rightWordRow, Model.rightRotationRow, Model.rightConstant,",
        "      u256_add_comm, u256_land_comm, u256_lor_comm] using " + current + "⟩",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--side", choices=("left", "right"), required=True)
    parser.add_argument("--round", type=int, action="append", dest="rounds")
    parser.add_argument("--runtime", type=Path, default=Path(__file__).with_name("runtime.hex"))
    args = parser.parse_args()
    rounds = args.rounds if args.rounds is not None else list(range(80))
    code = bytes.fromhex(args.runtime.read_text().strip())
    start = 288 if args.side == "left" else 4126
    stop = 8991 if args.side == "left" else 8967
    ret = stop
    for round_number in rounds:
        print(render(round_number, trace(code, start, stop, round_number, ret), args.side))


if __name__ == "__main__":
    main()
