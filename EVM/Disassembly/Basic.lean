import Ethereum.Semantics

/-!
# Disassembly

`disassemble` decodes a contract's bytecode into instructions and splits them into sections, one
per `JUMPDEST`. It follows evmlean's `decode` and `D_J`: an unknown opcode is `INVALID`, and a
push that runs past the end of the code is padded with zeros.

A bytecode file computes its sections once and proves `Checked bytes sections` by
`decide +kernel`, which says that they are the disassembly of its bytes.
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace EVM.Disassembly

/-- A decoded instruction. -/
inductive Instr where
  /-- An instruction without an immediate. -/
  | op (o : Operation)
  /-- A push and its immediate, as a big-endian number. -/
  | push (o : Operation) (v : Nat)
  /-- A `PUSH32` whose immediate is the `i`-th immutable. -/
  | immutable (i : Nat)
  deriving DecidableEq, Repr

namespace Instr

/-- The operation of the instruction. -/
def opn : Instr → Operation
  | op o => o
  | push o _ => o
  | immutable _ => .PUSH32

/-- The size of the instruction in bytes, including its immediate. -/
def width (i : Instr) : Nat := 1 + argOnNBytesOfInstr i.opn

def isJumpdest : Instr → Bool
  | op (.StackMemFlow .JUMPDEST) => true
  | _ => false

/-- Replaces an immutable by `PUSH32 0`, which is what the template has at that site. -/
def erase : Instr → Instr
  | op o => op o
  | push o v => push o v
  | immutable _ => push .PUSH32 0

/-- An immutable needs 33 bytes, where `n` is the number of bytes left in the code. -/
def fitsIn : Instr → Nat → Bool
  | immutable _, n => decide (33 ≤ n)
  | op _, _ => true
  | push _ _, _ => true

end Instr

/-- The total size in bytes of a list of instructions. -/
def sectionWidth : List Instr → Nat
  | [] => 0
  | i :: rest => i.width + sectionWidth rest

/-- Whether the section starts with a `JUMPDEST`. -/
def startsJD : List Instr → Bool
  | i :: _ => i.isJumpdest
  | [] => false

/-- The `n` immediate bytes of a push, where `rest` is the code after its opcode. Padded with zeros
if the code ends early, like `readWithPadding`. -/
def immediate (n : Nat) (rest : List UInt8) : List UInt8 :=
  rest.take n ++ List.replicate (n - rest.length) 0

/-- The instruction with opcode byte `b`, where `rest` is the code after it. -/
def instrOf (b : UInt8) (rest : List UInt8) : Instr :=
  let o := (parseInstr b).getD .INVALID
  if argOnNBytesOfInstr o = 0 then .op o
  else .push o (fromBytesBigEndian (immediate (argOnNBytesOfInstr o) rest))

/-- Decodes a list of bytes. `skip` is the number of immediate bytes left to skip. -/
def scan (skip : Nat) : List UInt8 → List Instr
  | [] => []
  | b :: rest =>
    match skip with
    | k + 1 => scan k rest
    | 0 => instrOf b rest :: scan (argOnNBytesOfInstr ((parseInstr b).getD .INVALID)) rest

/-- Splits the instructions into sections, starting a new one at every `JUMPDEST`. `pc` is the
offset of the first instruction. -/
def cut (pc : Nat) : List Instr → List (Nat × List Instr)
  | [] => []
  | i :: rest =>
    match cut (pc + i.width) rest with
    | [] => [(pc, [i])]
    | (q, s) :: more => if startsJD s then (pc, [i]) :: (q, s) :: more else (pc, i :: s) :: more

/-- The sections of a contract's bytecode, with their offsets. -/
def disassemble (bytes : List UInt8) : List (Nat × List Instr) := cut 0 (scan 0 bytes)

/-- All the instructions of the sections, in order. -/
def join (t : List (Nat × List Instr)) : List Instr := t.flatMap (·.2)

/-- Applies `Instr.erase` to every instruction. -/
def eraseImmutables (t : List (Nat × List Instr)) : List (Nat × List Instr) :=
  t.map fun p => (p.1, p.2.map Instr.erase)

/-- Every immutable has its 32 bytes inside the code, where `n` is the number of bytes left. Without
this a truncated `PUSH32` could pass for an immutable. -/
def fits : List Instr → Nat → Bool
  | [], _ => true
  | i :: rest, n =>
    i.fitsIn n && fits rest (n - i.width)

/-- The sections are the disassembly of `bytes` up to immutables, every immutable is a full
`PUSH32`, and code offsets fit in a word. -/
structure Checked (bytes : List UInt8) (table : List (Nat × List Instr)) : Prop where
  disassemble_eq : disassemble bytes = eraseImmutables table
  fits_eq : fits (join table) bytes.length = true
  small : bytes.length < 2 ^ 256

instance (bytes : List UInt8) (table : List (Nat × List Instr)) : Decidable (Checked bytes table) :=
  decidable_of_iff
    (disassemble bytes = eraseImmutables table ∧ fits (join table) bytes.length = true ∧ bytes.length < 2 ^ 256)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end EVM.Disassembly
