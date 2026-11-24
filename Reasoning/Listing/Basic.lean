import Ethereum.Semantics

/-!
# Listing — the listing

A contract's runtime bytecode, read once from offset 0 and cut into *sections*.

* An `Instr` is one decoded instruction: an operation without an immediate, a `PUSH1`–`PUSH32`
  together with its immediate already converted to a number, or a `PUSH32` whose 32 data bytes
  are immutable number `i` (filled in at deployment, see `Reasoning/Listing/Sound.lean`).
* `scan` decodes a byte list from its first byte, in the same way as evmlean's `decode` and
  `D_J`: an opcode byte that `parseInstr` does not know is `INVALID`, and a push cut short by the
  end of the code keeps whatever data bytes there are (evmlean does not pad them with zeros).
* `cut` groups the instructions into sections: a new section starts at offset 0 and at every
  `JUMPDEST`.
* `sections bytes = cut 0 (scan 0 bytes)` is the table of a contract.  A generated file checks it
  against a table written out as a literal; `Checked` is that check together with two closed side
  conditions.

Nothing here is ever evaluated at run time; `sections` is evaluated once per contract by the
kernel, in the proof of `Checked`.
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace Reasoning.Listing

/-- One decoded instruction. -/
inductive Instr where
  /-- An instruction with no immediate. -/
  | op (o : Operation)
  /-- A `PUSH1`–`PUSH32` and its immediate, read big-endian as a number. -/
  | push (o : Operation) (v : Nat)
  /-- A full 32-byte `PUSH32` whose data bytes are immutable number `i`. -/
  | immutable (i : Nat)
  deriving DecidableEq, Repr

namespace Instr

/-- The operation. -/
def opn : Instr → Operation
  | op o => o
  | push o _ => o
  | immutable _ => .PUSH32

/-- Bytes the instruction occupies: the opcode and its immediate. -/
def width (i : Instr) : Nat := 1 + argOnNBytesOfInstr i.opn

/-- Is this a `JUMPDEST`? -/
def isJumpdest : Instr → Bool
  | op (.StackMemFlow .JUMPDEST) => true
  | _ => false

/-- Forget that a push is an immutable: what the template holds at that site, a `PUSH32` of
zero. -/
def erase : Instr → Instr
  | op o => op o
  | push o v => push o v
  | immutable _ => push .PUSH32 0

/-- Room check for one instruction: an immutable needs its 33 bytes, `n` being the bytes left. -/
def fitsIn : Instr → Nat → Bool
  | immutable _, n => decide (33 ≤ n)
  | op _, _ => true
  | push _ _, _ => true

end Instr

/-- A section: the instructions from one cut point up to the next. -/
abbrev Section := List Instr

/-- A table: `(offset, section)` pairs, in ascending offset order. -/
abbrev Table := List (Nat × Section)

/-- Bytes a run of instructions occupies. -/
def sectionWidth : List Instr → Nat
  | [] => 0
  | i :: rest => i.width + sectionWidth rest

/-- Does the section begin with `JUMPDEST`? -/
def startsJD : Section → Bool
  | i :: _ => i.isJumpdest
  | [] => false

/-- The instruction whose opcode byte is `b`, `rest` being the bytes after it.  The immediate is
read with evmlean's own `fromBytesBigEndian` from the bytes that are there (fewer than the
width when the code ends inside the push). -/
def instrOf (b : UInt8) (rest : List UInt8) : Instr :=
  let o := (parseInstr b).getD .INVALID
  if argOnNBytesOfInstr o = 0 then .op o
  else .push o (fromBytesBigEndian (rest.take (argOnNBytesOfInstr o)))

/-- Decode a byte list from its first byte.  `skip` counts immediate bytes still to be stepped
over; the recursion is structural on the byte list so that the kernel evaluates it directly. -/
def scan (skip : Nat) : List UInt8 → List Instr
  | [] => []
  | b :: rest =>
    match skip with
    | k + 1 => scan k rest
    | 0 => instrOf b rest :: scan (argOnNBytesOfInstr ((parseInstr b).getD .INVALID)) rest

/-- Group instructions into sections, the first at offset `pc`: an instruction joins the section
of the instructions after it unless that section begins with `JUMPDEST`. -/
def cut (pc : Nat) : List Instr → Table
  | [] => []
  | i :: rest =>
    match cut (pc + i.width) rest with
    | [] => [(pc, [i])]
    | (q, s) :: more => if startsJD s then (pc, [i]) :: (q, s) :: more else (pc, i :: s) :: more

/-- The table of a contract's bytecode. -/
def sections (bytes : List UInt8) : Table := cut 0 (scan 0 bytes)

/-- All the instructions of a table, in order. -/
def join (t : Table) : List Instr := t.flatMap (·.2)

/-- Every immutable replaced by what the template holds there. -/
def Table.erase (t : Table) : Table := t.map fun p => (p.1, p.2.map Instr.erase)

/-- Every immutable push has all of its 32 data bytes inside the code, `n` being the number of
bytes left.  (A `PUSH32` cut short by the end of the code would erase to the same table entry.) -/
def fits : List Instr → Nat → Bool
  | [], _ => true
  | i :: rest, n =>
    i.fitsIn n && fits rest (n - i.width)

/-- The per-contract check: the bytes decode to the table with its immutables erased, every
immutable is a full `PUSH32`, and the code is short enough that offsets are words. -/
structure Checked (bytes : List UInt8) (table : Table) : Prop where
  sections_eq : sections bytes = table.erase
  fits_eq : fits (join table) bytes.length = true
  small : bytes.length < 2 ^ 256

end Reasoning.Listing
