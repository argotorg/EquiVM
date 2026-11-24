import Reasoning.Reach
import Reasoning.Listing.Sound

/-!
# Listing — block summaries from a run over the listing

The generated block theorems (`RuntimeBlocks_*`) state `RD` at a block's last offset from
`RD` at its first.  Their proofs apply one `RD.<opcode>` rule per instruction, and each rule
application proves `decode code pc = some …` on the bytes.  Here the same statements are proved
from the listing (`Reasoning/Listing/Basic.lean`): the instructions are already decoded, and a function runs
them.

* `step1`, `stepP`: what one instruction does to the *counted* part of the stack (`top`, a list
  whose spine is closed; the stack is `top ++ R`), the memory, the active words, the account map
  and the step and gas counters.  Each case builds exactly the terms the matching `RD.<opcode>`
  rule states, and the stack room that rule asks for.  `stepP` holds the instructions whose rule
  has a side condition (`ee.perm = true`, a return-data bound) and `GAS`.
* Counters: `ex = true` while the counters `k`, `C` are exact.  `SLOAD`, `SSTORE` and
  `EXTCODESIZE` have a cost that depends on the state; their rules conclude `∃ k' C'`, and after
  one of them `ex = false` (`RDm`).  `GAS` pushes a word computed from `C`, so it needs
  `ex = true`; the caller gives the gas spent so far in the form its statement uses (a *hint*)
  and the run asks that it equals `C`.
* `run`: `fuel` instructions of a list, one after the other, with the offset, the greatest room
  asked for against a bound `m` and the conjunction of the side conditions (`pre`).
* `RDL`: `RDm` at an offset together with the fact that the code decodes from there as a list
  of instructions.
* `RDL.run`: the run is sound, given `pre` and `R.length + m ≤ 1024`.
* `RDL.enter` and the endings (`rd`, `jump`, `jumpiT`, `jumpiNT`, with `X` forms for runs that
  lost the counters; `rev`, `ret`, `stop`, `invalid`).

Nothing is evaluated on bytes: the per-contract check of the listing (`Checked`) is the only
place the bytecode is read.
-/

open Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
-- the per-category functions share one signature; not every one reads every argument
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Reasoning.Listing

/-! ## Offsets -/

/-- Offsets add as words, whatever their size (`UInt256.ofNat` reduces modulo `2 ^ 256`). -/
theorem ofNat_add (n m : Nat) : UInt256.ofNat n + UInt256.ofNat m = UInt256.ofNat (n + m) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  show ((Fin.ofNat UInt256.size n) + (Fin.ofNat UInt256.size m)).val
      = (Fin.ofNat UInt256.size (n + m)).val
  rw [Fin.val_add, Fin.val_ofNat, Fin.val_ofNat, Fin.val_ofNat, ← Nat.add_mod]

theorem ofNat_add_one (n : Nat) : UInt256.ofNat n + ⟨1⟩ = UInt256.ofNat (n + 1) :=
  ofNat_add n 1

/-! ## `RD` with exact or lost counters -/

/-- `RD` with the counters `k`, `C` when `ex`, and with some counters otherwise. -/
def RDm (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State) (ex : Bool)
    (pc : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : AccountMap) (k C : ℕ) : Prop :=
  match ex with
  | true => RD code ee g s0 pc stk mem aw rdata acc k C
  | false => ∃ k' C', RD code ee g s0 pc stk mem aw rdata acc k' C'

section RDm

variable {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {ex : Bool}
  {pc pc' : UInt256} {stk stk' : List UInt256} {mem mem' : ByteArray} {aw aw' : UInt256}
  {rdata : ByteArray} {acc acc' : AccountMap} {k C : ℕ}

theorem RDm.some (h : RDm code ee g s0 ex pc stk mem aw rdata acc k C) :
    ∃ k' C', RD code ee g s0 pc stk mem aw rdata acc k' C' := by
  cases ex
  · exact h
  · exact ⟨_, _, h⟩

/-- A rule with an exact cost keeps the counters exact if they were. -/
theorem RDm.exact {c : ℕ} (h : RDm code ee g s0 ex pc stk mem aw rdata acc k C)
    (f : ∀ k C, RD code ee g s0 pc stk mem aw rdata acc k C →
      RD code ee g s0 pc' stk' mem' aw' rdata acc' (k + 1) (C + c)) :
    RDm code ee g s0 ex pc' stk' mem' aw' rdata acc' (k + 1) (C + c) := by
  cases ex
  · obtain ⟨k0, C0, h⟩ := h
    exact ⟨_, _, f _ _ h⟩
  · exact f _ _ h

/-- A rule that concludes `∃ k' C'` loses the counters. -/
theorem RDm.lose {k' C' : ℕ} (h : RDm code ee g s0 ex pc stk mem aw rdata acc k C)
    (f : ∀ k C, RD code ee g s0 pc stk mem aw rdata acc k C →
      ∃ k' C', RD code ee g s0 pc' stk' mem' aw' rdata acc' k' C') :
    RDm code ee g s0 false pc' stk' mem' aw' rdata acc' k' C' := by
  obtain ⟨k0, C0, h⟩ := h.some
  exact f _ _ h

end RDm

/-! ## One instruction -/

/-- `DUP1`–`DUP16`: the new counted words and the room asked for. -/
def dupTop (o : Operation.DOp) (top : List UInt256) : Option (List UInt256 × ℕ) :=
  match o, top with
  | .DUP1, x0 :: t => some (x0 :: x0 :: t, t.length + 2)
  | .DUP2, x0 :: x1 :: t => some (x1 :: x0 :: x1 :: t, t.length + 3)
  | .DUP3, x0 :: x1 :: x2 :: t => some (x2 :: x0 :: x1 :: x2 :: t, t.length + 4)
  | .DUP4, x0 :: x1 :: x2 :: x3 :: t => some (x3 :: x0 :: x1 :: x2 :: x3 :: t, t.length + 5)
  | .DUP5, x0 :: x1 :: x2 :: x3 :: x4 :: t => some (x4 :: x0 :: x1 :: x2 :: x3 :: x4 :: t, t.length + 6)
  | .DUP6, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: t => some (x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: t, t.length + 7)
  | .DUP7, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: t => some (x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: t, t.length + 8)
  | .DUP8, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: t => some (x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: t, t.length + 9)
  | .DUP9, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: t => some (x8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: t, t.length + 10)
  | .DUP10, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: t => some (x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: t, t.length + 11)
  | .DUP11, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: t => some (x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: t, t.length + 12)
  | .DUP12, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: t => some (x11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: t, t.length + 13)
  | .DUP13, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: t => some (x12 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: t, t.length + 14)
  | .DUP14, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: t => some (x13 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: t, t.length + 15)
  | .DUP15, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: t => some (x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: t, t.length + 16)
  | .DUP16, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: t => some (x15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: t, t.length + 17)
  | _, _ => none

/-- `SWAP1`–`SWAP16`. -/
def swapTop (o : Operation.ExOp) (top : List UInt256) : Option (List UInt256 × ℕ) :=
  match o, top with
  | .SWAP1, x0 :: x1 :: t => some (x1 :: x0 :: t, t.length + 2)
  | .SWAP2, x0 :: x1 :: x2 :: t => some (x2 :: x1 :: x0 :: t, t.length + 3)
  | .SWAP3, x0 :: x1 :: x2 :: x3 :: t => some (x3 :: x1 :: x2 :: x0 :: t, t.length + 4)
  | .SWAP4, x0 :: x1 :: x2 :: x3 :: x4 :: t => some (x4 :: x1 :: x2 :: x3 :: x0 :: t, t.length + 5)
  | .SWAP5, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: t => some (x5 :: x1 :: x2 :: x3 :: x4 :: x0 :: t, t.length + 6)
  | .SWAP6, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: t => some (x6 :: x1 :: x2 :: x3 :: x4 :: x5 :: x0 :: t, t.length + 7)
  | .SWAP7, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: t => some (x7 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: t, t.length + 8)
  | .SWAP8, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: t => some (x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: t, t.length + 9)
  | .SWAP9, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: t => some (x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x0 :: t, t.length + 10)
  | .SWAP10, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: t => some (x10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x0 :: t, t.length + 11)
  | .SWAP11, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: t => some (x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: t, t.length + 12)
  | .SWAP12, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: t => some (x12 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0 :: t, t.length + 13)
  | .SWAP13, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: t => some (x13 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x0 :: t, t.length + 14)
  | .SWAP14, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: t => some (x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0 :: t, t.length + 15)
  | .SWAP15, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: t => some (x15 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x0 :: t, t.length + 16)
  | .SWAP16, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: t => some (x16 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x0 :: t, t.length + 17)
  | _, _ => none

/-- Comparisons and bitwise operations (cost 3). -/
def compTop (o : Operation.CBLOp) (top : List UInt256) : Option (List UInt256 × ℕ) :=
  match o, top with
  | .LT, a :: b :: t => some (UInt256.lt a b :: t, t.length + 1)
  | .GT, a :: b :: t => some (UInt256.gt a b :: t, t.length + 1)
  | .SLT, a :: b :: t => some (UInt256.slt a b :: t, t.length + 1)
  | .SGT, a :: b :: t => some (UInt256.sgt a b :: t, t.length + 1)
  | .EQ, a :: b :: t => some (UInt256.eq a b :: t, t.length + 1)
  | .AND, a :: b :: t => some (UInt256.land a b :: t, t.length + 1)
  | .OR, a :: b :: t => some (UInt256.lor a b :: t, t.length + 1)
  | .XOR, a :: b :: t => some (UInt256.xor a b :: t, t.length + 1)
  | .SHL, a :: b :: t => some (UInt256.shiftLeft b a :: t, t.length + 1)
  | .SHR, a :: b :: t => some (UInt256.shiftRight b a :: t, t.length + 1)
  | .ISZERO, a :: t => some (UInt256.isZero a :: t, t.length + 1)
  | .NOT, a :: t => some (UInt256.lnot a :: t, t.length + 1)
  | .BYTE, a :: b :: t => some (UInt256.byteAt a b :: t, t.length + 1)
  | .SAR, a :: b :: t => some (UInt256.sar a b :: t, t.length + 1)
  | _, _ => none

/-- Arithmetic: the new counted words, the cost and the room asked for. -/
def arithTop (o : Operation.SAOp) (top : List UInt256) : Option (List UInt256 × ℕ × ℕ) :=
  match o, top with
  | .ADD, a :: b :: t => some ((a + b) :: t, 3, t.length + 1)
  | .MUL, a :: b :: t => some (UInt256.mul a b :: t, 5, t.length + 1)
  | .SUB, a :: b :: t => some (UInt256.sub a b :: t, 3, t.length + 1)
  | .DIV, a :: b :: t => some (UInt256.div a b :: t, 5, t.length + 1)
  | .MOD, a :: b :: t => some (UInt256.mod a b :: t, 5, t.length + 1)
  | .SDIV, a :: b :: t => some (UInt256.sdiv a b :: t, 5, t.length + 1)
  | .SIGNEXTEND, a :: b :: t => some (UInt256.signextend a b :: t, 5, t.length + 1)
  | .MULMOD, a :: b :: c :: t => some (UInt256.mulMod a b c :: t, 8, t.length + 1)
  | .EXP, a :: b :: t => some (UInt256.exp a b :: t, expGasCost b, t.length + 1)
  | _, _ => none

/-- Environment reads and copies. -/
def envStep (code : ByteArray) (ee : ExecutionEnv) (rdata : ByteArray) (o : Operation.EOp)
    (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap) (ex : Bool) (k C : ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ) :=
  match o, top with
  | .CALLDATASIZE, t =>
    some (UInt256.ofNat ee.calldata.size :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .CALLVALUE, t =>
    some (ee.weiValue :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .CALLER, t =>
    some (UInt256.ofNat ee.source.val :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .ADDRESS, t =>
    some (UInt256.ofNat ee.codeOwner.val :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .CODESIZE, t =>
    some (UInt256.ofNat code.size :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .RETURNDATASIZE, t =>
    some (UInt256.ofNat rdata.size :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .CALLDATALOAD, a :: t =>
    some (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32) :: t, mem, aw, acc, ex, k + 1, C + 3, t.length + 1)
  | .CALLDATACOPY, a :: b :: c :: t =>
    some (t, ee.calldata.write b.toNat mem a.toNat c.toNat, M aw a c, acc, ex, k + 1, C + (memExpansionCost aw a c + (3 + 3 * ((c.toNat + 31) / 32))), t.length)
  | .EXTCODESIZE, a :: t =>
    some (extCodeSizeWord acc a :: t, mem, aw, acc, false, k, C, t.length + 1)
  | .CODECOPY, a :: b :: c :: t =>
    some (t, code.write b.toNat mem a.toNat c.toNat, M aw a c, acc, ex, k + 1, C + (memExpansionCost aw a c + (3 + 3 * ((c.toNat + 31) / 32))), t.length)
  | _, _ => none

/-- Block reads. -/
def blockStep (code : ByteArray) (ee : ExecutionEnv) (rdata : ByteArray) (o : Operation.BOp)
    (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap) (ex : Bool) (k C : ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ) :=
  match o, top with
  | .TIMESTAMP, t =>
    some (UInt256.ofNat ee.header.timestamp :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .CHAINID, t =>
    some (UInt256.ofNat Ethereum.chainId :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | .BASEFEE, t =>
    some (UInt256.ofNat ee.header.baseFeePerGas :: t, mem, aw, acc, ex, k + 1, C + 2, t.length + 1)
  | _, _ => none

/-- Stack, memory (`MCOPY` included), storage and transient-storage reads (no jumps, no
`SSTORE`/`TSTORE`, no `GAS`). -/
def smfStep (code : ByteArray) (ee : ExecutionEnv) (rdata : ByteArray) (o : Operation.SMSFOp)
    (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap) (ex : Bool) (k C : ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ) :=
  match o, top with
  | .JUMPDEST, t =>
    some (t, mem, aw, acc, ex, k + 1, C + 1, t.length)
  | .POP, a :: t =>
    some (t, mem, aw, acc, ex, k + 1, C + 2, t.length)
  | .MSTORE, a :: b :: t =>
    some (t, b.toByteArray.write 0 mem a.toNat 32, M aw a ⟨32⟩, acc, ex, k + 1, C + (memExpansionCost aw a ⟨32⟩ + 3), t.length)
  | .MSTORE8, a :: b :: t =>
    some (t, (⟨#[UInt8.ofNat b.toNat]⟩ : ByteArray).write 0 mem a.toNat 1, M aw a ⟨1⟩, acc, ex, k + 1, C + (memExpansionCost aw a ⟨1⟩ + 3), t.length)
  | .MLOAD, a :: t =>
    some (memLoad a mem :: t, mem, M aw a ⟨32⟩, acc, ex, k + 1, C + (memExpansionCost aw a ⟨32⟩ + 3), t.length + 1)
  | .SLOAD, a :: t =>
    some ((acc.get? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD a ⟨0⟩)) :: t, mem, aw, acc, false, k, C, t.length + 1)
  | .TLOAD, a :: t =>
    some ((acc.get? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.tstorage.getD a ⟨0⟩)) :: t, mem, aw, acc, ex, k + 1, C + Ctload, t.length + 1)
  | .MCOPY, a :: b :: c :: t =>
    some (t, mem.write b.toNat mem a.toNat c.toNat, Mmcopy aw a b c, acc, ex, k + 1, C + (mcopyExpansionCost aw a b c + (3 + 3 * ((c.toNat + 31) / 32))), t.length)
  | _, _ => none

/-- `KECCAK256`. -/
def kecStep (code : ByteArray) (ee : ExecutionEnv) (rdata : ByteArray) (o : Operation.KOp)
    (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap) (ex : Bool) (k C : ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ) :=
  match o, top with
  | .KECCAK256, a :: b :: t =>
    some (keccakWord a b mem :: t, mem, M aw a b, acc, ex, k + 1, C + (memExpansionCost aw a b + (30 + 6 * ((b.toNat + 31) / 32))), t.length + 1)
  | _, _ => none

/-- What an instruction without side condition does to the counted words `top`, the memory, the
active words, the account map and the counters, and the stack room its rule asks for (as counted
words); `none` for an instruction it does not cover or a stack too short. -/
def step1 (code : ByteArray) (ee : ExecutionEnv) (rdata : ByteArray) (σ : Nat → UInt256)
    (i : Instr) (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap)
    (ex : Bool) (k C : ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ) :=
  match i with
  | .push (.Push .PUSH0) _ => none
  | .push (.Push _) v => some (UInt256.ofNat v :: top, mem, aw, acc, ex, k + 1, C + 3, top.length + 1)
  | .immutable j => some (σ j :: top, mem, aw, acc, ex, k + 1, C + 3, top.length + 1)
  | .op (.Push .PUSH0) => some (⟨0⟩ :: top, mem, aw, acc, ex, k + 1, C + 2, top.length + 1)
  | .op (.Dup o) =>
    match dupTop o top with
    | some (top', req) => some (top', mem, aw, acc, ex, k + 1, C + 3, req)
    | none => none
  | .op (.Exchange o) =>
    match swapTop o top with
    | some (top', req) => some (top', mem, aw, acc, ex, k + 1, C + 3, req)
    | none => none
  | .op (.CompBit o) =>
    match compTop o top with
    | some (top', req) => some (top', mem, aw, acc, ex, k + 1, C + 3, req)
    | none => none
  | .op (.StopArith o) =>
    match arithTop o top with
    | some (top', c, req) => some (top', mem, aw, acc, ex, k + 1, C + c, req)
    | none => none
  | .op (.Env o) => envStep code ee rdata o top mem aw acc ex k C
  | .op (.Block o) => blockStep code ee rdata o top mem aw acc ex k C
  | .op (.StackMemFlow o) => smfStep code ee rdata o top mem aw acc ex k C
  | .op (.Keccak o) => kecStep code ee rdata o top mem aw acc ex k C
  | _ => none

/-- The instructions whose rule has a side condition, which is returned, and `GAS`, which takes
the gas spent so far from the hints. -/
def stepP (ee : ExecutionEnv) (g : Sat256) (rdata : ByteArray)
    (i : Instr) (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap)
    (ex : Bool) (k C : ℕ) (hints : List ℕ) :
    Option (List UInt256 × ByteArray × UInt256 × AccountMap × Bool × ℕ × ℕ × ℕ × Prop × List ℕ) :=
  match i, top, ex, hints with
  | .op (.StackMemFlow .SSTORE), slot :: val :: t, _, hs =>
    some (t, mem, aw, sstoreAccountMap ee.codeOwner acc slot val, false, k, C, t.length,
      ee.perm = true, hs)
  | .op (.StackMemFlow .TSTORE), slot :: val :: t, ex, hs =>
    some (t, mem, aw, tstoreAccountMap ee.codeOwner acc slot val, ex, k + 1, C + Ctstore, t.length,
      ee.perm = true, hs)
  | .op (.Log .LOG1), a :: b :: _ :: t, ex, hs =>
    some (t, mem, M aw a b, acc, ex, k + 1,
      C + (memExpansionCost aw a b + (375 + 8 * b.toNat + 375)), t.length, ee.perm = true, hs)
  | .op (.Log .LOG2), a :: b :: _ :: _ :: t, ex, hs =>
    some (t, mem, M aw a b, acc, ex, k + 1,
      C + (memExpansionCost aw a b + (375 + 8 * b.toNat + 2 * 375)), t.length, ee.perm = true, hs)
  | .op (.Log .LOG3), a :: b :: _ :: _ :: _ :: t, ex, hs =>
    some (t, mem, M aw a b, acc, ex, k + 1,
      C + (memExpansionCost aw a b + (375 + 8 * b.toNat + 3 * 375)), t.length, ee.perm = true, hs)
  | .op (.Log .LOG4), a :: b :: _ :: _ :: _ :: _ :: t, ex, hs =>
    some (t, mem, M aw a b, acc, ex, k + 1,
      C + (memExpansionCost aw a b + (375 + 8 * b.toNat + 4 * 375)), t.length, ee.perm = true, hs)
  | .op (.Env .RETURNDATACOPY), a :: b :: c :: t, ex, hs =>
    some (t, rdata.write b.toNat mem a.toNat c.toNat, M aw a c, acc, ex, k + 1,
      C + (memExpansionCost aw a c + (3 + 3 * ((c.toNat + 31) / 32))), t.length,
      b.toNat + c.toNat ≤ rdata.size, hs)
  | .op (.StackMemFlow .GAS), t, true, c :: hs =>
    some ((g.subNat (c + 2)).toUInt256 :: t, mem, aw, acc, true, k + 1, c + 2, t.length + 1,
      C = c, hs)
  | _, _, _, _ => none

section Sound

variable {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {σ : Nat → UInt256} {R : List UInt256} {rdata : ByteArray}

section Pure
variable {mem : ByteArray} {aw : UInt256} {acc : AccountMap}

theorem dupTop_sound {o : Operation.DOp} {pc : Nat} {top top' : List UInt256} {req k C : ℕ}
    (hs : dupTop o top = some (top', req))
    (hd : decode code (UInt256.ofNat pc) = some (.Dup o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RD code ee g s0 (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RD code ee g s0 (UInt256.ofNat (pc + 1)) (top' ++ R) mem aw rdata acc (k + 1) (C + 3) := by
  unfold dupTop at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · have r := RD.dup1 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup2 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup3 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup4 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup5 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup6 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup7 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup8 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup9 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup10 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup11 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup12 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup13 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup14 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup15 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.dup16 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r

theorem swapTop_sound {o : Operation.ExOp} {pc : Nat} {top top' : List UInt256} {req k C : ℕ}
    (hs : swapTop o top = some (top', req))
    (hd : decode code (UInt256.ofNat pc) = some (.Exchange o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RD code ee g s0 (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RD code ee g s0 (UInt256.ofNat (pc + 1)) (top' ++ R) mem aw rdata acc (k + 1) (C + 3) := by
  unfold swapTop at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · have r := RD.swap1 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap2 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap3 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap4 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap5 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap6 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap7 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap8 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap9 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap10 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap11 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap12 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap13 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap14 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap15 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.swap16 rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r

theorem compTop_sound {o : Operation.CBLOp} {pc : Nat} {top top' : List UInt256} {req k C : ℕ}
    (hs : compTop o top = some (top', req))
    (hd : decode code (UInt256.ofNat pc) = some (.CompBit o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RD code ee g s0 (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RD code ee g s0 (UInt256.ofNat (pc + 1)) (top' ++ R) mem aw rdata acc (k + 1) (C + 3) := by
  unfold compTop at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · have r := RD.lt rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.gt rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.slt rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.sgt rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.eq rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.and rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.or rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.xor rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.shl rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.shr rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.iszero rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.not rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.byte rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.sar rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r

theorem arithTop_sound {o : Operation.SAOp} {pc : Nat} {top top' : List UInt256} {c req k C : ℕ}
    (hs : arithTop o top = some (top', c, req))
    (hd : decode code (UInt256.ofNat pc) = some (.StopArith o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RD code ee g s0 (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RD code ee g s0 (UInt256.ofNat (pc + 1)) (top' ++ R) mem aw rdata acc (k + 1) (C + c) := by
  unfold arithTop at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · have r := RD.add rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.mul rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.sub rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.div rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.mod rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.sdiv rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.signextend rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.mulmod rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r
  · have r := RD.exp rd hd (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r

theorem envStep_sound {o : Operation.EOp} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ}
    (hs : envStep code ee rdata o top mem aw acc ex k C = some (top', mem', aw', acc', ex', k', C', req))
    (hd : decode code (UInt256.ofNat pc) = some (.Env o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + 1)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold envStep at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.calldatasize rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.callvalue rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.caller rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.address rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.codesize rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.returndatasize rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.calldataload rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genCalldatacopy rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.lose rd (fun _ _ rd => by
      obtain ⟨k', C', r⟩ := RD.extcodesize rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact ⟨k', C', r⟩)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genCodecopy rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)

theorem blockStep_sound {o : Operation.BOp} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ}
    (hs : blockStep code ee rdata o top mem aw acc ex k C = some (top', mem', aw', acc', ex', k', C', req))
    (hd : decode code (UInt256.ofNat pc) = some (.Block o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + 1)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold blockStep at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.timestamp rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.chainid rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.basefee rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)

theorem smfStep_sound {o : Operation.SMSFOp} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ}
    (hs : smfStep code ee rdata o top mem aw acc ex k C = some (top', mem', aw', acc', ex', k', C', req))
    (hd : decode code (UInt256.ofNat pc) = some (.StackMemFlow o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + 1)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold smfStep at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.jumpdest rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.pop rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genMstore rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genMstore8 rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genMload rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.lose rd (fun _ _ rd => by
      obtain ⟨k', C', r⟩ := RD.sload rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact ⟨k', C', r⟩)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.tload rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genMcopy rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)

theorem kecStep_sound {o : Operation.KOp} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ}
    (hs : kecStep code ee rdata o top mem aw acc ex k C = some (top', mem', aw', acc', ex', k', C', req))
    (hd : decode code (UInt256.ofNat pc) = some (.Keccak o, none))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + 1)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold kecStep at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genKeccak256 rd hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)

end Pure

/-- One instruction of `step1` is the matching `RD.<opcode>` rule. -/
theorem step1_sound {i : Instr} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ}
    (hs : step1 code ee rdata σ i top mem aw acc ex k C
      = some (top', mem', aw', acc', ex', k', C', req))
    (hd : decode code (UInt256.ofNat pc) = some (i.sem σ))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + i.width)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold step1 at hs
  split at hs
  · exact absurd hs (by simp)
  · rename_i o v hne
    cases hs
    exact RDm.exact rd (fun _ _ rd => by
      have r := rd.pushConst _ hne hd
        (by simp only [List.length_append]; omega)
      rw [ofNat_add, Nat.succ_eq_add_one, Nat.add_comm _ 1] at r; exact r)
  · cases hs
    exact RDm.exact rd (fun _ _ rd => by
      have r := rd.pushConst (op := .PUSH32) _ (by decide) hd
        (by simp only [List.length_append]; omega)
      rw [ofNat_add] at r; exact r)
  · cases hs
    exact RDm.exact rd (fun _ _ rd => by
      have r := rd.push0 hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · split at hs <;> cases hs
    rename_i h
    exact RDm.exact rd (fun _ _ rd => dupTop_sound h hd hreq rd)
  · split at hs <;> cases hs
    rename_i h
    exact RDm.exact rd (fun _ _ rd => swapTop_sound h hd hreq rd)
  · split at hs <;> cases hs
    rename_i h
    exact RDm.exact rd (fun _ _ rd => compTop_sound h hd hreq rd)
  · split at hs <;> cases hs
    rename_i h
    exact RDm.exact rd (fun _ _ rd => arithTop_sound h hd hreq rd)
  · exact envStep_sound hs hd hreq rd
  · exact blockStep_sound hs hd hreq rd
  · exact smfStep_sound hs hd hreq rd
  · exact kecStep_sound hs hd hreq rd
  · exact absurd hs (by simp)

/-- One instruction of `stepP`, given its side condition. -/
theorem stepP_sound {i : Instr} {pc : Nat} {top top' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {acc acc' : AccountMap} {ex ex' : Bool} {k C k' C' req : ℕ} {p : Prop}
    {hints hints' : List ℕ}
    (hs : stepP ee g rdata i top mem aw acc ex k C hints
      = some (top', mem', aw', acc', ex', k', C', req, p, hints'))
    (hp : p)
    (hd : decode code (UInt256.ofNat pc) = some (i.sem σ))
    (hreq : req + R.length ≤ 1024)
    (rd : RDm code ee g s0 ex (UInt256.ofNat pc) (top ++ R) mem aw rdata acc k C) :
    RDm code ee g s0 ex' (UInt256.ofNat (pc + i.width)) (top' ++ R) mem' aw' rdata acc' k' C' := by
  unfold stepP at hs
  split at hs <;> cases hs <;> try simp only [List.cons_append] at rd ⊢
  · exact RDm.lose rd (fun _ _ rd => by
      obtain ⟨k', C', r⟩ := RD.sstore rd hp hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact ⟨k', C', r⟩)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.tstore rd hp hd (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genLog1 rd hd hp (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genLog2 rd hd hp (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genLog3 rd hd hp (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genLog4 rd hd hp (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · exact RDm.exact rd (fun _ _ rd => by
      have r := RD.genReturndatacopy rd hd hp (by simp only [List.length_append]; omega)
      rw [ofNat_add_one] at r; exact r)
  · subst hp
    have r := RD.genGas (g := g) (show RD code ee g s0 _ _ _ _ _ _ _ _ from rd) hd
      (by simp only [List.length_append]; omega)
    rw [ofNat_add_one] at r; exact r

end Sound

/-! ## A run of instructions -/

/-- Where a run stopped. -/
structure Res where
  /-- the offset -/
  pc : ℕ
  /-- the instructions not yet run -/
  rest : List Instr
  top : List UInt256
  mem : ByteArray
  aw : UInt256
  acc : AccountMap
  /-- are `k`, `C` exact? -/
  ex : Bool
  k : ℕ
  C : ℕ
  /-- did every rule's stack room fit in the bound `m`? -/
  ok : Bool
  /-- the side conditions met so far -/
  pre : Prop
  /-- the hints not yet used -/
  hints : List ℕ

/-- Run `fuel` instructions of `is` from offset `pc`; `none` if one is not covered or the list
is too short.  `m` is the stack room allowed, in counted words. -/
def run (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (rdata : ByteArray)
    (σ : Nat → UInt256) (m : ℕ) :
    ℕ → List Instr → ℕ → List UInt256 → ByteArray → UInt256 → AccountMap → Bool → ℕ → ℕ → Bool →
      Prop → List ℕ → Option Res
  | 0, is, pc, top, mem, aw, acc, ex, k, C, ok, pre, hints =>
    some ⟨pc, is, top, mem, aw, acc, ex, k, C, ok, pre, hints⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, _, _, _ => none
  | f + 1, i :: is, pc, top, mem, aw, acc, ex, k, C, ok, pre, hints =>
    match step1 code ee rdata σ i top mem aw acc ex k C with
    | some (top', mem', aw', acc', ex', k', C', req) =>
      run code ee g rdata σ m f is (pc + i.width) top' mem' aw' acc' ex' k' C'
        (ok && Nat.ble req m) pre hints
    | none =>
      match stepP ee g rdata i top mem aw acc ex k C hints with
      | some (top', mem', aw', acc', ex', k', C', req, p, hints') =>
        run code ee g rdata σ m f is (pc + i.width) top' mem' aw' acc' ex' k' C'
          (ok && Nat.ble req m) (pre ∧ p) hints'
      | none => none

/-- `RDm` at offset `n`, with the code decoding from `n` as the instructions `is`. -/
def RDL (code : ByteArray) (σ : Nat → UInt256) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (ex : Bool) (n : ℕ) (is : List Instr) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : AccountMap) (k C : ℕ) : Prop :=
  RDm code ee g s0 ex (UInt256.ofNat n) stk mem aw rdata acc k C ∧ Decodes code σ n is

section Sound

variable {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {σ : Nat → UInt256} {R : List UInt256} {rdata : ByteArray}

theorem run_sound {m : ℕ} (hm : m + R.length ≤ 1024) : ∀ (fuel : ℕ) (is : List Instr) (pc : ℕ)
    (top : List UInt256) (mem : ByteArray) (aw : UInt256) (acc : AccountMap) (ex : Bool)
    (k C : ℕ) (ok : Bool) (pre : Prop) (hints : List ℕ) (r : Res),
    run code ee g rdata σ m fuel is pc top mem aw acc ex k C ok pre hints = some r →
    r.ok = true → r.pre → ok = true ∧ pre ∧
      (RDL code σ ee g s0 ex pc is (top ++ R) mem aw rdata acc k C →
        RDL code σ ee g s0 r.ex r.pc r.rest (r.top ++ R) r.mem r.aw rdata r.acc r.k r.C)
  | 0, is, pc, top, mem, aw, acc, ex, k, C, ok, pre, hints, r, h, hok, hp => by
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨hok, hp, fun e => e⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, h, _, _ => by simp [run] at h
  | f + 1, i :: is, pc, top, mem, aw, acc, ex, k, C, ok, pre, hints, r, h, hok, hp => by
    simp only [run] at h
    split at h
    · rename_i top' mem' aw' acc' ex' k' C' req hs
      obtain ⟨hok', hpre, hrun⟩ := run_sound hm f is (pc + i.width) top' mem' aw' acc' ex' k' C'
        (ok && Nat.ble req m) pre hints r h hok hp
      rw [Bool.and_eq_true] at hok'
      have hreq : req ≤ m := Nat.le_of_ble_eq_true hok'.2
      exact ⟨hok'.1, hpre, fun e => hrun ⟨step1_sound hs e.2.head (by omega) e.1, e.2.tail⟩⟩
    · split at h
      · rename_i top' mem' aw' acc' ex' k' C' req p hints' hs
        obtain ⟨hok', hpre, hrun⟩ := run_sound hm f is (pc + i.width) top' mem' aw' acc' ex' k' C'
          (ok && Nat.ble req m) (pre ∧ p) hints' r h hok hp
        rw [Bool.and_eq_true] at hok'
        have hreq : req ≤ m := Nat.le_of_ble_eq_true hok'.2
        exact ⟨hok'.1, hpre.1, fun e =>
          hrun ⟨stepP_sound hs hpre.2 e.2.head (by omega) e.1, e.2.tail⟩⟩
      · exact absurd h (by simp)

/-- **The run is sound.**  `m` is the stack bound the block's statement assumes and `hints` the
gas spent before each `GAS`, as the statement writes it. -/
theorem RDL.run {ex : Bool} {pc : ℕ} {is : List Instr} {top : List UInt256} {mem : ByteArray}
    {aw : UInt256} {acc : AccountMap} {k C : ℕ} {pc' : ℕ} {rest : List Instr}
    {top' : List UInt256} {mem' : ByteArray} {aw' : UInt256} {acc' : AccountMap} {ex' : Bool}
    {k' C' : ℕ} {ok : Bool} {pre : Prop} {hints' : List ℕ}
    (e : RDL code σ ee g s0 ex pc is (top ++ R) mem aw rdata acc k C) (fuel : ℕ)
    (hints : List ℕ) (m : ℕ)
    (hr : run code ee g rdata σ m fuel is pc top mem aw acc ex k C true True hints
      = some ⟨pc', rest, top', mem', aw', acc', ex', k', C', ok, pre, hints'⟩)
    (hok : ok = true) (hstack : R.length + m ≤ 1024) (hpre : pre) :
    RDL code σ ee g s0 ex' pc' rest (top' ++ R) mem' aw' rdata acc' k' C' :=
  (run_sound (by omega) fuel is pc top mem aw acc ex k C true True hints _ hr hok hpre).2.2 e

/-! ## Entering and leaving a block -/

theorem decodes_drop : ∀ (j : ℕ) (s : List Instr) (t : ℕ), Decodes code σ t s →
    Decodes code σ (t + sectionWidth (s.take j)) (s.drop j)
  | 0, _, _, h => h
  | _ + 1, [], _, _ => trivial
  | j + 1, i :: s, t, h => by
    have := decodes_drop j s (t + i.width) h.tail
    simpa only [List.take_succ_cons, List.drop_succ_cons, sectionWidth, Nat.add_assoc] using this

/-- Enter at instruction `j` of a section that decodes from offset `t`. -/
theorem RDL.enter {t : ℕ} {s : List Instr} (hd : Decodes code σ t s) (j n : ℕ)
    (hn : t + sectionWidth (s.take j) = n) (top : List UInt256)
    {mem : ByteArray} {aw : UInt256} {acc : AccountMap} {k C : ℕ}
    (h : RD code ee g s0 (UInt256.ofNat n) (top ++ R) mem aw rdata acc k C) :
    RDL code σ ee g s0 true n (s.drop j) (top ++ R) mem aw rdata acc k C :=
  ⟨h, hn ▸ decodes_drop j s t hd⟩

variable {ex : Bool} {n : ℕ} {is : List Instr} {top : List UInt256} {mem : ByteArray}
  {aw : UInt256} {acc : AccountMap} {k C : ℕ}

/-- Leave without a jump: `RD` at the offset reached. -/
theorem RDL.rd {stk : List UInt256}
    (e : RDL code σ ee g s0 true n is stk mem aw rdata acc k C) :
    RD code ee g s0 (UInt256.ofNat n) stk mem aw rdata acc k C := e.1

theorem RDL.rdX {stk : List UInt256}
    (e : RDL code σ ee g s0 ex n is stk mem aw rdata acc k C) :
    ∃ k' C', RD code ee g s0 (UInt256.ofNat n) stk mem aw rdata acc k' C' := e.1.some

/-- Leave by a `JUMPI` that jumps. -/
theorem RDL.jumpiTX {a b : UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.StackMemFlow .JUMPI) :: is) ((a :: b :: top) ++ R)
      mem aw rdata acc k C)
    (hb : b ≠ ⟨0⟩) (hjd : (D_J code 0).contains a = true)
    (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDm code ee g s0 ex a (top ++ R) mem aw rdata acc (k + 1) (C + 10) :=
  RDm.exact (stk := a :: b :: (top ++ R)) e.1 (fun _ _ h => RD.jumpiT h e.2.head hb hjd
    (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega))

/-- Leave by a `JUMPI` that falls through. -/
theorem RDL.jumpiNTX {a b : UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.StackMemFlow .JUMPI) :: is) ((a :: b :: top) ++ R)
      mem aw rdata acc k C)
    (hb : b = ⟨0⟩) (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDm code ee g s0 ex (UInt256.ofNat (n + 1)) (top ++ R) mem aw rdata acc (k + 1) (C + 10) :=
  RDm.exact (stk := a :: b :: (top ++ R)) e.1 (fun _ _ h => by
    have r := RD.jumpiNT h e.2.head hb
      (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega)
    rwa [ofNat_add_one] at r)

/-- Leave by a `JUMP`. -/
theorem RDL.jumpX {a : UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.StackMemFlow .JUMP) :: is) ((a :: top) ++ R)
      mem aw rdata acc k C)
    (hjd : (D_J code 0).contains a = true)
    (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDm code ee g s0 ex a (top ++ R) mem aw rdata acc (k + 1) (C + 8) :=
  RDm.exact (stk := a :: (top ++ R)) e.1 (fun _ _ h => RD.jump h e.2.head hjd
    (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega))

/-- End in `REVERT`. -/
theorem RDL.rev {off len : UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.System .REVERT) :: is) ((off :: len :: top) ++ R)
      mem aw rdata acc k C)
    (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, h⟩ := e.1.some
  have h' : RD code ee g s0 (UInt256.ofNat n) (off :: len :: (top ++ R)) mem aw rdata acc _ _ := h
  exact RD.genRev h' e.2.head
    (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega)

/-- End in `RETURN`. -/
theorem RDL.ret {off len : UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.System .RETURN) :: is) ((off :: len :: top) ++ R)
      mem aw rdata acc k C)
    (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDret code g s0 acc (mem.readWithPadding off.toNat len.toNat) := by
  obtain ⟨_, _, h⟩ := e.1.some
  have h' : RD code ee g s0 (UInt256.ofNat n) (off :: len :: (top ++ R)) mem aw rdata acc _ _ := h
  exact RD.genRet h' e.2.head
    (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega)

/-- End in `STOP`. -/
theorem RDL.stop
    (e : RDL code σ ee g s0 ex n (.op (.StopArith .STOP) :: is) (top ++ R) mem aw rdata acc k C)
    (m : ℕ) (hm : Nat.ble top.length m = true) (hstack : R.length + m ≤ 1024) :
    RDret code g s0 acc ByteArray.empty := by
  obtain ⟨_, _, h⟩ := e.1.some
  exact RD.stop h e.2.head
    (by have := Nat.le_of_ble_eq_true hm; simp only [List.length_append]; omega)

/-- End in `INVALID`. -/
theorem RDL.invalid {stk : List UInt256}
    (e : RDL code σ ee g s0 ex n (.op (.System .INVALID) :: is) stk mem aw rdata acc k C) :
    RDinvalid code g s0 := by
  obtain ⟨_, _, h⟩ := e.1.some
  exact RD.invalid h e.2.head

end Sound

end Reasoning.Listing
