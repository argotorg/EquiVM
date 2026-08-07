import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopGuard
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopModel

/-!
# BLAKE2F positive-round loop invariant vocabulary

This file collects the model/memory/gas vocabulary for the arbitrary-round proof.  It is kept
separate from instruction traces:

* `positiveRoundModelState` is the pure state after `i` rounds;
* `memoryRepresentsVector` states that bytecode memory slots `v[0..15]` hold that state;
* `positiveRoundHeaderGas` is the exact cumulative gas recurrence at PC `1370`.

The recurrence is inferred from the compiled selector shape used by the completed unrolled
prefixes: a full loop-header-to-loop-header round costs
`3401 + 22 * (i % 10)`.  The `22 * (i % 10)` component is the linear cost of the SIGMA selector's
comparison chain before it reaches the packed word for residue `i % 10`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev hBaseOffset : Nat := 384

abbrev mBaseOffset : Nat := 640

abbrev tBaseOffset : Nat := 1152

abbrev vBaseOffset : Nat := 1472

abbrev wordBytes : Nat := 32

def hSlotOffset (i : Nat) : Nat := hBaseOffset + wordBytes * i

def mSlotOffset (i : Nat) : Nat := mBaseOffset + wordBytes * i

def tSlotOffset (i : Nat) : Nat := tBaseOffset + wordBytes * i

def vSlotOffset (i : Nat) : Nat := vBaseOffset + wordBytes * i

/-- Bytecode memory word read in the same 32-byte big-endian form as `MLOAD`. -/
def memoryWord (mem : ByteArray) (off : Nat) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off 32))

/-- Embed a model `UInt64` word into the bytecode's 256-bit word domain. -/
def u64AsWord (w : UInt64) : UInt256 :=
  UInt256.ofNat w.toNat

/-- A bytecode memory slot stores the given model word. -/
def memorySlotStoresU64 (mem : ByteArray) (off : Nat) (w : UInt64) : Prop :=
  memoryWord mem off = u64AsWord w

/-- Bytecode memory stores the parsed model `h` array. -/
def memoryRepresentsH (mem : ByteArray) (h : Array UInt64) : Prop :=
  h.size = 8 ∧ ∀ i, i < 8 → memorySlotStoresU64 mem (hSlotOffset i) h[i]!

/-- Bytecode memory stores the parsed model `m` array. -/
def memoryRepresentsM (mem : ByteArray) (m : Array UInt64) : Prop :=
  m.size = 16 ∧ ∀ i, i < 16 → memorySlotStoresU64 mem (mSlotOffset i) m[i]!

/-- Bytecode memory stores the two parsed model `t` words. -/
def memoryRepresentsT (mem : ByteArray) (t0 t1 : UInt64) : Prop :=
  memorySlotStoresU64 mem (tSlotOffset 0) t0 ∧
    memorySlotStoresU64 mem (tSlotOffset 1) t1

/-- Bytecode memory stores the working vector `v[0..15]`. -/
def memoryRepresentsVector (mem : ByteArray) (v : Array UInt64) : Prop :=
  v.size = 16 ∧ ∀ i, i < 16 → memorySlotStoresU64 mem (vSlotOffset i) v[i]!

/-- Pure model state after `i` compression rounds for a concrete input. -/
def positiveRoundModelState (input : ByteArray) (i : Nat) : Array UInt64 :=
  Model.roundsState (Model.parsedM input) i
    (Model.initialV (Model.parsedH input) (Model.parsedT0 input)
      (Model.parsedT1 input) (Model.parsedFinalFlag input))

theorem positiveRoundModelState_zero (input : ByteArray) :
    positiveRoundModelState input 0 =
      Model.initialV (Model.parsedH input) (Model.parsedT0 input)
        (Model.parsedT1 input) (Model.parsedFinalFlag input) := by
  simp [positiveRoundModelState]

theorem positiveRoundModelState_succ (input : ByteArray) (i : Nat) :
    positiveRoundModelState input (i + 1) =
      Model.roundStep (Model.parsedM input) i (positiveRoundModelState input i) := by
  simp [positiveRoundModelState, Model.roundsState_succ]

/-- Model-facing invariant at the bytecode rounds-loop header. -/
def positiveRoundHeaderInvariant (I : ExecutionEnv) (i : Nat) (mem : ByteArray) : Prop :=
  i ≤ Model.rounds I.calldata ∧
    mem.size = 1984 ∧
    memoryRepresentsH mem (Model.parsedH I.calldata) ∧
    memoryRepresentsM mem (Model.parsedM I.calldata) ∧
    memoryRepresentsT mem (Model.parsedT0 I.calldata) (Model.parsedT1 I.calldata) ∧
    memoryRepresentsVector mem (positiveRoundModelState I.calldata i)

theorem positiveRoundHeaderInvariant.index_le
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    i ≤ Model.rounds I.calldata :=
  h.1

theorem positiveRoundHeaderInvariant.mem_size
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    mem.size = 1984 :=
  h.2.1

theorem positiveRoundHeaderInvariant.representsH
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    memoryRepresentsH mem (Model.parsedH I.calldata) :=
  h.2.2.1

theorem positiveRoundHeaderInvariant.representsM
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    memoryRepresentsM mem (Model.parsedM I.calldata) :=
  h.2.2.2.1

theorem positiveRoundHeaderInvariant.representsT
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    memoryRepresentsT mem (Model.parsedT0 I.calldata) (Model.parsedT1 I.calldata) :=
  h.2.2.2.2.1

theorem positiveRoundHeaderInvariant.representsVector
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (h : positiveRoundHeaderInvariant I i mem) :
    memoryRepresentsVector mem (positiveRoundModelState I.calldata i) :=
  h.2.2.2.2.2

/-- Exact cumulative gas at the first rounds-loop header, before any positive round has run. -/
def positiveRoundSetupGas (finalFlagSet : Bool) : Nat :=
  if finalFlagSet then 7664 else 7637

/-- Exact gas from one loop header at index `i` to the next loop header at index `i + 1`. -/
def positiveRoundDelta (i : Nat) : Nat :=
  if i % 10 = 9 then
    3594
  else
    3401 + 22 * (i % 10)

/-- Exact cumulative gas at PC `1370` with loop index `i`. -/
def positiveRoundHeaderGas (finalFlagSet : Bool) : Nat → Nat
  | 0 => positiveRoundSetupGas finalFlagSet
  | i + 1 => positiveRoundHeaderGas finalFlagSet i + positiveRoundDelta i

/-- Exact cumulative gas after the loop guard exits or continues at PC `1370`. -/
def positiveRoundGuardGas (finalFlagSet : Bool) (i : Nat) : Nat :=
  positiveRoundHeaderGas finalFlagSet i + 23

@[simp] theorem positiveRoundHeaderGas_zero (finalFlagSet : Bool) :
    positiveRoundHeaderGas finalFlagSet 0 = positiveRoundSetupGas finalFlagSet := by
  rfl

@[simp] theorem positiveRoundHeaderGas_succ (finalFlagSet : Bool) (i : Nat) :
    positiveRoundHeaderGas finalFlagSet (i + 1) =
      positiveRoundHeaderGas finalFlagSet i + positiveRoundDelta i := by
  rfl

theorem positiveRoundHeaderGas_false_checkpoints :
    (List.range 8).map (positiveRoundHeaderGas false) =
      [7637, 11038, 14461, 17906, 21373, 24862, 28373, 31906] := by
  native_decide

theorem positiveRoundHeaderGas_true_checkpoints :
    (List.range 8).map (positiveRoundHeaderGas true) =
      [7664, 11065, 14488, 17933, 21400, 24889, 28400, 31933] := by
  native_decide

theorem positiveRoundGuardGas_false_checkpoints :
    (List.range 8).map (positiveRoundGuardGas false) =
      [7660, 11061, 14484, 17929, 21396, 24885, 28396, 31929] := by
  native_decide

theorem positiveRoundGuardGas_true_checkpoints :
    (List.range 8).map (positiveRoundGuardGas true) =
      [7687, 11088, 14511, 17956, 21423, 24912, 28423, 31956] := by
  native_decide

end Blake2f
