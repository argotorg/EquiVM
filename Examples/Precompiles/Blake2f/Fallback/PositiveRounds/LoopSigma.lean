import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopState
import Reasoning.EVMWord

/-!
# BLAKE2F positive-round SIGMA selector facts

The arbitrary-round proof should not grow by adding `Round7`, `Round8`, ... traces.  The compiled
selector is periodic with period `10`, matching the trusted model's `SIGMA[i % 10]` lookup.  This
file records the residue-parametric facts needed by a loop proof:

* the packed 64-bit selector word for round index `i`;
* the bytecode memory offset selected for each SIGMA entry;
* the exact selector-dependent gas component.

The concrete checkpoint theorems are intentionally derived from `Model.SIGMA`, not from the
round-specific trace constants.  This keeps the parametric layer tied to the trusted pure model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The model SIGMA nibble selected by bytecode round index `i` and nibble position `j`. -/
def sigmaNibble (i j : Nat) : Nat :=
  (Model.SIGMA[i % 10]!)[j]!

/-- Pack the sixteen 4-bit SIGMA entries in the same order as the compiled selector.

For residue `0` this is `0x0123456789abcdef`. -/
def sigmaPackedWordNat (i : Nat) : Nat :=
  (List.range 16).foldl (fun acc j => acc * 16 + sigmaNibble i j) 0

/-- Packed SIGMA word as an EVM stack word. -/
def sigmaPackedWord (i : Nat) : UInt256 :=
  UInt256.ofNat (sigmaPackedWordNat i)

/-- Bytecode `% 10` agrees with natural `% 10` for loop indices that cannot wrap as `UInt256`. -/
theorem u256_mod_ten_ofNat_of_lt {i : Nat} (hi : i < UInt256.size) :
    UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = UInt256.ofNat (i % 10) := by
  apply u256_inj
  unfold UInt256.mod UInt256.ofNat UInt256.toNat
  simp [Id.run]
  rw [Nat.mod_eq_of_lt hi]
  rw [Nat.mod_eq_of_lt (by decide : 10 < UInt256.size)]
  rw [Nat.mod_eq_of_lt (by omega : i % 10 < UInt256.size)]

/-- Bytecode memory offset for the model message word selected by `SIGMA[i % 10][j]`. -/
def sigmaMessageOffset (i j : Nat) : Nat :=
  mBaseOffset + wordBytes * sigmaNibble i j

/-- Bytecode memory offset for the selected message word as an EVM stack word. -/
def sigmaMessageOffsetWord (i j : Nat) : UInt256 :=
  UInt256.ofNat (sigmaMessageOffset i j)

/-- Exact gas from loop-body PC `1445` to the first shared `mixG` body at PC `1512`.

Residues `0..8` fall through the compiled SIGMA selector chain linearly.  Residue `9` is a
slightly shorter terminal branch: the bytecode compares against `9` without a final `DUP1` and its
target branch has no matching `POP`, saving `5` gas relative to the linear pattern. -/
def sigmaSelectorToMix0Gas (i : Nat) : Nat :=
  if i % 10 = 9 then
    361
  else
    168 + 22 * (i % 10)

/-- Gas after the guard and SIGMA/Mix0 argument selector, starting from a loop header. -/
def positiveRoundMix0EntryGas (finalFlagSet : Bool) (i : Nat) : Nat :=
  positiveRoundGuardGas finalFlagSet i + sigmaSelectorToMix0Gas i

/-- The residue-independent remainder of a full positive round after reaching PC `1512`. -/
def positiveRoundAfterMix0EntryGas : Nat :=
  3210

/-- Exact gas from loop-body PC `1445` to the next loop-header PC `1370`. -/
def positiveRoundBodyDelta (i : Nat) : Nat :=
  sigmaSelectorToMix0Gas i + positiveRoundAfterMix0EntryGas

/-- Shared `mixG` entry reached after the SIGMA selector and first message-argument setup. -/
abbrev positiveRoundMix0Pc : UInt256 := ⟨1512⟩

/-- Message word loaded by the positive-round selector for round index `i` and SIGMA position `j`. -/
def sigmaMessageLoad (mem : ByteArray) (i j : Nat) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (sigmaMessageOffset i j) 32))

/-- Uint64-masked message argument selected for round index `i` and SIGMA position `j`. -/
def sigmaMessageArg (mem : ByteArray) (i j : Nat) : UInt256 :=
  UInt256.land (sigmaMessageLoad mem i j) ⟨18446744073709551615⟩

/-- Stack at `positiveRoundMix0Pc` after the selector has prepared the first `mixG` arguments.

This is the arbitrary-index version of the concrete `RoundNSelector` stacks.  The selected
message arguments are `SIGMA[i % 10][1]` and `SIGMA[i % 10][0]`; the original loop index `i` is
preserved below the selector return metadata. -/
def positiveRoundMix0EntryStack (I : ExecutionEnv) (i : Nat) (mem : ByteArray) : List UInt256 :=
  [sigmaMessageArg mem i 1, sigmaMessageArg mem i 0, ⟨1693⟩, sigmaPackedWord i,
    ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundMix0EntryStack_length
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    (positiveRoundMix0EntryStack I i mem).length = 14 := by
  simp [positiveRoundMix0EntryStack]

theorem positiveRoundDelta_decompose (i : Nat) :
    positiveRoundDelta i = 23 + positiveRoundBodyDelta i := by
  unfold positiveRoundDelta positiveRoundBodyDelta sigmaSelectorToMix0Gas
    positiveRoundAfterMix0EntryGas
  split <;> omega

theorem positiveRoundHeaderGas_succ_decompose (finalFlagSet : Bool) (i : Nat) :
    positiveRoundHeaderGas finalFlagSet (i + 1) =
      positiveRoundGuardGas finalFlagSet i + positiveRoundBodyDelta i := by
  rw [positiveRoundHeaderGas_succ]
  unfold positiveRoundGuardGas
  rw [positiveRoundDelta_decompose]
  omega

theorem sigmaPackedWordNat_checkpoints :
    (List.range 10).map sigmaPackedWordNat =
      [81985529216486895,
        16881918945140062035,
        13312731748010193300,
        8733003861693448440,
        10400822202260547645,
        3200383143768358425,
        14204332651957162635,
        15816291393287259690,
        8064173457993569445,
        11710614767857974480] := by
  native_decide

theorem sigmaSelectorToMix0Gas_checkpoints :
    (List.range 10).map sigmaSelectorToMix0Gas =
      [168, 190, 212, 234, 256, 278, 300, 322, 344, 361] := by
  native_decide

theorem positiveRoundDelta_residue_checkpoints :
    (List.range 10).map positiveRoundDelta =
      [3401, 3423, 3445, 3467, 3489, 3511, 3533, 3555, 3577, 3594] := by
  native_decide

theorem sigmaFirstMessageOffset_checkpoints :
    (List.range 10).map (fun i => sigmaMessageOffset i 0) =
      [640, 1088, 992, 864, 928, 704, 1024, 1056, 832, 960] := by
  native_decide

theorem sigmaSecondMessageOffset_checkpoints :
    (List.range 10).map (fun i => sigmaMessageOffset i 1) =
      [672, 960, 896, 928, 640, 1024, 800, 992, 1120, 704] := by
  native_decide

theorem sigmaMessageOffset_lt_memory_size (i j : Nat) (hj : j < 16) :
    sigmaMessageOffset i j + wordBytes ≤ 1984 := by
  unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

theorem sigmaNibble_lt_16 (i j : Nat) (hj : j < 16) :
    sigmaNibble i j < 16 := by
  unfold sigmaNibble
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

end Blake2f
