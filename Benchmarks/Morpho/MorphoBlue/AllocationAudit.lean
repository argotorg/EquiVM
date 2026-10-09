import Benchmarks.Morpho.MorphoBlue.Allocation
import Benchmarks.Morpho.MorphoBlue.Dispatch
import Reasoning.ABIComposite
import Benchmarks.Morpho.MorphoBlue.PackedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- Symbolic bytes: these proofs never evaluate or allocate the enormous suffix.
def allocationAuditBool (n : Nat) : ByteArray :=
  (UInt256.ofNat 1).toByteArray ++ ByteArray.zeroes (n - 32)

theorem allocationAuditBool_size {n : Nat} (hn : 32 ≤ n) :
    (allocationAuditBool n).size = n := by
  rw [allocationAuditBool, ByteArray.size_append, toByteArray_size, ByteArray_zeroes_size]
  omega

theorem allocationAuditBool_word (n : Nat) :
    calldataWord (allocationAuditBool n) 0 = UInt256.ofNat 1 := by
  have hs : 32 ≤ (allocationAuditBool n).size := by
    rw [allocationAuditBool, ByteArray.size_append, toByteArray_size]
    omega
  have hw := calldataWord_bytes hs
  rw [allocationAuditBool, extract_append_left _ _ _ _ (by rw [toByteArray_size]),
    show (UInt256.ofNat 1).toByteArray.extract 0 32 = (UInt256.ofNat 1).toByteArray
      from by simpa only [toByteArray_size] using
        (ByteArray.extract_zero_size (b := (UInt256.ofNat 1).toByteArray))] at hw
  simpa only [uInt256OfByteArray_toByteArray] using congrArg uInt256OfByteArray hw

theorem allocationAuditBool_decode {n : Nat} (hn : 32 ≤ n) (hb : n < 2 ^ 255) :
    ABI.decodeReturnValue? abiBool (allocationAuditBool n) = some (.bool true) := by
  rw [decodeReturnBool_long (by rw [allocationAuditBool_size hn]; exact hn)
    (by rw [allocationAuditBool_size hn]; exact hb), allocationAuditBool_word]
  decide

-- The memory gas needed for 2^64 returned bytes is well below the model's gas bound.
theorem allocationAudit_memoryCost :
    Cₘ (UInt256.ofNat ((2 ^ 64 + 31) / 32)) < 2 ^ 128 ∧
      (2 : Nat) ^ 128 < UInt256.size := by decide

-- This is a local post-call mismatch, not a refutation of runtimeRefinementFor:
-- no callee Θ invocation or complete public execution is assumed to exist here.
theorem allocationAudit_oversizeReverts {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem out : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hout : out.size = 2 ^ 64) (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_14548_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (by rw [hout]; decide) h
  have rd2 := morphoBlocks.morpho_block_14555_taken
    (immWords := wordsOf (immStore v)) hstack (by rw [hout]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega) rd2

theorem allocationAudit_uint64SizePasses :
    UInt256.gt (UInt256.ofNat (2 ^ 64 - 128))
      (UInt256.ofNat (2 ^ 64 - 1)) = UInt256.ofNat 0 := by decide

theorem allocationAudit_uint64SizeStillReverts {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem out : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hout : out.size = 2 ^ 64 - 128)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14548)
      (ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_14548_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
    (by rw [hout]; decide) h
  have rd2 := morphoBlocks.morpho_block_14555_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by rw [hout]; decide) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_14572_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  dsimp only [morphoBlocks.morpho_block_14572_stack,
    morphoBlocks.morpho_block_14555_fallthrough_stack] at rd3
  rw [hout, hfree] at rd3
  have rd4 := morphoBlocks.morpho_block_11535_taken
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
    (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 2 ≤ 1024; omega) rd4

-- LIBRARY CANDIDATE: a checked full-word increase preserves a nonzero upper half.
theorem halfWord_high_nonzero_of_le {x y : UInt256}
    (hle : x.toNat ≤ y.toNat) (hx : halfWord true x ≠ UInt256.ofNat 0) :
    halfWord true y ≠ UInt256.ofNat 0 := by
  intro hy
  have hy0 := congrArg UInt256.toNat hy
  have hx0 : (halfWord true x).toNat ≠ 0 := by
    intro he
    apply hx
    exact uint256_toNat_eq_zero he
  change (UInt256.shiftRight y ⟨128⟩).toNat = 0 at hy0
  change (UInt256.shiftRight x ⟨128⟩).toNat ≠ 0 at hx0
  rw [rpowShiftRight128_toNat] at hy0 hx0
  have hd := Nat.div_le_div_right hle (c := 2 ^ 128)
  omega

end Benchmarks.Morpho.MorphoBlue
