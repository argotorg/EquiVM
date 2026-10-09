import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.BodyCommon

/-! Shared Morpho bytecode routines. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

theorem morphoDecodeAddress196Ok {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hcanon : (calldataWord ee.calldata 196).toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11389)
      (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (calldataWord ee.calldata 196 :: R) mem aw rdata σ k' C' := by
  have rd := morphoBlocks.morpho_block_11389_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord ee.calldata 196)
        (UInt256.land (calldataWord ee.calldata 196) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean hcanon, u256_sub_self]) h
  exact ⟨_, _, morphoBlocks.morpho_block_11423
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hvalid rd⟩

theorem morphoDecodeAddress196Revert {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hnc : ¬ (calldataWord ee.calldata 196).toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11389)
      (ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd := morphoBlocks.morpho_block_11389_taken
    (immWords := wordsOf (immStore v)) hstack (addressMaskSub_nonzero hnc)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_11389_taken_stack, List.length_cons]; omega) rd

end Benchmarks.Morpho.MorphoBlue
