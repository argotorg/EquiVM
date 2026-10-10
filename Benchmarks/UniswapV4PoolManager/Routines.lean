import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.EntrySource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_033
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_032

/-! Shared PoolManager bytecode routines. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem addressSubMask_zero {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.sub w (UInt256.land w solcAddrMask) = ⟨0⟩ :=
  u256_sub_eq_zero_iff_eq.mpr (solcAddrMask_clean hcanon).symm

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem addressSubMask_nonzero {w : UInt256} (hnc : ¬ w.toNat < EVM.addressModulus) :
    UInt256.sub w (UInt256.land w solcAddrMask) ≠ ⟨0⟩ := by
  intro hz
  have h := solcAddrMask_result_canonical w
  rw [← u256_sub_eq_zero_iff_eq.mp hz] at h
  exact hnc h

theorem decodeAddress4 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11583⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rdValid := poolManagerBlocks.poolManager_block_11583_fallthrough hstack
    (addressSubMask_zero hcanon) h
  have rdReturn := poolManagerBlocks.poolManager_block_11617 (by simp; omega) hvalid rdValid
  exact ⟨_, _, rdReturn⟩

theorem decodeAddress4Reverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨11583⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  have rdRevert := poolManagerBlocks.poolManager_block_11583_taken hstack
    (addressSubMask_nonzero hnc) hjump h
  exact emptyRevert v (by simp [poolManagerBlocks.poolManager_block_11583_taken_stack]; omega) rdRevert

theorem decodeAddress36 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11618⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (calldataWord I.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  have rdValid := poolManagerBlocks.poolManager_block_11618_fallthrough hstack
    (addressSubMask_zero hcanon) h
  have rdReturn := poolManagerBlocks.poolManager_block_11652 (by simp; omega) hvalid rdValid
  exact ⟨_, _, rdReturn⟩

theorem decodeAddress36Reverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨11618⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  have rdRevert := poolManagerBlocks.poolManager_block_11618_taken hstack
    (addressSubMask_nonzero hnc) hjump h
  exact emptyRevert v (by simp [poolManagerBlocks.poolManager_block_11618_taken_stack]; omega) rdRevert

theorem decodeAddressUintUint {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hlen : 100 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11653⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (calldataWord I.calldata 68 :: calldataWord I.calldata 36 :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rdAddr := poolManagerBlocks.poolManager_block_11653_fallthrough
    (by simpa only [List.length_cons] using hstack)
    (viaIRStaticLenCheckOk (words := 3) hlen hhi hsize) h
  have rdReturn := poolManagerBlocks.poolManager_block_11696_fallthrough
    (by simpa only [List.length_cons] using hstack) (addressSubMask_zero hc) rdAddr
  have rdDone := poolManagerBlocks.poolManager_block_11728 hstack hret rdReturn
  exact ⟨_, _, rdDone⟩

theorem decodeAddressUintUintLengthReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hbad : UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.ofNat (UInt256.size - 4)) ⟨96⟩ ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨11653⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  have rdRevert := poolManagerBlocks.poolManager_block_11653_taken
    (by simpa only [List.length_cons] using hstack) hbad hjump h
  exact emptyRevert v (by change R.length + 1 + 2 ≤ 1024; omega) rdRevert

theorem decodeAddressUintUintAddressReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hlen : 100 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size)
    (hc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨11653⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rdAddr := poolManagerBlocks.poolManager_block_11653_fallthrough
    (by simpa only [List.length_cons] using hstack)
    (viaIRStaticLenCheckOk (words := 3) hlen hhi hsize) h
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  have rdRevert := poolManagerBlocks.poolManager_block_11696_taken
    (by simpa only [List.length_cons] using hstack) (addressSubMask_nonzero hc) hjump rdAddr
  exact emptyRevert v (by change R.length + 1 + 1 + 2 ≤ 1024; omega) rdRevert

end Benchmarks.UniswapV4PoolManager
