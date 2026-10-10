import Benchmarks.UniswapV4PoolManager.PoolKeyMemory
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_033
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolKeyDecodePrepareWords {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hlen : 164 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit) (hsize : I.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨11905⟩ (UInt256.ofNat I.calldata.size :: ret :: R)
      entryMemory aw rdata σ k C) :
    ∃ aw' k' C', aw'.toNat ≤ max aw.toNat 3 ∧ RD (deployedRuntime v) I g s0 ⟨11960⟩ (ret :: ⟨160⟩ :: R)
      poolKeyAllocationMemory aw' rdata σ k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_11905_fallthrough (by simp; omega)
    (viaIRStaticLenCheckOk (words := 5) hlen hhi hsize) h
  have rd2 := poolManagerBlocks.poolManager_block_11948 (by simp; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  change RD _ _ _ _ ⟨11794⟩ (memLoad ⟨64⟩ entryMemory :: ⟨11960⟩ :: ret :: memLoad ⟨64⟩ entryMemory :: R)
    entryMemory _ _ _ _ _ at rd2
  rw [entryMemory_load64] at rd2
  have rd3 := poolManagerBlocks.poolManager_block_11794_fallthrough (by simp; omega) (by native_decide) rd2
  obtain ⟨k4, C4, rd4⟩ := RD.pack (poolManagerBlocks.poolManager_block_11818 (by simp; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
  refine ⟨_, k4, C4, ?_, rd4⟩
  have hm : 3 ≤ max aw.toNat 3 := le_max_right _ _
  iterate 2 apply memoryWords_le
  · exact le_max_left _ _
  all_goals change 64+32 ≤ 32*max aw.toNat 3; omega

theorem decodePoolKeyTraceWords {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hlen : 164 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit) (hsize : I.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11905⟩ (UInt256.ofNat I.calldata.size :: ret :: R)
      entryMemory aw rdata σ k C) :
    (¬PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧ RDrev (deployedRuntime v) g s0) ∨
    (PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧ ∃ aw' k' C', aw'.toNat ≤ max aw.toNat 10 ∧
      RD (deployedRuntime v) I g s0 ret (⟨160⟩ :: R) (poolKeyMemory (poolKeyOfCalldata I.calldata))
        aw' rdata σ k' C') := by
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  obtain ⟨aw0, k0, C0, haw0, rd0⟩ := poolKeyDecodePrepareWords v hstack hlen hhi hsize h
  by_cases hc0 : (calldataWord I.calldata 4).toNat < 2^160
  · have rd1 := poolManagerBlocks.poolManager_block_11960_fallthrough (by simp; omega)
      (addressSubMask_zero hc0) rd0
    by_cases hc1 : (calldataWord I.calldata 36).toNat < 2^160
    · obtain ⟨k2, C2, rd2⟩ := RD.pack ( poolManagerBlocks.poolManager_block_11994_fallthrough
        (by simp; omega) (addressSubMask_zero hc1) rd1)
      by_cases hfee : (calldataWord I.calldata 68).toNat < 2^24
      · have hfeeClean : UInt256.land (calldataWord I.calldata 68) (UInt256.ofNat 16777215) =
            calldataWord I.calldata 68 := u256LandMaskCleanOfToNat _ _ rfl hfee
        obtain ⟨k3, C3, rd3⟩ := RD.pack ( poolManagerBlocks.poolManager_block_12028_fallthrough
          (by simp; omega) (u256_sub_eq_zero_iff_eq.mpr hfeeClean.symm) rd2)
        by_cases htick : int24Canonical (calldataWord I.calldata 100)
        · have htickClean : UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 100) =
              calldataWord I.calldata 100 := (signextend24_eq_iff _).2 htick
          obtain ⟨k4, C4, rd4⟩ := RD.pack ( poolManagerBlocks.poolManager_block_12048_fallthrough
            (by simp; omega) (u256_sub_eq_zero_iff_eq.mpr htickClean.symm) rd3)
          by_cases hhooks : (calldataWord I.calldata 132).toNat < 2^160
          · obtain ⟨k5, C5, rd5⟩ := RD.pack ( poolManagerBlocks.poolManager_block_12066_fallthrough
              (by simp; omega) (addressSubMask_zero hhooks) rd4)
            obtain ⟨k6, C6, rd6⟩ := RD.pack (poolManagerBlocks.poolManager_block_12104
              (by simp; omega) hret rd5)
            refine .inr ⟨⟨hc0, hc1, hfee, htick, hhooks⟩, _, k6, C6, ?_, rd6⟩
            have hm : 10 ≤ max aw.toNat 10 := le_max_right _ _
            have hbase : aw0.toNat ≤ max aw.toNat 10 := haw0.trans (max_le_max_left _ (by decide))
            clear * - hbase hm
            change (M (M (M (M (M aw0 ⟨160⟩ ⟨32⟩) ⟨192⟩ ⟨32⟩) ⟨224⟩ ⟨32⟩)
              ⟨256⟩ ⟨32⟩) ⟨288⟩ ⟨32⟩).toNat ≤ max aw.toNat 10
            iterate 5 apply memoryWords_le
            · exact hbase
            · change 160+32 ≤ 32*max aw.toNat 10; omega
            · change 192+32 ≤ 32*max aw.toNat 10; omega
            · change 224+32 ≤ 32*max aw.toNat 10; omega
            · change 256+32 ≤ 32*max aw.toNat 10; omega
            · change 288+32 ≤ 32*max aw.toNat 10; omega
          · obtain ⟨aw5, k5, C5, rd5⟩ := poolManagerBlocks.poolManager_block_12066_taken_packed
              (by simp; omega) (addressSubMask_nonzero hhooks) hjump rd4
            exact .inl ⟨fun hk => hhooks hk.2.2.2.2, emptyRevert v (by change R.length+6 ≤ 1024; omega) rd5⟩
        · have hbad : UInt256.sub (calldataWord I.calldata 100)
              (UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 100)) ≠ ⟨0⟩ := by
            apply u256_sub_ne_zero_of_ne
            exact fun he => htick ((signextend24_eq_iff _).1 he.symm)
          obtain ⟨aw4, k4, C4, rd4⟩ := poolManagerBlocks.poolManager_block_12048_taken_packed
            (by simp; omega) hbad hjump rd3
          exact .inl ⟨fun hk => htick hk.2.2.2.1, emptyRevert v (by change R.length+6 ≤ 1024; omega) rd4⟩
      · have hbad : UInt256.sub (calldataWord I.calldata 68)
            (UInt256.land (calldataWord I.calldata 68) (UInt256.ofNat 16777215)) ≠ ⟨0⟩ := by
          apply u256_sub_ne_zero_of_ne
          intro he
          exact hfee ((landMask_eq_iff _ _ rfl).1 he.symm)
        obtain ⟨aw3, k3, C3, rd3⟩ := poolManagerBlocks.poolManager_block_12028_taken_packed
          (by simp; omega) hbad hjump rd2
        exact .inl ⟨fun hk => hfee hk.2.2.1, emptyRevert v (by change R.length+6 ≤ 1024; omega) rd3⟩
    · obtain ⟨aw2, k2, C2, rd2⟩ := poolManagerBlocks.poolManager_block_11994_taken_packed
        (by simp; omega) (addressSubMask_nonzero hc1) hjump rd1
      exact .inl ⟨fun hk => hc1 hk.2.1, emptyRevert v (by change R.length+6 ≤ 1024; omega) rd2⟩
  · have rd1 := poolManagerBlocks.poolManager_block_11960_taken (by simp; omega)
      (addressSubMask_nonzero hc0) hjump rd0
    exact .inl ⟨fun hk => hc0 hk.1, emptyRevert v (by change R.length+6 ≤ 1024; omega) rd1⟩

end Benchmarks.UniswapV4PoolManager
