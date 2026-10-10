import Benchmarks.UniswapV4PoolManager.SwapABI
import Benchmarks.UniswapV4PoolManager.SwapDecodeMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeBounds
import Benchmarks.UniswapV4PoolManager.Allocate96Trace
import Benchmarks.UniswapV4PoolManager.BytesSliceTrace
import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hlen : 292 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size) (haw : aw.toNat ≤ 10)
    (h : RD (deployedRuntime v) I g s0 ⟨1328⟩ R entryMemory aw rdata σ k C) :
    (¬SwapCalldataBounds I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (SwapCalldataBounds I.calldata ∧ ∃ aw' k' C', aw'.toNat ≤ 13 ∧ Cₘ aw' ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨1488⟩
        ([calldataWord I.calldata (swapDataStart I.calldata),
          UInt256.ofNat (swapDataStart I.calldata+32), ⟨160⟩, ⟨384⟩, ⟨352⟩, ⟨320⟩] ++ R)
        (swapDecodeMemory (poolKeyOfCalldata I.calldata) (swapParamsOfCalldata I.calldata))
        aw' rdata σ k' C') := by
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have rd1 := poolManagerBlocks.poolManager_block_1328 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases decodePoolKeyTraceWords v (by omega) (by omega) hhi hsize
      (by rw [deployedRuntime_jumps]; jump_dest) rd1 with
    ⟨hbad, hr⟩ | ⟨hk, aw1, k1, C1, haw1, rd2⟩
  · exact .inl ⟨fun hb => hbad hb.2.2.1, hr⟩
  have hparams : UInt256.slt (UInt256.ofNat I.calldata.size+
      UInt256.ofNat (UInt256.size-164)) (UInt256.ofNat 96) = ⟨0⟩ := by
    change UInt256.slt (UInt256.ofNat I.calldata.size+UInt256.sub ⟨0⟩ (UInt256.ofNat 164)) _ = _
    rw [wordAddNegSub]
    apply slt_lit_zero (by decide)
    · rw [usub_ofNat_lit_toNat (by omega) hsize]; omega
    · rw [usub_ofNat_lit_toNat (by omega) hsize]
      change I.calldata.size < 2^255+4 at hhi
      omega
  obtain ⟨k3, C3, rd3⟩ := RD.pack (poolManagerBlocks.poolManager_block_1336_fallthrough
    (by simp only [List.length_cons]; omega) hparams rd2)
  obtain ⟨k4, C4, rd4⟩ := RD.pack (poolManagerBlocks.poolManager_block_1379 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
  simp only [poolManagerBlocks.poolManager_block_1379_stack] at rd4
  rw [show memLoad (UInt256.ofNat 64) (poolKeyMemory (poolKeyOfCalldata I.calldata)) = ⟨320⟩
    from poolKeyMemory_load64 _] at rd4
  have rd5 := allocate96CostTrace v (by simp only [List.length_cons]; omega) (by decide)
    (by rw [deployedRuntime_jumps]; jump_dest) rd4
  have haw5 : (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩).toNat ≤ 10 := by
    iterate 2 apply memoryWords_le
    · omega
    all_goals decide
  by_cases hz : calldataWord I.calldata 164 = ⟨0⟩ ∨ calldataWord I.calldata 164 = ⟨1⟩
  swap
  · have hr := poolManagerBlocks.poolManager_block_1391_taken
      (by simp only [List.length_cons]; omega) (boolSubNormalize_nonzero hz) hjump rd5
    exact .inl ⟨fun hb => hz hb.2.2.2.1.1,
      emptyRevert v (by change R.length+5 ≤ 1024; omega) hr⟩
  obtain ⟨k6, C6, rd6⟩ := RD.pack (poolManagerBlocks.poolManager_block_1391_fallthrough
    (by simp only [List.length_cons]; omega) (boolSubNormalize_zero hz) rd5)
  by_cases hp : (calldataWord I.calldata 228).toNat < 2^160
  swap
  · have hr := poolManagerBlocks.poolManager_block_1404_taken (by omega)
      (addressSubMask_nonzero hp) hjump rd6
    exact .inl ⟨fun hb => hp hb.2.2.2.1.2,
      emptyRevert v (by change R.length+6 ≤ 1024; omega) hr⟩
  obtain ⟨k7, C7, rd7⟩ := RD.pack (poolManagerBlocks.poolManager_block_1404_fallthrough
    (by omega) (addressSubMask_zero hp) rd6)
  by_cases ho : (calldataWord I.calldata 260).toNat ≤ solcMaxU64
  swap
  · have hc : UInt256.gt (calldataWord I.calldata 260) (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < (calldataWord I.calldata 260).toNat
        from Nat.lt_of_not_ge ho)]
      decide
    have hr := poolManagerBlocks.poolManager_block_1449_taken (by omega) hc hjump rd7
    exact .inl ⟨fun hb => ho hb.2.2.2.2.1,
      emptyRevert v (by change R.length+7 ≤ 1024; omega) hr⟩
  obtain ⟨k8, C8, rd8⟩ := RD.pack (poolManagerBlocks.poolManager_block_1449_fallthrough
    (by omega) (ugt_zero ho) rd7)
  have hbool := canonicalBoolWord hz
  change RD _ _ _ _ ⟨1475⟩ (calldataWord I.calldata 260 :: ⟨160⟩ :: ⟨384⟩ :: ⟨352⟩ :: ⟨320⟩ :: R)
    (wordSequenceMemory (writeWord (poolKeyMemory (poolKeyOfCalldata I.calldata)) 64 ⟨416⟩) 320
      [calldataWord I.calldata 164, calldataWord I.calldata 196, calldataWord I.calldata 228])
    (M (M (M (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
      ⟨320⟩ ⟨32⟩) ⟨352⟩ ⟨32⟩) ⟨384⟩ ⟨32⟩) _ _ _ _ at rd8
  rw [← hbool] at rd8
  have haw8 : (M (M (M (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
      ⟨320⟩ ⟨32⟩) ⟨352⟩ ⟨32⟩) ⟨384⟩ ⟨32⟩).toNat ≤ 13 := by
    iterate 3 apply memoryWords_le
    · omega
    all_goals decide
  have rd9 := poolManagerBlocks.poolManager_block_1475 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd8
  simp only [poolManagerBlocks.poolManager_block_1475_stack] at rd9
  have hs : (UInt256.ofNat 4+calldataWord I.calldata 260).toNat = swapDataStart I.calldata := by
    rw [uadd_toNat]
    change (4+(calldataWord I.calldata 260).toNat)%UInt256.size = 4+(calldataWord I.calldata 260).toNat
    exact Nat.mod_eq_of_lt (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  have hstart : (UInt256.ofNat 4+calldataWord I.calldata 260).toNat+solcMaxU64+32 < 2^255 := by
    rw [hs]
    change 4+(calldataWord I.calldata 260).toNat+(2^64-1)+32 < 2^255
    change _ ≤ 2^64-1 at ho
    omega
  rcases decodeBytesSlice (ret := UInt256.ofNat 1488)
      (R := [UInt256.ofNat 160, UInt256.ofNat 384, UInt256.ofNat 352, UInt256.ofNat 320]++R) v
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hsize hstart
      (by rw [deployedRuntime_jumps]; jump_dest) rd9 with ⟨hbad, hr⟩ | ⟨hb, k10, C10, hcost, rd10⟩
  · exact .inl ⟨fun hh => hbad (hs ▸ hh.2.2.2.2.2), hr⟩
  rw [hs] at hb rd10
  have hsrc : (UInt256.ofNat 4+calldataWord I.calldata 260)+⟨32⟩ =
      UInt256.ofNat (swapDataStart I.calldata+32) := by
    apply u256_inj
    change ((UInt256.ofNat 4+calldataWord I.calldata 260)+UInt256.ofNat 32).toNat = _
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hs]; have hh := hb.2.2.2; omega), hs,
      UInt256.toNat_ofNat_of_lt (by have hh := hb.2.2.2; omega)]
  rw [hsrc] at rd10
  refine .inr ⟨⟨hlen, hb.1, hk, ⟨hz, hp⟩, ho, hb⟩, _, k10, C10, haw8, ?_, ?_⟩
  swap
  · simpa only [swapDecodeMemory, swapParamsOfCalldata, swapParamsWordList] using rd10
  have hm := memoryCost_mono (b := ⟨13⟩) haw8
  have hc : Cₘ (⟨13⟩ : UInt256) = 39 := by decide +kernel
  omega

end Benchmarks.UniswapV4PoolManager
