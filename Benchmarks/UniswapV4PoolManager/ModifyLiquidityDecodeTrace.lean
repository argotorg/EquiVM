import Benchmarks.UniswapV4PoolManager.ModifyLiquidityABI
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityDecodeMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeBounds
import Benchmarks.UniswapV4PoolManager.Allocate128Trace
import Benchmarks.UniswapV4PoolManager.BytesSliceTrace
import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- Decode the pool key, liquidity parameters, and hook-data slice at the public entry. -/
theorem modifyLiquidityDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hlen : 324 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size) (haw : aw.toNat ≤ 10)
    (h : RD (deployedRuntime v) I g s0 ⟨5248⟩ R entryMemory aw rdata σ k C) :
    (¬ModifyLiquidityCalldataBounds I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (ModifyLiquidityCalldataBounds I.calldata ∧ ∃ aw' k' C', aw'.toNat ≤ 14 ∧ Cₘ aw' ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨5394⟩
        ([calldataWord I.calldata (modifyLiquidityDataStart I.calldata),
          UInt256.ofNat (modifyLiquidityDataStart I.calldata+32), ⟨160⟩, ⟨320⟩] ++ R)
        (modifyLiquidityDecodeMemory (poolKeyOfCalldata I.calldata)
          (modifyLiquidityOfCalldata I.calldata)) aw' rdata σ k' C') := by
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have rd1 := poolManagerBlocks.poolManager_block_5248 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases decodePoolKeyTraceWords v (by omega) (by omega) hhi hsize
      (by rw [deployedRuntime_jumps]; jump_dest) rd1 with
    ⟨hbad, hr⟩ | ⟨hk, aw1, k1, C1, haw1, rd2⟩
  · exact .inl ⟨fun hb => hbad hb.2.2.1, hr⟩
  have hparams : UInt256.slt (UInt256.ofNat I.calldata.size +
      UInt256.ofNat (UInt256.size-164)) (UInt256.ofNat 128) = ⟨0⟩ := by
    change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.sub ⟨0⟩ (UInt256.ofNat 164)) _ = _
    rw [wordAddNegSub]
    apply slt_lit_zero (by decide)
    · rw [usub_ofNat_lit_toNat (by omega) hsize]; omega
    · rw [usub_ofNat_lit_toNat (by omega) hsize]
      change I.calldata.size < 2^255+4 at hhi
      omega
  obtain ⟨k3, C3, rd3⟩ := RD.pack (poolManagerBlocks.poolManager_block_5256_fallthrough
    (by simp only [List.length_cons]; omega) hparams rd2)
  obtain ⟨k4, C4, rd4⟩ := RD.pack (poolManagerBlocks.poolManager_block_5299 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3)
  simp only [poolManagerBlocks.poolManager_block_5299_stack] at rd4
  rw [show memLoad (UInt256.ofNat 64) (poolKeyMemory (poolKeyOfCalldata I.calldata)) = ⟨320⟩
    from poolKeyMemory_load64 _] at rd4
  rcases allocate128CheckedTrace v (by simp only [List.length_cons]; omega)
      (by rw [deployedRuntime_jumps]; jump_dest) rd4 with ⟨hbad, _⟩ | ⟨_, rd5⟩
  · exact (hbad (by decide +kernel)).elim
  have haw5 : (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩).toNat ≤ 10 := by
    iterate 2 apply memoryWords_le
    · omega
    all_goals decide
  by_cases hl : int24Canonical (calldataWord I.calldata 164)
  swap
  · have hc : UInt256.sub (calldataWord I.calldata 164)
        (UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 164)) ≠ ⟨0⟩ := by
      apply u256_sub_ne_zero_of_ne
      exact fun he => hl ((signextend24_eq_iff _).1 he.symm)
    have hr := poolManagerBlocks.poolManager_block_5311_taken
      (by simp only [List.length_cons]; omega) hc hjump rd5
    exact .inl ⟨fun hb => hl hb.2.2.2.1.1,
      emptyRevert v (by change R.length+5 ≤ 1024; omega) hr⟩
  obtain ⟨k6, C6, rd6⟩ := RD.pack (poolManagerBlocks.poolManager_block_5311_fallthrough
    (by simp only [List.length_cons]; omega)
    (u256_sub_eq_zero_iff_eq.mpr ((signextend24_eq_iff _).2 hl).symm) rd5)
  by_cases hu : int24Canonical (calldataWord I.calldata 196)
  swap
  · have hc : UInt256.sub (calldataWord I.calldata 196)
        (UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 196)) ≠ ⟨0⟩ := by
      apply u256_sub_ne_zero_of_ne
      exact fun he => hu ((signextend24_eq_iff _).1 he.symm)
    have hr := poolManagerBlocks.poolManager_block_5325_taken (by omega) hc hjump rd6
    exact .inl ⟨fun hb => hu hb.2.2.2.1.2,
      emptyRevert v (by change R.length+5 ≤ 1024; omega) hr⟩
  obtain ⟨k7, C7, rd7⟩ := RD.pack (poolManagerBlocks.poolManager_block_5325_fallthrough (by omega)
    (u256_sub_eq_zero_iff_eq.mpr ((signextend24_eq_iff _).2 hu).symm) rd6)
  by_cases ho : (calldataWord I.calldata 292).toNat ≤ solcMaxU64
  swap
  · have hc : UInt256.gt (calldataWord I.calldata 292) (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < (calldataWord I.calldata 292).toNat
        from Nat.lt_of_not_ge ho)]
      decide
    have hr := poolManagerBlocks.poolManager_block_5340_taken (by omega) hc hjump rd7
    exact .inl ⟨fun hb => ho hb.2.2.2.2.1,
      emptyRevert v (by change R.length+5 ≤ 1024; omega) hr⟩
  obtain ⟨k8, C8, rd8⟩ := RD.pack (poolManagerBlocks.poolManager_block_5340_fallthrough
    (by omega) (ugt_zero ho) rd7)
  change RD _ _ _ _ ⟨5381⟩ (calldataWord I.calldata 292 :: ⟨160⟩ :: ⟨320⟩ :: R)
    (modifyLiquidityDecodeMemory (poolKeyOfCalldata I.calldata) (modifyLiquidityOfCalldata I.calldata))
    (M (M (M (M (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
      ⟨320⟩ ⟨32⟩) ⟨352⟩ ⟨32⟩) ⟨384⟩ ⟨32⟩) ⟨416⟩ ⟨32⟩) _ _ _ _ at rd8
  have haw8 : (M (M (M (M (M (M aw1 (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
      ⟨320⟩ ⟨32⟩) ⟨352⟩ ⟨32⟩) ⟨384⟩ ⟨32⟩) ⟨416⟩ ⟨32⟩).toNat ≤ 14 := by
    iterate 4 apply memoryWords_le
    · omega
    all_goals decide
  have rd9 := poolManagerBlocks.poolManager_block_5381 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd8
  have hs : (UInt256.ofNat 4+calldataWord I.calldata 292).toNat = modifyLiquidityDataStart I.calldata := by
    rw [uadd_toNat]
    change (4+(calldataWord I.calldata 292).toNat)%UInt256.size = 4+(calldataWord I.calldata 292).toNat
    exact Nat.mod_eq_of_lt (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  have hstart : (UInt256.ofNat 4+calldataWord I.calldata 292).toNat+solcMaxU64+32 < 2^255 := by
    rw [hs]
    change 4+(calldataWord I.calldata 292).toNat+(2^64-1)+32 < 2^255
    change _ ≤ 2^64-1 at ho
    omega
  rcases decodeBytesSlice v (by simp only [List.length_cons]; omega) hsize hstart
      (by rw [deployedRuntime_jumps]; jump_dest) rd9 with ⟨hbad, hr⟩ | ⟨hb, k10, C10, hcost, rd10⟩
  · exact .inl ⟨fun hh => hbad (hs ▸ hh.2.2.2.2.2), hr⟩
  rw [hs] at hb rd10
  have hsrc : (UInt256.ofNat 4+calldataWord I.calldata 292)+⟨32⟩ =
      UInt256.ofNat (modifyLiquidityDataStart I.calldata+32) := by
    apply u256_inj
    change ((UInt256.ofNat 4+calldataWord I.calldata 292)+UInt256.ofNat 32).toNat = _
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hs]; have hh := hb.2.2.2; omega), hs,
      UInt256.toNat_ofNat_of_lt (by have hh := hb.2.2.2; omega)]
  rw [hsrc] at rd10
  refine .inr ⟨⟨hlen, hb.1, hk, ⟨hl, hu⟩, ho, hb⟩, _, k10, C10, haw8, ?_, rd10⟩
  have hm := memoryCost_mono (b := ⟨14⟩) haw8
  have hc : Cₘ (⟨14⟩ : UInt256) = 42 := by decide +kernel
  omega

end Benchmarks.UniswapV4PoolManager
