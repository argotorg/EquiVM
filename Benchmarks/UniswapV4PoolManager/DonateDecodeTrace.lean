import Benchmarks.UniswapV4PoolManager.DonateABI
import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeBounds
import Benchmarks.UniswapV4PoolManager.BytesSliceTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_028

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hlen : 260 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit)
    (hsize : I.calldata.size < UInt256.size) (haw : aw.toNat ≤ 10)
    (h : RD (deployedRuntime v) I g s0 ⟨10029⟩ R entryMemory aw rdata σ k C) :
    (¬DonateCalldataBounds I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (DonateCalldataBounds I.calldata ∧ ∃ aw' k' C', aw'.toNat ≤ 10 ∧ Cₘ aw' ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨10076⟩
        ([calldataWord I.calldata (donateDataStart I.calldata),
          UInt256.ofNat (donateDataStart I.calldata+32), calldataWord I.calldata 164, ⟨160⟩, calldataWord I.calldata 196] ++ R)
        (poolKeyMemory (poolKeyOfCalldata I.calldata))
        aw' rdata σ k' C') := by
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have rd1 := poolManagerBlocks.poolManager_block_10029 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases decodePoolKeyTraceWords v (by omega) (by omega) hhi hsize
      (by rw [deployedRuntime_jumps]; jump_dest) rd1 with
    ⟨hbad, hr⟩ | ⟨hk, aw1, k1, C1, haw1, rd2⟩
  · exact .inl ⟨fun hb => hbad hb.2.2.1, hr⟩
  by_cases ho : (calldataWord I.calldata 228).toNat ≤ solcMaxU64
  swap
  · have hc : UInt256.gt (calldataWord I.calldata 228) (UInt256.ofNat solcMaxU64) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < (calldataWord I.calldata 228).toNat
        from Nat.lt_of_not_ge ho)]
      decide
    have hr := poolManagerBlocks.poolManager_block_10037_taken (by omega) hc hjump rd2
    exact .inl ⟨fun hb => ho hb.2.2.2.1,
      emptyRevert v (by change R.length+6 ≤ 1024; omega) hr⟩
  obtain ⟨k8, C8, rd8⟩ := RD.pack (poolManagerBlocks.poolManager_block_10037_fallthrough
    (by omega) (ugt_zero ho) rd2)
  have rd9 := poolManagerBlocks.poolManager_block_10063 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd8
  simp only [poolManagerBlocks.poolManager_block_10063_stack] at rd9
  have hs : (UInt256.ofNat 4+calldataWord I.calldata 228).toNat = donateDataStart I.calldata := by
    rw [uadd_toNat]
    change (4+(calldataWord I.calldata 228).toNat)%UInt256.size = 4+(calldataWord I.calldata 228).toNat
    exact Nat.mod_eq_of_lt (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  have hstart : (UInt256.ofNat 4+calldataWord I.calldata 228).toNat+solcMaxU64+32 < 2^255 := by
    rw [hs]
    change 4+(calldataWord I.calldata 228).toNat+(2^64-1)+32 < 2^255
    change _ ≤ 2^64-1 at ho
    omega
  rcases decodeBytesSlice (ret := UInt256.ofNat 10076)
      (R := [calldataWord I.calldata 164, UInt256.ofNat 160, calldataWord I.calldata 196]++R) v
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hsize hstart
      (by rw [deployedRuntime_jumps]; jump_dest) rd9 with ⟨hbad, hr⟩ | ⟨hb, k10, C10, hcost, rd10⟩
  · exact .inl ⟨fun hh => hbad (hs ▸ hh.2.2.2.2), hr⟩
  rw [hs] at hb rd10
  have hsrc : (UInt256.ofNat 4+calldataWord I.calldata 228)+⟨32⟩ =
      UInt256.ofNat (donateDataStart I.calldata+32) := by
    apply u256_inj
    change ((UInt256.ofNat 4+calldataWord I.calldata 228)+UInt256.ofNat 32).toNat = _
    rw [uadd_word_ofNat_toNat _ 32 (by rw [hs]; have hh := hb.2.2.2; omega), hs,
      UInt256.toNat_ofNat_of_lt (by have hh := hb.2.2.2; omega)]
  rw [hsrc] at rd10
  have haw10 : aw1.toNat ≤ 10 := by omega
  refine .inr ⟨⟨hlen, hb.1, hk, ho, hb⟩, _, k10, C10, haw10, ?_, rd10⟩
  have hm := memoryCost_mono (b := ⟨10⟩) haw10
  have hc : Cₘ (⟨10⟩ : UInt256) = 30 := by decide +kernel
  omega

end Benchmarks.UniswapV4PoolManager
