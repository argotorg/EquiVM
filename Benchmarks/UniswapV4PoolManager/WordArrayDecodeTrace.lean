import Benchmarks.UniswapV4PoolManager.WordArrayDecode
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_034
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: natural-to-word conversion commutes with modular addition.
theorem ofNat_add_words (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  change (a % UInt256.size + b % UInt256.size) % UInt256.size = (a + b) % UInt256.size
  exact (Nat.add_mod _ _ _).symm

-- GENERALIZES array_end_bound_of_ugt_zero to expose the non-wrapping address itself.
theorem wordArrayEnd_toNat {off len : UInt256}
    (ho : off.toNat ≤ solcMaxU64) (hn : len.toNat ≤ solcMaxU64) :
    ((off + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 36).toNat =
      off.toNat + 32 * len.toNat + 36 := by
  have hfit : off.toNat + 32 * len.toNat + 36 < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at ho hn ⊢; omega
  have hs : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32 * len.toNat) := by
    simpa only [u256_ofNat_toNat] using (shiftLeft5_ofNat_eq (n := len.toNat) (by omega))
  have he : (off + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 36 =
      UInt256.ofNat (off.toNat + 32 * len.toNat + 36) := by
    conv_lhs => rw [← u256_ofNat_toNat off, hs, ofNat_add_words, ofNat_add_words]
  rw [he, UInt256.toNat_ofNat_of_lt hfit]

/-- Shared dynamic word-array decoder, used by both storage array entry points. -/
theorem decodeWordArray {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw ret : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hs : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12155⟩
      (UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ WordArrayBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (WordArrayBounds ee.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ret
        (calldataWord ee.calldata (4 + (calldataWord ee.calldata 4).toNat) ::
         UInt256.ofNat (36 + (calldataWord ee.calldata 4).toNat) :: R)
        mem aw rdata σ k' C') := by
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  by_cases hshort : ee.calldata.size < 36
  · have hc := viaIRStaticLenCheckShort (words := 1) hs hshort (by decide) hsize
    have rd := poolManagerBlocks.poolManager_block_12155_taken (by omega)
      (by
        change UInt256.slt (UInt256.ofNat ee.calldata.size + UInt256.ofNat (UInt256.size - 4)) (UInt256.ofNat (32 * 1)) ≠ ⟨0⟩
        rw [hc]; decide) hjump h
    exact .inl ⟨by intro hb; exact (Nat.not_lt_of_ge hb.1) hshort,
      emptyRevert v (by change R.length + 2 + 2 ≤ 1024; omega) rd⟩
  by_cases hhuge : 2 ^ 255 + 4 ≤ ee.calldata.size
  · have hc := viaIRStaticLenCheckHuge (words := 1) hhuge hsize (by decide)
    have rd := poolManagerBlocks.poolManager_block_12155_taken (by omega)
      (by
        change UInt256.slt (UInt256.ofNat ee.calldata.size + UInt256.ofNat (UInt256.size - 4)) (UInt256.ofNat (32 * 1)) ≠ ⟨0⟩
        rw [hc]; decide) hjump h
    exact .inl ⟨by intro hb; have := hb.2.1; omega,
      emptyRevert v (by change R.length + 2 + 2 ≤ 1024; omega) rd⟩
  have hc := viaIRStaticLenCheckOk (words := 1) (by omega) (by omega) hsize
  have rd0 := poolManagerBlocks.poolManager_block_12155_fallthrough (by omega) hc h
  change RD _ _ _ _ _ (ret :: UInt256.ofNat ee.calldata.size :: R) _ _ _ _ _ _ at rd0
  let off := calldataWord ee.calldata 4
  let len := calldataWord ee.calldata (4 + off.toNat)
  by_cases ho : off.toNat ≤ solcMaxU64
  swap
  · have rd := poolManagerBlocks.poolManager_block_12199_taken (by simp; omega) (by
        change UInt256.gt off (UInt256.ofNat 18446744073709551615) ≠ UInt256.ofNat 0
        rw [ugt_one (show (UInt256.ofNat 18446744073709551615).toNat < off.toNat from Nat.lt_of_not_ge ho)]
        decide) hjump rd0
    exact .inl ⟨fun hb ↦ ho hb.2.2.1,
      emptyRevert v (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  have rd1 := poolManagerBlocks.poolManager_block_12199_fallthrough
    (by simp; omega) (ugt_zero ho) rd0
  change RD _ _ _ _ _ (off :: ret :: UInt256.ofNat ee.calldata.size :: R) _ _ _ _ _ _ at rd1
  have hof : (off + UInt256.ofNat 35).toNat = off.toNat + 35 :=
    uadd_word_ofNat_toNat off 35 (by norm_num [solcMaxU64, UInt256.size] at ho ⊢; omega)
  have hos : (off + UInt256.ofNat 35).toNat < 2 ^ 255 := by
    rw [hof]; norm_num [solcMaxU64] at ho; omega
  by_cases hh : ee.calldata.size < 2 ^ 255
  swap
  · have hz := slt_zero_low_high hos (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega)
    have rd := poolManagerBlocks.poolManager_block_12217_taken (by omega)
      (by rw [hz]; decide) hjump rd1
    exact .inl ⟨fun hb ↦ hh hb.2.1,
      emptyRevert v (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  by_cases hlw : 4 + off.toNat + 32 ≤ ee.calldata.size
  swap
  · have hz := slt_lit_zero hh (by rw [hof]; omega) hos
    have rd := poolManagerBlocks.poolManager_block_12217_taken (by omega)
      (by rw [hz]; decide) hjump rd1
    exact .inl ⟨fun hb ↦ hlw hb.2.2.2.1,
      emptyRevert v (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  have hone := slt_lit_one_low hh (by rw [hof]; omega)
  have rd2 := poolManagerBlocks.poolManager_block_12217_fallthrough (by omega)
    (by rw [hone]; rfl) rd1
  have hload : uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + off).toNat 32) =
      len := by
    change uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + off).toNat 32) = len
    rw [add4_word_toNat off ho]
  by_cases hn : len.toNat ≤ solcMaxU64
  swap
  · have rd := poolManagerBlocks.poolManager_block_12228_taken (by omega) (by
        rw [hload, ugt_one (show (UInt256.ofNat 18446744073709551615).toNat < len.toNat from Nat.lt_of_not_ge hn)]
        decide) hjump rd2
    exact .inl ⟨fun hb ↦ hn hb.2.2.2.2.1,
      emptyRevert v (by change R.length + 4 + 2 ≤ 1024; omega) rd⟩
  have rd3 := poolManagerBlocks.poolManager_block_12228_fallthrough
    (by omega) (by rw [hload]; exact ugt_zero hn) rd2
  change RD _ _ _ _ _ (UInt256.ofNat ee.calldata.size :: off :: ret ::
    uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + off).toNat 32) :: R)
    _ _ _ _ _ _ at rd3
  rw [hload] at rd3
  have hend := wordArrayEnd_toNat ho hn
  by_cases hp : 4 + off.toNat + 32 + 32 * len.toNat ≤ ee.calldata.size
  swap
  · have rd := poolManagerBlocks.poolManager_block_12249_taken (by omega)
      (by rw [ugt_one (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)]; decide) hjump rd3
    exact .inl ⟨fun hb ↦ hp hb.2.2.2.2.2,
      emptyRevert v (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  have rd4 := poolManagerBlocks.poolManager_block_12249_fallthrough (by omega)
    (ugt_zero (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)) rd3
  have rd5 := poolManagerBlocks.poolManager_block_12263 (by omega) hret rd4
  have hoff : UInt256.ofNat 36 + off = UInt256.ofNat (36 + off.toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat off, ofNat_add_words]
  refine .inr ⟨⟨by omega, hh, ho, hlw, hn, hp⟩, k + 9 + 7 + 8 + 10 + 10 + 5,
    C + 32 + 28 + 31 + 37 + 37 + 20, ?_⟩
  simpa only [poolManagerBlocks.poolManager_block_12263_stack, hoff] using rd5

end Benchmarks.UniswapV4PoolManager
