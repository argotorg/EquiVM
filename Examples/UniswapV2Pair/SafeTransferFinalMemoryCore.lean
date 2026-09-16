import Examples.UniswapV2Pair.SafeTransferReturnCore
import Examples.UniswapV2Pair.SafeTransferReturnCases
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem safeTransferDynamicFinalMemory_invariants_of_zeroSlot {base : ByteArray} (aw ptr toWord value : UInt256) (out : ByteArray)
    (hin : 96 ≤ base.size) (hgap : ptr.toNat - base.size < USize.size)
    (hptrLo : 128 ≤ ptr.toNat) (hbase : base.size ≤ ptr.toNat + 132)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 355 < UInt256.size)
    (hzero : (safeTransferDynamicCallMem2 base ptr toWord value).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray) :
    ∃ next : UInt256,
      128 ≤ (safeTransferDynamicFinalMem base ptr toWord value out).size ∧
      next.toNat - (safeTransferDynamicFinalMem base ptr toWord value out).size < USize.size ∧
      128 ≤ next.toNat ∧ (safeTransferDynamicFinalMem base ptr toWord value out).size ≤ next.toNat + 132 ∧
      next.toNat ≤ ptr.toNat + out.size + 227 ∧
      (safeTransferDynamicFinalWords aw ptr out).toNat * 32 < UInt256.size ∧
      128 ≤ (safeTransferDynamicFinalWords aw ptr out).toNat * 32 ∧
      (safeTransferDynamicFinalMem base ptr toWord value out).readWithPadding 64 32 = next.toByteArray ∧
      (safeTransferDynamicFinalMem base ptr toWord value out).readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray := by
  have hp164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have hs0 := safeTransferDynamicCallMem2_size ptr toWord value (by omega) hgap (by omega)
  rw [Nat.max_eq_right (by omega : base.size ≤ ptr.toNat + 260)] at hs0
  have hread0 := safeTransferDynamicCallMem2_read64 ptr toWord value (by omega) hgap (by omega) (by omega)
  have hread96 := hzero
  obtain ⟨_, _, hb0, hc0⟩ := safeTransferDynamicCallWords_bounds aw ptr haw (by omega)
  by_cases he : out.size = 0
  · simp only [safeTransferDynamicFinalMem, safeTransferDynamicFinalWords, he, ite_true]
    refine Exists.intro (ptr + (⟨164⟩ : UInt256)) ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, hb0, ?_, hread0, hread96⟩
    · rw [hs0]; omega
    · rw [hs0, hp164]
      have hu : 0 < USize.size := lt_usize 0 (by omega)
      omega
    · rw [hp164]; omega
    · rw [hs0, hp164]; omega
    · rw [hp164]; omega
    · omega
  · simp only [safeTransferDynamicFinalMem, safeTransferDynamicFinalWords, he, ite_false]
    have hs := solcReturnDataMem_size (mem := safeTransferDynamicCallMem2 base ptr toWord value) (ptr + ⟨164⟩) out
      (by rw [hs0]; omega) (by rw [hs0, hp164]; omega) (by rw [hp164]; omega)
    rw [hs0, hp164] at hs
    have hround := solcReturnDataRounded_toNat out.size (by omega)
    have hroundLe : (out.size + 63) / 32 * 32 ≤ out.size + 63 := Nat.div_mul_le_self _ _
    have hroundGe : out.size + 32 ≤ (out.size + 63) / 32 * 32 := by
      have hmod := Nat.mod_lt (out.size + 63) (by omega : 0 < 32)
      have hsum := Nat.div_add_mod (out.size + 63) 32
      omega
    let next := (ptr + ⟨164⟩) + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)
    have hp : next.toNat = ptr.toNat + 164 + (out.size + 63) / 32 * 32 := by
      dsimp only [next]
      rw [uadd_toNat, hp164, hround, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨hbAw, hgeAw⟩ := solcReturnDataActiveWords_bounds (safeTransferDynamicCallWords2 aw ptr) (ptr + ⟨164⟩) out
      hb0 (by rw [hp164]; omega)
    refine ⟨next, ?_, ?_, ?_, ?_, ?_, hbAw, ?_, ?_, ?_⟩
    · rw [hs]; omega
    · rw [hp, hs]
      have hu : 31 < USize.size := lt_usize 31 (by omega)
      omega
    · rw [hp]; omega
    · rw [hp, hs]; omega
    · rw [hp]; omega
    · omega
    · have h := solcReturnDataMem_read64 (mem := safeTransferDynamicCallMem2 base ptr toWord value) (ptr + ⟨164⟩) out
        (by rw [hs0]; omega) (by rw [hs0, hp164]; omega) (by rw [hp164]; omega) (by rw [hp164]; omega)
      exact h
    · rw [solcReturnDataMem_read96 (ptr + ⟨164⟩) out (by rw [hs0]; omega)
        (by rw [hs0, hp164]; omega) (by rw [hp164]; omega) (by rw [hp164]; omega)]
      exact hread96

end UniswapV2Pair
