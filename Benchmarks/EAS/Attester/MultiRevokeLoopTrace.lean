import Benchmarks.EAS.Attester.MultiRevokeRowTrace
import Benchmarks.EAS.Attester.MultiRevokeRowView
import Benchmarks.EAS.Attester.NestedBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokeOuterSteps {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i remaining schemaPtr : Nat} {secondData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([UInt256.ofNat i, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw out σ k C)
    (hstack : R.length + 19 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hi : i + remaining ≤ n)
    (hf : free + (96 + 160 * solcMaxU64) * remaining < UInt256.size)
    (hsign : I.calldata.size < 2 ^ 255)
    (hsecond : secondData.toNat + 32 * n ≤ I.calldata.size)
    (hcd : schemaPtr + 32 * n < UInt256.size)
    (hrows : ∀ j, i ≤ j → j < i + remaining → RowValid I.calldata secondData j) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([UInt256.ofNat (i + remaining), UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R)
      (multiRevokeRowsMemory mem I.calldata free base schemaPtr secondData i remaining)
      aw' out σ k' C' := by
  induction remaining generalizing mem free i aw k C with
  | zero => exact ⟨aw, k, C, h⟩
  | succ remaining ih =>
      have hir : i < n := by omega
      have valid := hrows i (le_refl _) (by omega)
      rcases multiRevokeRowView h (by omega) hir (by omega) with ⟨hbad, hrev⟩ | ⟨hc, hn, aw', k',
          C', hv⟩
      · exact False.elim (hbad.elim (fun hh ↦ hh valid.1) valid.2)
      have hb := valid.bounds hsign (by omega)
      have hfreeRow : free + 96 + 160 * (rowLength I.calldata secondData i).toNat < UInt256.size :=
          by
        have hm := Nat.mul_le_mul_left 160 hb.2.1
        have hrem : 96 + 160 * solcMaxU64 ≤ (96 + 160 * solcMaxU64) * (remaining + 1) := by
          exact Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hv' : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨479⟩
          ([UInt256.ofNat (rowLength I.calldata secondData i).toNat,
            UInt256.ofNat (rowLength I.calldata secondData i).toNat,
            UInt256.ofNat (rowData I.calldata secondData i).toNat, UInt256.ofNat i,
            UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n, secondData,
            UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw' out σ k' C' := by
        simpa only [u256_ofNat_toNat] using hv
      obtain ⟨aw'', k'', C'', hr⟩ := multiRevokeRowBuild hv' hstack hbase hin hspan hlen hptr
        hir hb.1 hb.2.1 hfreeRow hcd (by have := lt_size_of_lt_sign hsign; omega)
      have hp := multiRevokeRowMemory_prefix mem I.calldata free base i schemaPtr
        (rowData I.calldata secondData i).toNat (rowLength I.calldata secondData i).toNat (by omega)
      have hmemSize := hp.size
      have hl := (hp.load_preserved hbase (le_refl _) hin (by omega)).trans hlen
      have hf' : free + 96 + 160 * (rowLength I.calldata secondData i).toNat +
          (96 + 160 * solcMaxU64) * remaining < UInt256.size := by
        have hm := Nat.mul_le_mul_left 160 hb.2.1
        rw [Nat.mul_add, Nat.mul_one] at hf
        omega
      obtain ⟨awf, kf, Cf, hfinal⟩ := ih hr (by omega) (by omega) hl
        (multiRevokeRowMemory_freePtr (by omega) hbase) (by omega) hf'
        (by intro j hj hjn; exact hrows j (by omega) (by omega))
      refine ⟨awf, kf, Cf, ?_⟩
      simpa only [multiRevokeRowsMemory, show i + 1 + remaining = i + (remaining + 1) by omega]
        using hfinal

theorem multiRevokeOuterRun {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n schemaPtr : Nat} {secondData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([⟨0⟩, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw out σ k C)
    (hstack : R.length + 19 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hf : free + (96 + 160 * solcMaxU64) * n < UInt256.size)
    (hsign : I.calldata.size < 2 ^ 255)
    (hsecond : secondData.toNat + 32 * n ≤ I.calldata.size)
    (hcd : schemaPtr + 32 * n < UInt256.size)
    (hrows : ∀ j < n, RowValid I.calldata secondData j) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨762⟩
      ([UInt256.ofNat n, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R)
      (multiRevokeRowsMemory mem I.calldata free base schemaPtr secondData 0 n)
      aw' out σ k' C' := by
  obtain ⟨aw', k', C', h'⟩ := multiRevokeOuterSteps (i := 0) (remaining := n)
    h hstack hbase hin hspan hlen hptr (by omega) hf hsign hsecond hcd
    (by intro j _ hj; exact hrows j (by omega))
  simp only [Nat.zero_add] at h'
  exact attesterRuntime_block_367_taken_packed
    (R := UInt256.ofNat n :: secondData :: UInt256.ofNat n :: UInt256.ofNat schemaPtr :: R)
    (by simp only [List.length_cons]; omega) (by rw [ult_zero (Nat.le_refl _)]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h'

theorem multiRevokeOuterRevert {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n schemaPtr : Nat} {secondData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([⟨0⟩, UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw out σ k C)
    (hstack : R.length + 19 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hf : free + (96 + 160 * solcMaxU64) * n < UInt256.size)
    (hsign : I.calldata.size < 2 ^ 255)
    (hsecond : secondData.toNat + 32 * n ≤ I.calldata.size)
    (hcd : schemaPtr + 32 * n < UInt256.size)
    (hbad : ¬ ∀ j < n, RowValid I.calldata secondData j) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  classical
  have hex : ∃ j, j < n ∧ ¬ RowValid I.calldata secondData j := by
    push_neg at hbad
    exact hbad
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change j < n ∧ ¬ RowValid I.calldata secondData j at hj
  have hbefore : ∀ t < j, RowValid I.calldata secondData t := by
    intro t ht
    have hnot := Nat.find_min hex ht
    by_contra hn
    exact hnot ⟨by omega, hn⟩
  have hfj : free + (96 + 160 * solcMaxU64) * j < UInt256.size := by
    have := Nat.mul_le_mul_left (96 + 160 * solcMaxU64) (Nat.le_of_lt hj.1)
    omega
  obtain ⟨aw', k', C', h'⟩ := multiRevokeOuterSteps (i := 0) (remaining := j)
    h hstack hbase hin hspan hlen hptr (by omega) hfj hsign hsecond hcd
    (by intro t _ ht; exact hbefore t (by omega))
  simp only [Nat.zero_add] at h'
  rcases multiRevokeRowView h' (by omega) hj.1 (by omega) with ⟨_, hr⟩ | ⟨hc, hn, _⟩
  · exact hr
  · exact False.elim (hj.2 ⟨hc, hn⟩)

end Benchmarks.EAS.Attester
