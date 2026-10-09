import Benchmarks.EAS.Attester.MultiRevokeCells
import Benchmarks.EAS.Attester.PairHeap
import Benchmarks.EAS.Attester.MultiArrayABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem revokeDataMemory_heap {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hfit : free + 32 + 160 * n < UInt256.size) :
    PairArrayAt (revokeDataMemory mem cd free cdptr n) free (free + 32 + 160 * n) free n
      (fun j ↦ (calldataWord cd (cdptr + 32 * j), ⟨0⟩)) := by
  refine ⟨le_refl _, by omega, revokeDataMemory_length hfree (by omega), ?_⟩
  intro j hj
  exact ⟨free + 32 + 96 * n + 64 * j, by omega, by omega,
    revokeDataMemory_cells hfree hfit hj⟩

theorem multiRevokeRowMemory_heap {mem cd : ByteArray} {free base i schemaPtr uidPtr n : Nat}
    (hfree : 96 ≤ free) (hslot : base + 64 + 32 * i ≤ free)
    (hn : 0 < n) (hfit : free + 96 + 160 * n < UInt256.size) :
    PairRequestAt (multiRevokeRowMemory mem cd free base i schemaPtr uidPtr n)
      free (free + 96 + 160 * n) (free + 32 + 160 * n)
      (calldataWord cd (schemaPtr + 32 * i)) n
      (fun j ↦ (calldataWord cd (uidPtr + 32 * j), ⟨0⟩)) := by
  obtain ⟨hfirst, hsecond⟩ := multiRevokeRowMemory_fields
    (mem := mem) (cd := cd) (schemaPtr := schemaPtr) (uidPtr := uidPtr) hslot hfit
  refine ⟨by omega, by omega, hfirst, free, ?_, ?_⟩
  · convert hsecond using 1; congr 2; omega
  · apply PairArrayAt.mono (hi := free + 32 + 160 * n) _ (le_refl _) (by omega)
    apply (revokeDataMemory_heap hfree (by omega)).congr
    intro off hlo hhi
    exact multiRevokeRowMemory_data_preserved hfree hslot hn (by omega) hlo hhi

theorem multiRevokeRowsEnd_lower (cd : ByteArray) (free : Nat) (secondData : UInt256)
    (i remaining : Nat) : free ≤ multiRevokeRowsEnd cd free secondData i remaining := by
  induction remaining generalizing free i with
  | zero => rfl
  | succ remaining ih =>
      rw [multiRevokeRowsEnd]
      exact le_trans (by omega) (ih _ _)

theorem multiRevokeRowsEnd_upper {cd : ByteArray} {free i remaining : Nat}
    {secondData : UInt256}
    (hrows : ∀ j, i ≤ j → j < i + remaining → (rowLength cd secondData j).toNat ≤ solcMaxU64) :
    multiRevokeRowsEnd cd free secondData i remaining ≤ free + (96 + 160 * solcMaxU64) * remaining
        := by
  induction remaining generalizing free i with
  | zero => simp [multiRevokeRowsEnd]
  | succ remaining ih =>
      rw [multiRevokeRowsEnd]
      have hb := hrows i (by omega) (by omega)
      have hh := ih (free := free + 96 + 160 * (rowLength cd secondData i).toNat)
        (i := i + 1) (by intro j hj hj'; exact hrows j (by omega) (by omega))
      rw [Nat.mul_succ]
      omega

theorem multiRevokeRowsMemory_size {mem cd : ByteArray}
    {free base schemaPtr i remaining : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hspan : base + 32 + 32 * (i + remaining) ≤ free)
    (hsize : mem.size = free)
    (hrows : ∀ j, i ≤ j → j < i + remaining → 0 < (rowLength cd secondData j).toNat) :
    (multiRevokeRowsMemory mem cd free base schemaPtr secondData i remaining).size =
      multiRevokeRowsEnd cd free secondData i remaining := by
  induction remaining generalizing mem free i with
  | zero => exact hsize
  | succ remaining ih =>
      rw [multiRevokeRowsMemory, multiRevokeRowsEnd]
      apply ih (by omega) (by omega)
      · rw [multiRevokeRowMemory_size hfree (by omega) (hrows i (by omega) (by omega)), hsize]
        omega
      · intro j hj hj'; exact hrows j (by omega) (by omega)

theorem multiRevokeRowsMemory_cells {mem cd : ByteArray}
    {free base schemaPtr i remaining j : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hbase : 96 ≤ base)
    (hspan : base + 32 + 32 * (i + remaining) ≤ free) (hsize : mem.size = free)
    (hrows : ∀ j, i ≤ j → j < i + remaining → 0 < (rowLength cd secondData j).toNat)
    (hfit : multiRevokeRowsEnd cd free secondData i remaining < UInt256.size)
    (hji : i ≤ j) (hjn : j < i + remaining) :
    let result := multiRevokeRowsMemory mem cd free base schemaPtr secondData i remaining
    ∃ ptr, memLoad (UInt256.ofNat (base + 32 + 32 * j)) result = UInt256.ofNat ptr ∧
      PairRequestAt result 96 (multiRevokeRowsEnd cd free secondData i remaining) ptr
        (calldataWord cd (schemaPtr + 32 * j)) (rowLength cd secondData j).toNat
        (fun k ↦ (calldataWord cd ((rowData cd secondData j).toNat + 32 * k), ⟨0⟩)) := by
  dsimp only
  induction remaining generalizing mem free i with
  | zero => omega
  | succ remaining ih =>
      rw [multiRevokeRowsMemory, multiRevokeRowsEnd]
      rw [multiRevokeRowsEnd] at hfit
      have hn := hrows i (by omega) (by omega)
      have hend := multiRevokeRowsEnd_lower cd
        (free + 96 + 160 * (rowLength cd secondData i).toNat) secondData (i + 1) remaining
      have hnextSize : (multiRevokeRowMemory mem cd free base i schemaPtr
          (rowData cd secondData i).toNat (rowLength cd secondData i).toNat).size =
          free + 96 + 160 * (rowLength cd secondData i).toNat := by
        rw [multiRevokeRowMemory_size hfree (by omega) hn, hsize]; omega
      by_cases hij : i = j
      · subst j
        have hr := multiRevokeRowMemory_heap (mem := mem) (cd := cd) (base := base) (i := i)
          (schemaPtr := schemaPtr) (uidPtr := (rowData cd secondData i).toNat)
          hfree (by omega) hn (by omega : free + 96 + 160 * (rowLength cd secondData i).toNat < _)
        have hr' := hr.congr (mem' := multiRevokeRowsMemory _ cd
          (free + 96 + 160 * (rowLength cd secondData i).toNat)
          base schemaPtr secondData (i + 1) remaining) (by
            intro off hlo hhi
            exact multiRevokeRowsMemory_preserves (by omega) (by omega)
              (by rw [hnextSize]; omega) (by omega) hhi (.inr (by omega)))
        refine ⟨free + 32 + 160 * (rowLength cd secondData i).toNat, ?_,
          hr'.mono hfree hend⟩
        rw [multiRevokeRowsMemory_preserves (by omega) (by omega)
          (by rw [hnextSize]; omega) (by omega) (by omega) (.inl (by omega))]
        exact multiRevokeRowMemory_slot (by omega)
      · exact ih (by omega) (by omega) hnextSize
          (by intro k hk hk'; exact hrows k (by omega) (by omega)) hfit (by omega) (by omega)

theorem multiRevokeBuiltMemory_bounds {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    160 + 96 * arrayCount cd 4 ≤ multiRevokeBuiltFree cd ∧
      multiRevokeBuiltFree cd ≤
        160 + 96 * arrayCount cd 4 + (96 + 160 * solcMaxU64) * arrayCount cd 4 ∧
      multiRevokeBuiltFree cd < UInt256.size := by
  have hn := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hn
  have hupper := multiRevokeRowsEnd_upper (free := 160 + 96 * arrayCount cd 4)
    (i := 0) (remaining := arrayCount cd 4) (secondData := UInt256.ofNat (arrayDataNat cd 36)) (by
      intro j hj hj'
      exact uint64Bound_of_isZero_gt (hrows j (by rw [hshape.2]; omega)).1.length)
  have hlower := multiRevokeRowsEnd_lower cd (160 + 96 * arrayCount cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)
  refine ⟨hlower, hupper, lt_of_le_of_lt hupper ?_⟩
  norm_num only [solcMaxU64, UInt256.size] at hn ⊢
  omega

theorem multiRevokeBuiltMemory_size {cd : ByteArray} (hshape : BatchShape cd)
    (hrows : BatchRowsValid cd) : (multiRevokeBuiltMemory cd).size = multiRevokeBuiltFree cd := by
  apply multiRevokeRowsMemory_size (by omega) (by omega)
  · rw [pairArrayMemory_size (by decide), solcFreePtrMem_size]
    omega
  · intro j hj hj'
    have hn := (hrows j (by rw [hshape.2]; omega)).2
    exact Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz))

theorem multiRevokeBuiltMemory_heap {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    PairRequestsAt (multiRevokeBuiltMemory cd) 96 (multiRevokeBuiltFree cd) 128 (arrayCount cd 4)
      (fun i ↦ calldataWord cd (arrayDataNat cd 4 + 32 * i))
      (fun i ↦ (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat)
      (fun i j ↦ (calldataWord cd
        ((rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 * j), ⟨0⟩)) := by
  obtain ⟨hlower, hupper, hfit⟩ := multiRevokeBuiltMemory_bounds hc hshape hrows
  have hsize : (pairArrayMemory solcFreePtrMem 128 (arrayCount cd 4) ⟨96⟩).size =
      160 + 96 * arrayCount cd 4 := by
    rw [pairArrayMemory_size (by decide), solcFreePtrMem_size]
    omega
  refine ⟨by decide, by omega, ?_, ?_⟩
  · rw [multiRevokeBuiltMemory, multiRevokeRowsMemory_preserves (by omega) (by decide)
      (by rw [hsize]; omega) (by decide) (by omega) (.inl (by omega))]
    exact pairArrayMemory_length (by decide) (by decide)
  · intro j hj
    exact multiRevokeRowsMemory_cells (by omega) (by decide) (by omega) hsize
      (by intro k hk hk'
          have hn := (hrows k (by rw [hshape.2]; omega)).2
          exact Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz)))
      hfit (Nat.zero_le _) (by omega)

end Benchmarks.EAS.Attester
