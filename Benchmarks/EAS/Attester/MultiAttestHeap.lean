import Benchmarks.EAS.Attester.MultiAttestCells
import Benchmarks.EAS.Attester.AttestCellHeap
import Benchmarks.EAS.Attester.MultiArrayABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attestDataMemory_heap {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hfit : free + 32 + 480 * n < UInt256.size) :
    AttestArrayAt (attestDataMemory mem cd free cdptr n) free (free + 32 + 480 * n) free n
      (fun j ↦ calldataWord cd (cdptr + 32 * j)) := by
  refine ⟨le_refl _, by omega, attestDataMemory_length hfree (by omega), ?_⟩
  intro j hj
  obtain ⟨ptr, hp, hc⟩ := attestFillMemory_cells
    (mem := structArrayMemory mem free n attestDefaultFields)
    (free := free + 32 + 224 * n) (slots := free + 32) (i := 0) (n := n) (j := j)
    (values := fun j ↦ calldataWord cd (cdptr + 32 * j))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨ptr, hp, hc.mono (by omega) (by omega)⟩

theorem multiAttestRowMemory_heap {mem cd : ByteArray} {free base i schemaPtr uidPtr n : Nat}
    (hfree : 96 ≤ free) (hslot : base + 64 + 32 * i ≤ free)
    (hn : 0 < n) (hfit : free + 96 + 480 * n < UInt256.size) :
    AttestRequestAt (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n)
      free (free + 96 + 480 * n) (free + 32 + 480 * n)
      (calldataWord cd (schemaPtr + 32 * i)) n
      (fun j ↦ calldataWord cd (uidPtr + 32 * j)) := by
  obtain ⟨hfirst, hsecond⟩ := multiAttestRowMemory_fields
    (mem := mem) (cd := cd) (schemaPtr := schemaPtr) (uidPtr := uidPtr) hslot hfit
  refine ⟨by omega, by omega, hfirst, free, ?_, ?_⟩
  · convert hsecond using 1; congr 2; omega
  · apply AttestArrayAt.mono (hi := free + 32 + 480 * n) _ (le_refl _) (by omega)
    apply (attestDataMemory_heap hfree (by omega)).congr
    intro off hlo hhi
    exact multiAttestRowMemory_data_preserved hfree hslot hn (by omega) hlo hhi

theorem multiAttestRowsEnd_lower (cd : ByteArray) (free : Nat) (secondData : UInt256)
    (i remaining : Nat) : free ≤ multiAttestRowsEnd cd free secondData i remaining := by
  induction remaining generalizing free i with
  | zero => rfl
  | succ remaining ih =>
      rw [multiAttestRowsEnd]
      exact le_trans (by omega) (ih _ _)

theorem multiAttestRowsEnd_upper {cd : ByteArray} {free i remaining : Nat}
    {secondData : UInt256}
    (hrows : ∀ j, i ≤ j → j < i + remaining → (rowLength cd secondData j).toNat ≤ solcMaxU64) :
    multiAttestRowsEnd cd free secondData i remaining ≤ free + (96 + 480 * solcMaxU64) * remaining
        := by
  induction remaining generalizing free i with
  | zero => simp [multiAttestRowsEnd]
  | succ remaining ih =>
      rw [multiAttestRowsEnd]
      have hb := hrows i (by omega) (by omega)
      have hh := ih (free := free + 96 + 480 * (rowLength cd secondData i).toNat)
        (i := i + 1) (by intro j hj hj'; exact hrows j (by omega) (by omega))
      rw [Nat.mul_succ]
      omega

theorem multiAttestRowsMemory_size {mem cd : ByteArray}
    {free base schemaPtr i remaining : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hspan : base + 32 + 32 * (i + remaining) ≤ free)
    (hsize : mem.size = free)
    (hrows : ∀ j, i ≤ j → j < i + remaining → 0 < (rowLength cd secondData j).toNat) :
    (multiAttestRowsMemory mem cd free base schemaPtr secondData i remaining).size =
      multiAttestRowsEnd cd free secondData i remaining := by
  induction remaining generalizing mem free i with
  | zero => exact hsize
  | succ remaining ih =>
      rw [multiAttestRowsMemory, multiAttestRowsEnd]
      apply ih (by omega) (by omega)
      · rw [multiAttestRowMemory_size hfree (by omega) (hrows i (by omega) (by omega)), hsize]
        omega
      · intro j hj hj'; exact hrows j (by omega) (by omega)

theorem multiAttestRowsMemory_cells {mem cd : ByteArray}
    {free base schemaPtr i remaining j : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hbase : 96 ≤ base)
    (hspan : base + 32 + 32 * (i + remaining) ≤ free) (hsize : mem.size = free)
    (hrows : ∀ j, i ≤ j → j < i + remaining → 0 < (rowLength cd secondData j).toNat)
    (hfit : multiAttestRowsEnd cd free secondData i remaining < UInt256.size)
    (hji : i ≤ j) (hjn : j < i + remaining) :
    let result := multiAttestRowsMemory mem cd free base schemaPtr secondData i remaining
    ∃ ptr, memLoad (UInt256.ofNat (base + 32 + 32 * j)) result = UInt256.ofNat ptr ∧
      AttestRequestAt result 96 (multiAttestRowsEnd cd free secondData i remaining) ptr
        (calldataWord cd (schemaPtr + 32 * j)) (rowLength cd secondData j).toNat
        (fun k ↦ calldataWord cd ((rowData cd secondData j).toNat + 32 * k)) := by
  dsimp only
  induction remaining generalizing mem free i with
  | zero => omega
  | succ remaining ih =>
      rw [multiAttestRowsMemory, multiAttestRowsEnd]
      rw [multiAttestRowsEnd] at hfit
      have hn := hrows i (by omega) (by omega)
      have hend := multiAttestRowsEnd_lower cd
        (free + 96 + 480 * (rowLength cd secondData i).toNat) secondData (i + 1) remaining
      have hnextSize : (multiAttestRowMemory mem cd free base i schemaPtr
          (rowData cd secondData i).toNat (rowLength cd secondData i).toNat).size =
          free + 96 + 480 * (rowLength cd secondData i).toNat := by
        rw [multiAttestRowMemory_size hfree (by omega) hn, hsize]; omega
      by_cases hij : i = j
      · subst j
        have hr := multiAttestRowMemory_heap (mem := mem) (cd := cd) (base := base) (i := i)
          (schemaPtr := schemaPtr) (uidPtr := (rowData cd secondData i).toNat)
          hfree (by omega) hn (by omega : free + 96 + 480 * (rowLength cd secondData i).toNat < _)
        have hr' := hr.congr (mem' := multiAttestRowsMemory _ cd
          (free + 96 + 480 * (rowLength cd secondData i).toNat)
          base schemaPtr secondData (i + 1) remaining) (by
            intro off hlo hhi
            exact multiAttestRowsMemory_preserves (by omega) (by omega)
              (by rw [hnextSize]; omega) (by omega) hhi (.inr (by omega)))
        refine ⟨free + 32 + 480 * (rowLength cd secondData i).toNat, ?_,
          hr'.mono hfree hend⟩
        rw [multiAttestRowsMemory_preserves (by omega) (by omega)
          (by rw [hnextSize]; omega) (by omega) (by omega) (.inl (by omega))]
        exact multiAttestRowMemory_slot (by omega)
      · exact ih (by omega) (by omega) hnextSize
          (by intro k hk hk'; exact hrows k (by omega) (by omega)) hfit (by omega) (by omega)

theorem multiAttestBuiltMemory_bounds {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    160 + 96 * arrayCount cd 4 ≤ multiAttestBuiltFree cd ∧
      multiAttestBuiltFree cd ≤
        160 + 96 * arrayCount cd 4 + (96 + 480 * solcMaxU64) * arrayCount cd 4 ∧
      multiAttestBuiltFree cd < UInt256.size := by
  have hn := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hn
  have hupper := multiAttestRowsEnd_upper (free := 160 + 96 * arrayCount cd 4)
    (i := 0) (remaining := arrayCount cd 4) (secondData := UInt256.ofNat (arrayDataNat cd 36)) (by
      intro j hj hj'
      exact uint64Bound_of_isZero_gt (hrows j (by rw [hshape.2]; omega)).1.length)
  have hlower := multiAttestRowsEnd_lower cd (160 + 96 * arrayCount cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)
  refine ⟨hlower, hupper, lt_of_le_of_lt hupper ?_⟩
  norm_num only [solcMaxU64, UInt256.size] at hn ⊢
  omega

theorem multiAttestBuiltMemory_size {cd : ByteArray} (hshape : BatchShape cd)
    (hrows : BatchRowsValid cd) : (multiAttestBuiltMemory cd).size = multiAttestBuiltFree cd := by
  apply multiAttestRowsMemory_size (by omega) (by omega)
  · rw [pairArrayMemory_size (by decide), solcFreePtrMem_size]
    omega
  · intro j hj hj'
    have hn := (hrows j (by rw [hshape.2]; omega)).2
    exact Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz))

theorem multiAttestBuiltMemory_heap {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    AttestRequestsAt (multiAttestBuiltMemory cd) 96 (multiAttestBuiltFree cd) 128 (arrayCount cd 4)
      (fun i ↦ calldataWord cd (arrayDataNat cd 4 + 32 * i))
      (fun i ↦ (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat)
      (fun i j ↦ calldataWord cd
        ((rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 * j)) := by
  obtain ⟨hlower, hupper, hfit⟩ := multiAttestBuiltMemory_bounds hc hshape hrows
  have hsize : (pairArrayMemory solcFreePtrMem 128 (arrayCount cd 4) ⟨96⟩).size =
      160 + 96 * arrayCount cd 4 := by
    rw [pairArrayMemory_size (by decide), solcFreePtrMem_size]
    omega
  refine ⟨by decide, by omega, ?_, ?_⟩
  · rw [multiAttestBuiltMemory, multiAttestRowsMemory_preserves (by omega) (by decide)
      (by rw [hsize]; omega) (by decide) (by omega) (.inl (by omega))]
    exact pairArrayMemory_length (by decide) (by decide)
  · intro j hj
    exact multiAttestRowsMemory_cells (by omega) (by decide) (by omega) hsize
      (by intro k hk hk'
          have hn := (hrows k (by rw [hshape.2]; omega)).2
          exact Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz)))
      hfit (Nat.zero_le _) (by omega)

end Benchmarks.EAS.Attester
