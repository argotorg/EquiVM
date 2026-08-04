import Examples.Ripemd160Old.HashPadding
import Examples.Precompiles.Ripemd160.HashCursor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

noncomputable def oldSourceWord (I : ExecutionEnv) (j : Nat) : UInt256 :=
  uInt256OfByteArray
    ((hashAllocatedMem I).readWithPadding (160 + 32 * j) 32)

theorem oldRead32_roundtrip (mem : ByteArray) (addr : Nat)
    (h : addr + 32 ≤ mem.size) :
    mem.readWithPadding addr 32 =
      UInt256.toByteArray (uInt256OfByteArray (mem.readWithPadding addr 32)) := by
  have hsz : (mem.readWithPadding addr 32).size = 32 := by
    rw [readWithPadding_eq_extract mem addr h, ByteArray.size_extract]
    omega
  rw [← word_toBytesBE_toByteArray_eq_toByteArray,
    toBytesBE_uInt256OfByteArray_of_size hsz]
  apply ByteArray.ext
  apply Array.ext'
  rw [byteArray_toList_eq] at *
  rw [List.toList_data_toByteArray]

theorem oldCopyIterations_le (I : ExecutionEnv) :
    oldCopyIterations I ≤ I.calldata.size + 1 := by
  unfold oldCopyIterations
  rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
  omega

theorem oldCopySource_toNat (I : ExecutionEnv) (j : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hj : j < oldCopyIterations I) :
    (oldCopySourceAddr j).toNat = 160 + 32 * j := by
  unfold oldCopySourceAddr
  rw [uadd_toNat, oldCopyIndexWord_toNat I j hsmall (by omega),
    show (⟨160⟩ : UInt256).toNat = 160 from by decide,
    show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
  have hb := oldCopy_body_lt I hj
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem oldCopyDest_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i ≤ oldCopyIterations I) :
    (oldCopyDestAddr I i).toNat = (hashPadPtr I).toNat + 32 * i := by
  unfold oldCopyDestAddr
  rw [uadd_toNat, oldCopyIndexWord_toNat I i hsmall hi,
    show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
  rw [hashPadPtr_toNat I hsmall]
  have hb := oldCopyIterations_le I
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem oldCopyBase_awSmall (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (oldCopyCursor I 0).aw.toNat < 2 ^ 64 := by
  simpa [oldCopyCursor] using (show (fallbackPaddedAw I).toNat < 2 ^ 64 by
    rw [fallbackPaddedAw_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega)

theorem oldCopyBase_cover (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPadPtr I).toNat ≤ (oldCopyCursor I 0).mem.size := by
  simp only [oldCopyCursor, hashAllocatedMem_size]
  rw [hashPadPtr_toNat I hsmall]
  omega

theorem oldCopyBase_sourceWord (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {j : Nat}
    (hj : j < oldCopyIterations I) :
    RuntimeWordAt (oldCopyCursor I 0) (oldCopySourceAddr j) (oldSourceWord I j) := by
  have haddr := oldCopySource_toNat I j hsmall hj
  have hcover : 160 + 32 * j + 32 ≤ (hashAllocatedMem I).size := by
    rw [hashAllocatedMem_size]
    have hb := oldCopy_body_lt I hj
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [oldCopyCursor, oldSourceWord]
    have hround := oldRead32_roundtrip (hashAllocatedMem I) (160 + 32 * j) hcover
    rw [haddr]
    exact hround
  · simpa [oldCopyCursor, haddr] using hcover
  · simp only [oldCopyCursor]
    intro hge
    have haw := fallbackPaddedAw_toNat I hsmall
    have hmul := fallbackPaddedAw_mul32_toNat I hsmall
    change (fallbackPaddedAw I * ⟨32⟩).toNat ≤ (oldCopySourceAddr j).toNat at hge
    rw [hmul, haw, haddr] at hge
    have hb := oldCopy_body_lt I hj
    have hd := Nat.mod_add_div (I.calldata.size + 223) 32
    have hm := Nat.mod_lt (I.calldata.size + 223) (by decide : 0 < 32)
    omega

/-- During the rounded source copy, all source words remain intact and every completed
destination word contains its corresponding source word. -/
theorem oldCopyCursor_invariant (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldCopyIterations I) :
    (oldCopyCursor I i).aw.toNat < 2 ^ 64 ∧
    (hashPadPtr I).toNat + 32 * i ≤ (oldCopyCursor I i).mem.size ∧
    (∀ j, j < oldCopyIterations I →
      RuntimeWordAt (oldCopyCursor I i) (oldCopySourceAddr j) (oldSourceWord I j)) ∧
    (∀ j, j < i →
      RuntimeWordAt (oldCopyCursor I i) (oldCopyDestAddr I j) (oldSourceWord I j)) := by
  induction i with
  | zero =>
      exact ⟨oldCopyBase_awSmall I hsmall, oldCopyBase_cover I hsmall,
        fun j hj => oldCopyBase_sourceWord I hsmall hj, by omega⟩
  | succ i ih =>
      have hip : i ≤ oldCopyIterations I := by omega
      have hit : i < oldCopyIterations I := by omega
      obtain ⟨hawC, hcoverC, hsource, hdest⟩ := ih hip
      let c := oldCopyCursor I i
      let loaded := runtimeLoadCursor c (oldCopySourceAddr i)
      have hsrcAddr := oldCopySource_toNat I i hsmall hit
      have hdstAddr := oldCopyDest_toNat I i hsmall hip
      have hsrcBound : (oldCopySourceAddr i).toNat + 63 < 32 * (2 ^ 64) := by
        rw [hsrcAddr]
        unfold maxFallbackCalldataSize at hsmall
        have hb := oldCopy_body_lt I hit
        omega
      have hdstBound : (oldCopyDestAddr I i).toNat + 63 < 32 * (2 ^ 64) := by
        rw [hdstAddr, hashPadPtr_toNat I hsmall]
        have hn32 : 32 * oldCopyIterations I ≤ I.calldata.size + 31 := by
          unfold oldCopyIterations
          simpa [Nat.mul_comm] using Nat.div_mul_le_self (I.calldata.size + 31) 32
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hloadedAw : loaded.aw.toNat < 2 ^ 64 := by
        simpa [loaded, runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
          runtimeMstoreAw_lt_pow64 hawC hsrcBound
      have hload : runtimeMloadValue c.mem c.aw (oldCopySourceAddr i) =
          oldSourceWord I i := (hsource i hit).load
      have hnext : oldCopyCursor I (i + 1) =
          runtimeStoreCursor loaded (oldCopyDestAddr I i) (oldSourceWord I i) := by
        simp only [oldCopyCursor, c, loaded, hload]
      rw [hnext]
      have hgap : (oldCopyDestAddr I i).toNat - loaded.mem.size < USize.size := by
        have hle : (oldCopyDestAddr I i).toNat ≤ loaded.mem.size := by
          simpa [loaded, runtimeLoadCursor, hdstAddr] using hcoverC
        simp [Nat.sub_eq_zero_of_le hle, USize.size]
      have hawNext :
          (runtimeStoreCursor loaded (oldCopyDestAddr I i) (oldSourceWord I i)).aw.toNat <
            2 ^ 64 := by
        simpa [runtimeStoreCursor] using
          runtimeMstoreAw_lt_pow64 hloadedAw hdstBound
      refine ⟨hawNext, ?_, ?_, ?_⟩
      · simp only [runtimeStoreCursor]
        have hgrow := toByteArray_write_size_ge_off_add32 (oldSourceWord I i)
          loaded.mem (oldCopyDestAddr I i).toNat hgap
        change (hashPadPtr I).toNat + 32 * (i + 1) ≤
          (runtimeMstoreMem loaded.mem (oldCopyDestAddr I i) (oldSourceWord I i)).size
        unfold runtimeMstoreMem
        rw [hdstAddr] at hgrow ⊢
        simpa [Nat.mul_add] using hgrow
      · intro j hj
        have hw := (hsource j hj).afterLoadWide hawC hsrcBound
        apply hw.storeAbove hloadedAw hdstBound
        · rw [oldCopySource_toNat I j hsmall hj, hdstAddr,
            hashPadPtr_toNat I hsmall]
          change j < (I.calldata.size + 31) / 32 at hj
          omega
        · exact hgap
      · intro j hj
        by_cases hji : j < i
        · have hw := (hdest j hji).afterLoadWide hawC hsrcBound
          apply hw.storeAbove hloadedAw hdstBound
          · rw [oldCopyDest_toNat I j hsmall (by omega), hdstAddr]
            omega
          · exact hgap
        · have hji' : j = i := by omega
          subst j
          exact runtimeStoreCursor_word_self loaded (oldCopyDestAddr I i)
            (oldSourceWord I i) hloadedAw hdstBound hgap

theorem oldZeroDest_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i ≤ oldZeroIterations I) :
    (hashPadPtr I + oldZeroIndexWord I i).toNat =
      (hashPadPtr I).toNat + oldZeroIndex I i := by
  rw [uadd_toNat, oldZeroIndexWord_toNat I i hsmall hi,
    show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
  rw [hashPadPtr_toNat I hsmall]
  have hz := oldZeroIndex_at_end I
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  unfold maxFallbackCalldataSize at hsmall
  unfold oldZeroIndex at hz ⊢
  omega

/-- The zero loop preserves copied words and records every completed all-zero word. -/
theorem oldZeroCursor_invariant (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldZeroIterations I) :
    (oldZeroCursor I i).aw.toNat < 2 ^ 64 ∧
    (hashPadPtr I).toNat + oldZeroIndex I i ≤ (oldZeroCursor I i).mem.size ∧
    (∀ j, j < oldCopyIterations I →
      RuntimeWordAt (oldZeroCursor I i) (oldCopyDestAddr I j) (oldSourceWord I j)) ∧
    (∀ j, j < i →
      RuntimeWordAt (oldZeroCursor I i)
        (hashPadPtr I + oldZeroIndexWord I j) ⟨0⟩) := by
  induction i with
  | zero =>
      obtain ⟨haw, hcover, _, hdest⟩ :=
        oldCopyCursor_invariant I hsmall (le_refl (oldCopyIterations I))
      exact ⟨by simpa [oldZeroCursor] using haw,
        by simpa [oldZeroCursor, oldZeroIndex] using hcover,
        by simpa [oldZeroCursor] using hdest, by omega⟩
  | succ i ih =>
      have hip : i ≤ oldZeroIterations I := by omega
      have hit : i < oldZeroIterations I := by omega
      obtain ⟨haw, hcover, hcopied, hzero⟩ := ih hip
      let c := oldZeroCursor I i
      let addr := hashPadPtr I + oldZeroIndexWord I i
      have haddr := oldZeroDest_toNat I i hsmall hip
      have hbound : addr.toNat + 63 < 32 * (2 ^ 64) := by
        dsimp only [addr]
        rw [haddr, hashPadPtr_toNat I hsmall]
        have hz := oldZeroIndex_before_end I hit
        have hp := (hashPaddedLength_bounds I.calldata.size).2
        unfold maxFallbackCalldataSize at hsmall
        omega
      have hgap : addr.toNat - c.mem.size < USize.size := by
        have hle : addr.toNat ≤ c.mem.size := by
          dsimp only [addr, c]
          rw [haddr]
          exact hcover
        simp [Nat.sub_eq_zero_of_le hle, USize.size]
      have hnext : oldZeroCursor I (i + 1) = runtimeStoreCursor c addr ⟨0⟩ := by
        simp only [oldZeroCursor, c, addr]
      rw [hnext]
      have hawNext : (runtimeStoreCursor c addr ⟨0⟩).aw.toNat < 2 ^ 64 := by
        simpa [runtimeStoreCursor] using runtimeMstoreAw_lt_pow64 haw hbound
      refine ⟨hawNext, ?_, ?_, ?_⟩
      · have hgrow := toByteArray_write_size_ge_off_add32 (⟨0⟩ : UInt256)
          c.mem addr.toNat hgap
        simp only [runtimeStoreCursor, runtimeMstoreMem]
        dsimp only [addr] at hgrow ⊢
        rw [haddr] at hgrow ⊢
        unfold oldZeroIndex at hgrow ⊢
        simpa [Nat.mul_add, Nat.add_assoc] using hgrow
      · intro j hj
        apply (hcopied j hj).storeAbove haw hbound
        · rw [oldCopyDest_toNat I j hsmall (by omega), haddr]
          unfold oldZeroIndex
          omega
        · exact hgap
      · intro j hj
        by_cases hji : j < i
        · apply (hzero j hji).storeAbove haw hbound
          · rw [oldZeroDest_toNat I j hsmall (by omega), haddr]
            unfold oldZeroIndex
            omega
          · exact hgap
        · have hji' : j = i := by omega
          subst j
          exact runtimeStoreCursor_word_self c addr ⟨0⟩ haw hbound hgap

end Ripemd160Old
