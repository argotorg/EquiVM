import Benchmarks.EAS.Attester.Dispatch
import Benchmarks.EAS.Attester.MultiArrayABI
import Benchmarks.EAS.Attester.MultiAttestLoopTrace
import Benchmarks.EAS.Attester.PairArrayTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterMultiAttestDispatch {cd : ByteArray}
    (hsel : (attesterMultiAttestSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some multiAttestTransition := by
  have heq := byteArray_eq_of_beq hsel
  rw [dispatchMsg_eq_dispatchList contract cd, contract_transitions]
  simp only [dispatchList_cons, dispatchList_nil, attestSelectorOf, multiAttestSelectorOf,
    multiRevokeSelectorOf, revokeSelectorOf, ← heq]
  rfl

theorem attesterMultiAttestReachDecode {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hsel : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2482⟩ [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨116⟩, ⟨121⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  have hsz := calldata_size_ge_of_selIs I attesterMultiAttestSelBytes rfl hsel
  have hnot : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false := by
    rw [← byteArray_eq_of_beq hsel]
    decide +kernel
  obtain ⟨k, C, rd43⟩ := attesterRuntimeReach43 hcode hvalue hsz hsize hnot
  have rd102 := attesterRuntime_block_43_taken (by decide)
    (by change UInt256.eq ⟨0x54e1db35⟩ (solcSelectorWord I) ≠ ⟨0⟩
        rw [attesterMultiAttestEvmSelector hsz, hsel]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) rd43
  have rd2482 := attesterRuntime_block_102 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) rd102
  exact ⟨_, _, rd2482⟩

theorem multiAttestRequire {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {n m secondData schemaData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨935⟩
      ([m, secondData, n, schemaData] ++ R) mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) :
    ((n = ⟨0⟩ ∨ m ≠ n) ∧ RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
      (n ≠ ⟨0⟩ ∧ m = n ∧ ∃ k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1006⟩
        ([n, ⟨96⟩, m, secondData, n, schemaData] ++ R) mem aw out σ k' C') := by
  by_cases hn : n = ⟨0⟩
  · subst n
    have h' := attesterRuntime_block_935_taken (R := schemaData :: R)
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [attesterRuntime_validJumps]; native_decide) h
    have h'' := attesterRuntime_block_951_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) h'
    exact .inl ⟨.inl rfl, attesterRuntime_block_957
      (by simp only [attesterRuntime_block_951_fallthrough_stack, List.length_cons]; omega) h''⟩
  have h' := attesterRuntime_block_935_fallthrough (R := schemaData :: R)
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) h
  have h'' := attesterRuntime_block_946 (by simp only [List.length_cons]; omega) h'
  by_cases hmn : m = n
  · subst m
    have h''' := attesterRuntime_block_951_taken
      (by simp only [List.length_cons]; omega)
      (by rw [u256_eq_refl]; decide) (by rw [attesterRuntime_validJumps]; native_decide) h''
    exact .inr ⟨hn, rfl, _, _, h'''⟩
  · have h''' := attesterRuntime_block_951_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [uInt256_eq_zero_of_ne (fun he ↦ hmn (uInt256_eq_one_eq he))]; rfl) h''
    exact .inl ⟨.inr hmn, attesterRuntime_block_957
      (by simp only [attesterRuntime_block_951_fallthrough_stack, List.length_cons]; omega) h'''⟩

theorem multiAttestBodyView {words : String → UInt256} {I g s0 σ mem aw out k C R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2482⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨116⟩ :: R) mem aw out σ k C)
    (hstack : R.length + 18 ≤ 1024) :
    (¬ MultiHeadChecks I.calldata ∧ RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
      (MultiHeadChecks I.calldata ∧ ∃ k' C',
        RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨935⟩
          ([UInt256.ofNat (arrayCount I.calldata 36), UInt256.ofNat (arrayDataNat I.calldata 36),
            UInt256.ofNat (arrayCount I.calldata 4),
                UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
          mem aw out σ k' C') := by
  rcases attesterMultiHeads h hstack (by rw [attesterRuntime_validJumps]; native_decide) with
      hbad | ⟨hc, k', C', h'⟩
  · exact .inl hbad
  have h'' := attesterRuntime_block_116 (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  refine .inr ⟨hc, k' + 3, C' + 12, ?_⟩
  simpa only [arrayCount_word,
    arrayData_eq_ofNat (uint64Bound_of_isZero_gt hc.firstOffset),
    arrayData_eq_ofNat (uint64Bound_of_isZero_gt hc.secondOffset)] using h''

theorem multiAttestBadShape {words : String → UInt256} {I g s0 σ mem aw out k C R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨935⟩
      ([UInt256.ofNat (arrayCount I.calldata 36), UInt256.ofNat (arrayDataNat I.calldata 36),
        UInt256.ofNat (arrayCount I.calldata 4), UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
      mem aw out σ k C)
    (hstack : R.length + 9 ≤ 1024) (hbad : ¬ BatchShape I.calldata) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  rcases multiAttestRequire h hstack with ⟨_, hr⟩ | ⟨hn, heq, _⟩
  · exact hr
  · apply False.elim
    apply hbad
    constructor
    · by_contra hz
      have hz' : arrayCount I.calldata 4 = 0 := by omega
      exact hn (by rw [hz']; rfl)
    · have heq' := congrArg UInt256.toNat heq
      simpa only [arrayCount_word] using heq'

theorem multiAttestReachOuter {words : String → UInt256} {I g s0 σ aw out k C R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨935⟩
      ([UInt256.ofNat (arrayCount I.calldata 36), UInt256.ofNat (arrayDataNat I.calldata 36),
        UInt256.ofNat (arrayCount I.calldata 4), UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
      solcFreePtrMem aw out σ k C)
    (hstack : R.length + 14 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1109⟩
      ([⟨0⟩, ⟨128⟩, UInt256.ofNat (arrayCount I.calldata 4), ⟨96⟩,
          UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 36), UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
      (pairArrayMemory solcFreePtrMem 128 (arrayCount I.calldata 4) ⟨96⟩) aw' out σ k' C' := by
  rcases multiAttestRequire h (by omega) with ⟨hbad, hrev⟩ | ⟨hn, heq, k', C', h'⟩
  · apply False.elim
    rcases hbad with hz | hne
    · have hz' := congrArg UInt256.toNat hz
      rw [arrayCount_word] at hz'
      change arrayCount I.calldata 4 = 0 at hz'
      exact Nat.ne_of_gt hshape.1 hz'
    · exact hne (congrArg UInt256.ofNat hshape.2)
  have hn64 := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount I.calldata 4 ≤ solcMaxU64 at hn64
  rw [hshape.2] at h'
  exact pairArrayAllocate1006
    (R := ⟨96⟩ :: UInt256.ofNat (arrayCount I.calldata 4) :: UInt256.ofNat (arrayDataNat I.calldata
        36) ::
      UInt256.ofNat (arrayCount I.calldata 4) :: UInt256.ofNat (arrayDataNat I.calldata 4) :: R)
    h' (by simp only [List.length_cons]; omega) (by decide) solcFreePtrMem_mload64 hshape.1 hn64
    (by change arrayCount I.calldata 4 ≤ 18446744073709551615 at hn64
        change 128 + 32 + 96 * arrayCount I.calldata 4 < 2 ^ 256
        omega)

theorem multiAttestBuildRequests {words : String → UInt256} {I g s0 σ aw out k C R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨935⟩
      ([UInt256.ofNat (arrayCount I.calldata 36), UInt256.ofNat (arrayDataNat I.calldata 36),
        UInt256.ofNat (arrayCount I.calldata 4), UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
      solcFreePtrMem aw out σ k C)
    (hstack : R.length + 21 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hsize : I.calldata.size < UInt256.size) :
    (¬ BatchRowsValid I.calldata ∧ RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
      (BatchRowsValid I.calldata ∧ ∃ aw' k' C',
        RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1657⟩
          ([UInt256.ofNat (arrayCount I.calldata 4), ⟨128⟩, UInt256.ofNat (arrayCount I.calldata 4),
              ⟨96⟩,
            UInt256.ofNat (arrayCount I.calldata 4), UInt256.ofNat (arrayDataNat I.calldata 36),
            UInt256.ofNat (arrayCount I.calldata 4),
                UInt256.ofNat (arrayDataNat I.calldata 4)] ++ R)
          (multiAttestBuiltMemory I.calldata) aw' out σ k' C') := by
  obtain ⟨aw', k', C', h'⟩ := multiAttestReachOuter h (by omega) hc hshape
  have hn64 := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount I.calldata 4 ≤ solcMaxU64 at hn64
  have hf : 160 + 96 * arrayCount I.calldata 4 +
      (96 + 480 * solcMaxU64) * arrayCount I.calldata 4 < UInt256.size := by
    change arrayCount I.calldata 4 ≤ 18446744073709551615 at hn64
    norm_num only [solcMaxU64, UInt256.size]
    omega
  have hbound0 := hc.first.outer_bounds (uint64Bound_of_isZero_gt hc.firstOffset) hsize
  have hbound1 := hc.second.outer_bounds (uint64Bound_of_isZero_gt hc.secondOffset) hsize
  change arrayDataNat I.calldata 4 + 32 * arrayCount I.calldata 4 ≤ I.calldata.size at hbound0
  change arrayDataNat I.calldata 36 + 32 * arrayCount I.calldata 36 ≤ I.calldata.size at hbound1
  rw [hshape.2] at hbound1
  have hsecond : (UInt256.ofNat (arrayDataNat I.calldata 36)).toNat +
      32 * arrayCount I.calldata 4 ≤ I.calldata.size := by
    rw [ulit_toNat' _ (by omega)]; exact hbound1
  have hin : 128 + 32 ≤ (pairArrayMemory solcFreePtrMem 128 (arrayCount I.calldata 4) ⟨96⟩).size :=
      by
    rw [pairArrayMemory_size (by decide)]; omega
  by_cases hrows : BatchRowsValid I.calldata
  · refine .inr ⟨hrows, ?_⟩
    exact multiAttestOuterRun (free := 160 + 96 * arrayCount I.calldata 4) (base := 128)
      h' hstack (by decide) hin (by omega)
      (pairArrayMemory_length (by decide) (by decide)) (pairArrayMemory_freePtr (by decide))
      hf (hc.size_lt_sign hsize) hsecond (by omega)
      (by intro j hj; exact hrows j (by rw [hshape.2]; exact hj))
  · refine .inl ⟨hrows, ?_⟩
    exact multiAttestOuterRevert (free := 160 + 96 * arrayCount I.calldata 4) (base := 128)
      h' hstack (by decide) hin (by omega)
      (pairArrayMemory_length (by decide) (by decide)) (pairArrayMemory_freePtr (by decide))
      hf (hc.size_lt_sign hsize) hsecond (by omega)
      (by intro hh; apply hrows; intro j hj; exact hh j (by rw [← hshape.2]; exact hj))

end Benchmarks.EAS.Attester
