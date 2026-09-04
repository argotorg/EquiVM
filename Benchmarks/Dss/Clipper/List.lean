import Benchmarks.Dss.Clipper.ListReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperX_list_empty_toCopyLoop (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨504⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hlen : solcSlotWord σ I ⟨11⟩ = ⟨0⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨548⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: clipperListEmptySrc :: clipperListEmptyDst ::
        clipperListEmptyBound :: clipperListEmptyBound ::
        clipperListEmptySrc :: clipperListEmptyDst ::
        clipperListEmptyFmp :: clipperListEmptyFmp ::
        clipperListArrayBasePtr :: [sel])
      (clipperListReturnLengthMem (⟨0⟩ : UInt256) clipperListEmptyFmp
        (clipperListArrayLengthMem ⟨0⟩))
      (clipperListReturnFinalAw (UInt256.ofNat 5) clipperListEmptyFmp
        clipperListArrayBasePtr)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1812⟩ := clipperX_list_entry (v := v) (code := code)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) hpatch hreach
  obtain ⟨_, _, rd512raw⟩ := clipperListStorageArrayGetter_empty
    (ret := (⟨512⟩ : UInt256)) (R := [sel]) rd1812
    (clipperListStorageArrayGetterWfPatched v hpatch)
    (clipperJumpDest1890 v hpatch) (clipperJumpDest512 v hpatch) hlen
    (by simp only [List.length_singleton]; omega)
  have rd512 := by
    simpa [hlen] using rd512raw
  obtain ⟨_, _, rd548⟩ := clipperListReturnFromMemToCopyLoop
    (arrPtr := clipperListArrayBasePtr) (fmp := clipperListEmptyFmp)
    (len := (⟨0⟩ : UInt256)) (R := [sel]) rd512
    (clipperListReturnFromMemWfPatched v hpatch)
    (clipperListArrayLengthMem_mload64 ⟨0⟩)
    clipperListReturnOffsetMem_empty_mload128
    clipperListReturnLengthMem_empty_mload128
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [clipperListEmptyFmp, clipperListEmptySrc, clipperListEmptyDst,
      clipperListEmptyBound] using rd548⟩

set_option maxHeartbeats 1000000 in
theorem clipperX_list_empty_const (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hcopy : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨548⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: clipperListEmptySrc :: clipperListEmptyDst ::
        clipperListEmptyBound :: clipperListEmptyBound ::
        clipperListEmptySrc :: clipperListEmptyDst ::
        clipperListEmptyFmp :: clipperListEmptyFmp ::
        clipperListArrayBasePtr :: [sel])
      (clipperListReturnLengthMem (⟨0⟩ : UInt256) clipperListEmptyFmp
        (clipperListArrayLengthMem ⟨0⟩))
      (clipperListReturnFinalAw (UInt256.ofNat 5) clipperListEmptyFmp
        clipperListArrayBasePtr)
      ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      ⟨(ABI.natBytes 32 ++ ABI.natBytes 0).toArray⟩ := by
  obtain ⟨_, _, rd548⟩ := hcopy
  have hdone :
      UInt256.isZero (UInt256.lt (⟨0⟩ : UInt256) clipperListEmptyBound) ≠ ⟨0⟩ := by
    native_decide
  have hreturn :
      (clipperListReturnLengthMem (⟨0⟩ : UInt256) (clipperListArrayFreePtr ⟨0⟩)
        (clipperListArrayLengthMem ⟨0⟩)).readWithPadding
        (clipperListArrayFreePtr ⟨0⟩).toNat
        (UInt256.sub (clipperListEmptyBound + clipperListEmptyDst)
          clipperListEmptyFmp).toNat =
        ⟨(ABI.natBytes 32 ++ ABI.natBytes 0).toArray⟩ := by
    simpa [clipperListEmptyFmp, clipperListEmptyDst, clipperListEmptyBound] using
      clipperListReturnLengthMem_empty_returnBytes
  exact clipperListReturnCopyLoopExit
    (i := (⟨0⟩ : UInt256)) (src := (⟨32⟩ : UInt256) + clipperListArrayBasePtr)
    (dst := clipperListEmptyDst)
    (bound := clipperListEmptyBound) (fmp := clipperListEmptyFmp)
    (arrPtr := clipperListArrayBasePtr) (R := [sel]) rd548
    (clipperListReturnFromMemWfPatched v hpatch) (clipperJumpDest572 v hpatch)
    hdone clipperListReturnLengthMem_empty_mload64 hreturn
    (by simp only [List.length_singleton]; omega)

theorem clipperX_list_empty (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨504⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hlen : solcSlotWord σ I ⟨11⟩ = ⟨0⟩) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A I)) := by
  have hcopy := clipperX_list_empty_toCopyLoop v hpatch hreach hlen
  have hret := clipperX_list_empty_const v hpatch hcopy
  rw [clipperActiveArrayReturnBytes_empty hlen]
  exact hret

set_option maxHeartbeats 1000000 in
theorem clipperX_list_nonempty (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hwfStorage : clipperStorageWF σ I)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨504⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hlen : solcSlotWord σ I ⟨11⟩ ≠ ⟨0⟩) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (clipperActiveArrayReturnBytes (initState cA gh bl σ σ₀ g A I)) := by
  obtain ⟨_, _, rd1812⟩ := clipperX_list_entry (v := v) (code := code)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) hpatch hreach
  obtain ⟨_, _, rd1870raw⟩ := clipperListStorageArrayGetter_nonempty_to_loop
    (ret := (⟨512⟩ : UInt256)) (R := [sel]) rd1812
    (clipperListStorageArrayGetterWfPatched v hpatch) hlen
    (by simp only [List.length_singleton]; omega)
  have hlenPos : 0 < (solcSlotWord σ I ⟨11⟩).toNat := by
    by_contra hpos
    have hzero : (solcSlotWord σ I ⟨11⟩).toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzero)
  obtain ⟨_, _, rd512⟩ :=
    clipperListStorageArrayLoopFrom
      (σ := σ) (ee := I) (ret := (⟨512⟩ : UInt256)) (R := [sel])
      hwfStorage (clipperListStorageArrayGetterWfPatched v hpatch)
      (clipperJumpDest1870 v hpatch) (clipperJumpDest512 v hpatch)
      (by simp only [List.length_singleton]; omega)
      ((solcSlotWord σ I ⟨11⟩).toNat - 1) 0
      (by omega) _ _ (by
        simpa [clipperListArrayDest_zero, clipperListArraySlot,
          clipperListArrayCopiedMem, clipperListArrayCopiedAw] using rd1870raw)
  obtain ⟨_, _, rd548⟩ := clipperListReturnFromMemToCopyLoop
    (arrPtr := clipperListArrayBasePtr)
    (fmp := clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))
    (len := solcSlotWord σ I ⟨11⟩) (R := [sel]) rd512
    (clipperListReturnFromMemWfPatched v hpatch)
    (clipperListArrayCopiedMem_mload64_of_wf hwfStorage)
    (clipperListReturnOffsetMem_mload128_of_wf hwfStorage)
    (clipperListReturnBaseMem_mload128_of_wf hwfStorage)
    (by simp only [List.length_singleton]; omega)
  exact clipperListReturnCopyLoopFrom
    (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    hwfStorage (clipperListReturnFromMemWfPatched v hpatch)
    (clipperJumpDest548 v hpatch) (clipperJumpDest572 v hpatch)
    (by simp only [List.length_singleton]; omega)
    (solcSlotWord σ I ⟨11⟩).toNat 0 (by omega) _ _ rd548

theorem clipperListBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hStorageWF : clipperStorageWF σ_evm I) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 15) (by native_decide) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ listTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.array
            (clipperActiveArrayValues
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))])) := by
    exact clipperListBodyReturnsActive v
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
      (by simp only [initState]; exact hwv) (by simp)
  have hval :
      some [Value.array
          (clipperActiveArrayValues
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))] =
        some [Value.array
          (clipperActiveArrayValues
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))] := by
    rw [← clipperActiveArrayValues_accountMapEquiv hAccounts]
  have henc :
      returnEquiv
        (clipperActiveArrayReturnBytes
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
        (some [(.array
          (clipperActiveArrayValues
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)))])
        listTransition.returnType :=
    clipperListReturnEquiv (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
  have hreach := clipperReachListBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (clipperActiveArrayReturnBytes
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) := by
    by_cases hlen : solcSlotWord σ_evm I ⟨11⟩ = ⟨0⟩
    · exact clipperX_list_empty v hpatch hreach hlen
    · exact clipperX_list_nonempty v hpatch hStorageWF hreach hlen
  exact hret.reEquivExecutionTransport hcode (clipperDispatch_list v hsel)
    (clipperDecode_list v hsz) hbody hval hAccounts henc

end Benchmarks.Dss.Clipper
