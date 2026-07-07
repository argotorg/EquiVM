import Benchmarks.Safe.Routines

/-! # Safe `getThreshold()` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Safe

def safeThresholdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨4⟩

theorem safeDecode_getThreshold_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getthresholdTransition.params.map Param.name)
      (transitionSignature getthresholdTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem safeGetThresholdBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (h : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      getthresholdTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (safeThresholdWord σ I).toNat))])) := by
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact h) ?_
  show evalExpr? config { contract := contract, locals := ∅ }
    (initState cA gh bl σ σ₀ g A I) (.storage thresholdRef) =
      .ok (.int (Int.ofNat (safeThresholdWord σ I).toNat))
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := ∅ })
    (slot := thresholdRef)
    (er := ({ base := "threshold", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨4⟩ (.int uint256Int))
    (value := .int (Int.ofNat (safeThresholdWord σ I).toNat))
    (hbase := by simp [thresholdRef])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [safeThresholdWord] using
        safeStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨4⟩)]

theorem safeGetThresholdX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (safeSelBytes 18)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeThresholdWord σ I)) := by
  obtain ⟨_, _, h1501⟩ := safeReachGetThresholdBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1514⟩ := safeGuardPeelOk (gt := ⟨1512⟩) h1501 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1517⟩ := (h1514.push1 ⟨4⟩ (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega))
    |>.sload (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have h974 := h1517
    |>.push2 ⟨974⟩ (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.jump (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.safeReturnWordFromMem974 h974
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeGetThresholdBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 18))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (safeSelBytes 18) (by native_decide) hsel
  have hword : safeThresholdWord σ_evm I = safeThresholdWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  exact safeReEquivExecTransport hcode
    (safeGetThresholdX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (safeSelectorDispatchGetThreshold hsel) (safeDecode_getThreshold_ok hsz4)
    (safeGetThresholdBodyReturns hwv) (by rw [← hword])
    hAccounts
    (returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (safeThresholdWord σ_evm I)))

theorem safeGetThresholdBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 18))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact safeGetThresholdBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 18) (by native_decide) hsel
    obtain ⟨_, _, h1501⟩ := safeReachGetThresholdBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
      hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1512⟩) h1501 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchGetThreshold hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
