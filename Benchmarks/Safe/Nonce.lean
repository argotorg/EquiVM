import Benchmarks.Safe.Routines

/-! # Safe `nonce()` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Safe

def safeNonceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨5⟩

theorem safeDecode_nonce_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nonceTransition.params.map Param.name)
      (transitionSignature nonceTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem safeNonceBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (h : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      nonceTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (safeNonceWord σ I).toNat))])) := by
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact h) ?_
  show evalExpr? config { contract := contract, locals := ∅ }
    (initState cA gh bl σ σ₀ g A I) (.storage nonceRef) =
      .ok (.int (Int.ofNat (safeNonceWord σ I).toNat))
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := ∅ })
    (slot := nonceRef)
    (er := ({ base := "nonce", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨5⟩ (.int uint256Int))
    (value := .int (Int.ofNat (safeNonceWord σ I).toNat))
    (hbase := by simp [nonceRef])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [safeNonceWord] using
        safeStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨5⟩)]

theorem safeNonceX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (safeSelBytes 22)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeNonceWord σ I)) := by
  obtain ⟨_, _, h1187⟩ := safeReachNonceBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1200⟩ := safeGuardPeelOk (gt := ⟨1198⟩) h1187 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h1206⟩ := (h1200.push2 ⟨974⟩ (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega))
    |>.push1 ⟨5⟩ (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.sload (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have h974 := h1206.dup2 (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.jump (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.safeReturnWordFromMem974 h974
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem safeNonceBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 22))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (safeSelBytes 22) (by native_decide) hsel
  have hword : safeNonceWord σ_evm I = safeNonceWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  exact safeReEquivExecTransport hcode
    (safeNonceX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (safeSelectorDispatchNonce hsel) (safeDecode_nonce_ok hsz4)
    (safeNonceBodyReturns hwv) (by rw [← hword])
    hAccounts
    (returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (safeNonceWord σ_evm I)))

theorem safeNonceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 22))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact safeNonceBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 22) (by native_decide) hsel
    obtain ⟨_, _, h1187⟩ := safeReachNonceBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
      hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1198⟩) h1187 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchNonce hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
