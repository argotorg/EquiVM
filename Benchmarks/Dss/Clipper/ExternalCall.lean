import Reasoning.ExternalCall
import Solm.Equiv

/-!
# Clipper-local external-call transport helpers

These are contract-local variants of generic external-call facts that should eventually move to
`Reasoning/`.  They live here because the benchmark prompt forbids editing `Reasoning/` directly.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Clipper

private theorem clipperAccountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem clipperAccountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

-- GENERALIZES Reasoning.ExternalCall.typedCallViaEVM_accountMapEquiv:
-- remove the unused pre-call substate equality hypothesis.
theorem typedCallViaEVM_accountMapEquiv_noSubstate {cfg : Config}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) callPerm ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  obtain ⟨calldata, hdecode, hcall⟩ := hcall
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    clipperAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  cases hcall with
  | callMade hvalue hTheta hevm' hvalue' hdepth =>
    obtain ⟨callGas, A_in, hTheta⟩ := hTheta
    rename_i valueWord cA' σ' g' A'
    generalize htheta_solm :
      Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
        evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
        evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
        (toExecute evm_solm.accountMap tgt) callGas
        (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
        (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
        callPerm = thetaRes
    have hcode_equiv :
        toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
      accountMapExtensionalEq_toExecute h_ext_eq tgt
    have htheta_solm' :
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
          evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
          (toExecute evm_evm.accountMap tgt) callGas
          (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header
          callPerm =
          (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
            thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
      rw [← htheta_solm]
      rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
    let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
    have hTheta_rel :=
      (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := valueWord)
      (v' := valueWord)
      (d := calldata)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      h_ext_eq).1 hTheta.symm htheta_solm'
    have hCreated' : evm'_evm.createdAccounts = thetaRes.1 := by
      simp [hevm', hTheta_rel.1]
    have hTheta_s :
        (evm'_evm.createdAccounts, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1, z, out) =
          Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
            evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
            evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
            (toExecute evm_solm.accountMap tgt) callGas
            (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
            (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
            callPerm := by
      rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
      rw [hCreated']
      exact htheta_solm.symm
    use thetaRes.2.1
    use thetaRes.2.2.2.1
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, hTheta_s⟩ rfl (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue') (by
        rw [hEnv]
        exact hdepth)
    · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
      simpa [hevm'] using clipperAccountMapEquiv_of_accountMapExtensionalEq hσext
  | callNotMade hsubstate hevm' hvalue =>
    let A' := (State.addAccessedAccount evm_solm tgt).substate
    use evm_solm.accountMap
    use A'
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      apply callViaEVM.callNotMade (perm := callPerm)
      · rfl
      · simp [A', hCreated, hevm']
      · rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue
    · simpa [hevm'] using hAccounts

end Benchmarks.Dss.Clipper
