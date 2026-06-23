import Reasoning.SolmBody
import Reasoning.Storage

import Ethereum.Theory.StorageExtensionality

/-!
# ExternalCall — the `CALL` ↔ `externalCall` coupling

The Solm↔EVM boundary for a contract's **external call**, the peer of `Reasoning/Dispatch.lean`
(which couples the transaction entry / dispatcher).  An EVM `CALL` (exposed by `RD.call` as a
`Θ`-link) and the Solm `externalCall` (the `externalCallViaEVM` relation) invoke the *identical* `Θ`
with the same arguments, so the opaque result `(z, σ', o)` coincides on both sides **by
construction** — no assumption about the callee's code.

`callCoincides` is generic over the contract config / callee name / argument values; a per-contract
proof only supplies the trace **couplings** (the target address it masked, and the calldata it built
in memory = the ABI encoding) — exactly as the dispatcher consumes a per-contract selector fact.
`callNotMade_depthLimit` is the call-depth-limit counterpart (the `CALL` returns `0` without `Θ`).
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

/-- The 160-bit address round-trip the EVM `CALL` opcode performs on `msg.sender`:
    `ofUInt256 (ofNat addr) = addr`. -/
theorem accountAddress_roundtrip (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hlt : a.val < AccountAddress.size := a.isLt
  have hv : ((UInt256.ofNat a.val).val : ℕ) = a.val := by
    show ((Fin.ofNat _ a.val) : Fin UInt256.size).val = a.val
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_trans hlt hsize)
  apply Fin.ext
  simp only [AccountAddress.ofUInt256, Fin.ofNat, hv]
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-- `wordOfInt 0 = ⟨0⟩` — the zero value word a value-free `CALL` forwards. -/
theorem wordOfInt_zero : EVM.wordOfInt 0 = (⟨0⟩ : UInt256) := by decide

private theorem accountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem accountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

/-- **Coincidence (call made).**  Given the EVM-side `Θ`-link produced by `RD.call` (with witnesses
    `A_in`, `callGas`) and the trace couplings — the Solm target `tgt` is the cleaned stack address
    (`htgt`), and the ABI encoding of `name args` is exactly the calldata the bytecode placed in
    memory (`hcd`) — the Solm `externalCallViaEVM` holds for the *same* opaque `(z, σ', o)`.
    Instantiate the Solm existentials with the EVM witnesses; `Θ`'s determinism does the rest.
    Generic over the config / callee name / arguments (value `0`). -/
theorem callCoincides {cfg : Config} {evm : EVM.State} {name : Ident} {args : List Value}
    {tgt : EVM.Address} {targetWord : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {o : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256}
    (hperm : evm.executionEnv.perm = true)
    (hdepth : evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args
            = some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (cA', σ', g'', A', z, o) =
        Ethereum.EVM.Θ evm.executionEnv.blobVersionedHashes evm.createdAccounts evm.genesisBlockHeader
          evm.blocks evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 targetWord) (toExecute evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.perm) :
    typedCallViaEVM cfg evm tgt name 0 args
      (z, { evm with accountMap := σ', substate := A', createdAccounts := cA' }, o) := by
  -- rewrite the EVM `Θ`-link into the Solm form (round-trip sender, `tgt`, `perm = true`)
  have h := hΘ
  rw [accountAddress_roundtrip, ← htgt, hperm] at h
  exact ⟨mem.readWithPadding inOff.toNat inSize.toNat, hcd,
    callViaEVM.callMade wordOfInt_zero.symm ⟨callGas, A_in, h⟩ rfl
      (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _) hdepth⟩

/-- `Θ` respects observationally equivalent account maps.

<<<<<<< Updated upstream
If a typed external call is possible from an EVM state, and a Solm-side state differs only by
`accountMapEquiv`-equivalent current/original account maps, then the same success flag and return
data are possible on the Solm side, with a post-call account map equivalent to the EVM post-call
map.  This is the narrow interface needed by examples; it should be replaced by the direct proof
about `Ethereum.EVM.Θ` once that proof lands. -/
theorem typedCallViaEVM_accountMapEquiv {cfg : Config} {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out))
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (_hSubstate : evm_solm.substate = evm_evm.substate)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  obtain ⟨calldata, hdecode, hcall⟩ := hcall
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    accountMapExtensionalEq_of_accountMapEquiv hAccounts
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
        (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header true = thetaRes
    have hcode_equiv :
        toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
      accountMapExtensionalEq_toExecute h_ext_eq tgt
    have htheta_solm' :
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
          evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
          (toExecute evm_evm.accountMap tgt) callGas
          (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header true =
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
      (w := true)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z  thetaRes.2.2.2.2.1
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
            (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header true := by
      rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
      rw [hCreated']
      exact htheta_solm.symm
    use thetaRes.2.1
    use thetaRes.2.2.2.1
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      exact callViaEVM.callMade hvalue ⟨callGas, A_in, hTheta_s⟩ rfl (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue') (by
        rw [hEnv]
        exact hdepth)
    · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
      simpa [hevm'] using accountMapEquiv_of_accountMapExtensionalEq hσext
  | callNotMade hsubstate hevm' hvalue =>
    let A' := (State.addAccessedAccount evm_solm tgt).substate
    use evm_solm.accountMap
    use A'
    constructor
    · refine ⟨calldata, hdecode, ?_⟩
      apply callViaEVM.callNotMade
      · rfl
      · simp [A', hCreated, hevm']
      · rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hvalue
    · simpa [hevm'] using hAccounts


/-- `initState`-specialized form of `typedCallViaEVM_accountMapEquiv`.

This is the shape runtime-equivalence examples usually need: the EVM and Solm runs start from
split-but-equivalent current account maps while all other transaction fields, including `σ₀`, are
shared. -/
theorem typedCallViaEVM_initState_accountMapEquiv {cfg : Config}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {evm'_evm : EVM.State} {tgt : EVM.Address} {name : Ident} {value : ℤ}
    {args : List Value} {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg (initState cA gh bl σ_evm σ₀ g A I) tgt name value
      args (z, evm'_evm, out))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg (initState cA gh bl σ_solm σ₀ g A I) tgt name value args
        (z,
          { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm :=
  typedCallViaEVM_accountMapEquiv
    (evm_solm := initState cA gh bl σ_solm σ₀ g A I) hcall
    (by simpa [initState] using hAccounts)
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])

/-- `EVMStateEquiv`-returning form of `typedCallViaEVM_initState_accountMapEquiv`.

The opaque external call carries the simulation relation: from `initState`s that agree up to
`accountMapEquiv` on the current/original maps, the same `(z, out)` is possible on the Solm side, and
the two post-call states are related by `EVMStateEquiv` (executionEnv/createdAccounts equal, accounts
up to `accountMapEquiv`).  `hEnv` records that the EVM post-call state keeps `initState`'s
execution environment — true whenever it is a field update of `initState …` (e.g. the `callCoincides`
result).  This is the external-call peer of the storage-write `EVMStateEquiv` chains, so a body that
ends in `SSTORE`s after a call can stay entirely within the `EVMStateEquiv` simulation relation. -/
theorem typedCallViaEVM_initState_EVMStateEquiv {cfg : Config}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {evm'_evm : EVM.State} {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg (initState cA gh bl σ_evm σ₀ g A I) tgt name value args
      (z, evm'_evm, out))
    (hEnv : evm'_evm.executionEnv = (initState cA gh bl σ_solm σ₀ g A I).executionEnv)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg (initState cA gh bl σ_solm σ₀ g A I) tgt name value args
        (z,
          { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      EVMStateEquiv evm'_evm
        { initState cA gh bl σ_solm σ₀ g A I with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := evm'_evm.createdAccounts } := by
  obtain ⟨σ'_solm, A'_solm, hcoin_solm, hσ'⟩ :=
    typedCallViaEVM_initState_accountMapEquiv hcall hAccounts
  exact ⟨σ'_solm, A'_solm, hcoin_solm, hEnv, rfl, hσ'⟩

/-- A synthetic ABI that always encodes the chosen raw calldata.  This lets raw `callViaEVM`
    transport reuse the typed-call account-map bridge without adding a second trusted axiom. -/
def rawCallTransportConfig (storage : StorageLayout) (calldata : ByteArray) : Config :=
  { storage := storage
    externalABI :=
      { encode? := fun _ _ => some calldata
        decode? := fun _ _ => none }
    selfDeployment := fun _ _ => none }

/-- Raw low-level call transport across observationally equivalent account maps. -/
theorem callViaEVM_accountMapEquiv {storage : StorageLayout}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray} {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm_evm tgt value calldata (z, evm'_evm, out))
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hSubstate : evm_solm.substate = evm_evm.substate)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM evm_solm tgt value calldata
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  let cfg := rawCallTransportConfig storage calldata
  have htyped : typedCallViaEVM cfg evm_evm tgt "" value [] (z, evm'_evm, out) :=
    ⟨calldata, rfl, hcall⟩
  obtain ⟨σ'_solm, A'_solm, htyped_solm, hσ'⟩ :=
    typedCallViaEVM_accountMapEquiv htyped hAccounts hOriginalAccounts hCreated hGenesis hBlocks
      hSubstate hEnv
  rcases htyped_solm with ⟨calldata', henc, hraw⟩
  simp only [cfg, rawCallTransportConfig] at henc
  cases henc
  exact ⟨σ'_solm, A'_solm, hraw, hσ'⟩

/-- `initState`-specialized raw low-level call transport. -/
theorem callViaEVM_initState_accountMapEquiv {storage : StorageLayout}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {evm'_evm : EVM.State} {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM (initState cA gh bl σ_evm σ₀ g A I) tgt value calldata
      (z, evm'_evm, out))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM (initState cA gh bl σ_solm σ₀ g A I) tgt value calldata
        (z,
          { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm :=
  callViaEVM_accountMapEquiv (storage := storage)
    (evm_solm := initState cA gh bl σ_solm σ₀ g A I) hcall
    (by simpa [initState] using hAccounts)
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])

/-- `EVMStateEquiv`-returning form of raw low-level call transport. -/
theorem callViaEVM_initState_EVMStateEquiv {storage : StorageLayout}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {evm'_evm : EVM.State} {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM (initState cA gh bl σ_evm σ₀ g A I) tgt value calldata
      (z, evm'_evm, out))
    (hEnv : evm'_evm.executionEnv = (initState cA gh bl σ_solm σ₀ g A I).executionEnv)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM (initState cA gh bl σ_solm σ₀ g A I) tgt value calldata
        (z,
          { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      EVMStateEquiv evm'_evm
        { initState cA gh bl σ_solm σ₀ g A I with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := evm'_evm.createdAccounts } := by
  obtain ⟨σ'_solm, A'_solm, hcall_solm, hσ'⟩ :=
    callViaEVM_initState_accountMapEquiv (storage := storage) hcall hAccounts
  exact ⟨σ'_solm, A'_solm, hcall_solm, hEnv, rfl, hσ'⟩

/-- **Coincidence (call not made).**  At the call-depth limit (`evm.depth = 1024`) the EVM `CALL`
    returns `0` *without* invoking `Θ`; the Solm `externalCallViaEVM` takes the matching
    `callNotMade` branch — `(false, evm[substate], ∅)` — independent of value/balance.  Generic over
    config / callee name / arguments (value `0`). -/
theorem callNotMade_depthLimit {cfg : Config} {evm : EVM.State} {tgt : EVM.Address}
    {name : Ident} {args : List Value} {calldata : ByteArray}
    (hcd : cfg.externalABI.encode? name args = some calldata)
    (hdepth : evm.executionEnv.depth = 1024) :
    typedCallViaEVM cfg evm tgt name 0 args
      (false, { evm with substate := (evm.addAccessedAccount tgt).substate }, ByteArray.empty) := by
  refine ⟨calldata, hcd, ?_⟩
  apply callViaEVM.callNotMade rfl rfl
  rintro ⟨_, hne⟩
  exact hne hdepth

end Reasoning.Theory
