import Reasoning.SolmBody
import Reasoning.Storage

import Ethereum.Theory.StaticStorage

/-!
# ExternalCall — the `CALL` ↔ `externalCall` coupling

The Solm↔EVM boundary for a contract's **external call**, the peer of `Reasoning/Dispatch.lean`
(which couples the transaction entry / dispatcher).  An EVM `CALL` (exposed by `RD.call` as a
`Θ`-link) and the Solm `externalCall` (the `typedCallViaEVM` relation) invoke the *identical* `Θ`
with the same arguments, so the opaque result `(z, σ', o)` coincides on both sides **by
construction** — no assumption about the callee's code.

`callCoincides` is generic over the contract config / callee name / argument values; a per-contract
proof only supplies the trace **couplings** (the target address it masked, and the calldata it built
in memory = the ABI encoding) — exactly as the dispatcher consumes a per-contract selector fact.
`callNotMade_depthLimit` is the call-depth-limit counterpart (the `CALL` returns `0` without `Θ`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Theory


/-- **Coincidence (call made).**  Given the EVM-side `Θ`-link produced by `RD.call` (with witnesses
    `A_in`, `callGas`) and the trace couplings — the Solm target `tgt` is the cleaned stack address
    (`htgt`), and the ABI encoding of `name args` is exactly the calldata the bytecode placed in
    memory (`hcd`) — the Solm `typedCallViaEVM` holds for the *same* opaque `(z, σ', o)`.
    Instantiate the Solm existentials with the EVM witnesses; `Θ`'s determinism does the rest.
    Generic over the config / callee name / arguments (value `0`).  The `Θ`-link carries the
    callee permission `callPerm && evm.executionEnv.perm`: for a `CALL` (`callPerm = true`) this
    is the caller's own bit, as `RD.call` produces it; for a `STATICCALL` it is `false`. -/
theorem callCoincides {cfg : Config} {evm : EVM.State} {name : Ident} {args : List Value}
    {tgt : EVM.Address} {targetWord : UInt256}
    {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {o : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool}
    (hdepth : evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args
            = some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (σ', g'', A', z, o) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 targetWord) (toExecute evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
          (callPerm && evm.executionEnv.perm)) :
    typedCallViaEVM cfg evm tgt name 0 args
      (z, { evm with accountMap := σ', substate := A' }, o)
      callPerm := by
  -- rewrite the EVM `Θ`-link into the Solm form (round-trip sender, `tgt`)
  have h := hΘ
  rw [accountAddress_roundtrip, ← htgt] at h
  exact ⟨mem.readWithPadding inOff.toNat inSize.toNat, hcd,
    callViaEVM.callMade (perm := callPerm) wordOfInt_zero.symm ⟨callGas, A_in, h⟩ rfl
      (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _) hdepth⟩

theorem typedCallViaEVM_executionEnv_eq {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm target name value args (z, evm', out) perm) :
    evm'.executionEnv = evm.executionEnv := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  cases hraw with
  | callMade _hvalue _hTheta hevm' _hvalue' _hdepth =>
      subst hevm'
      rfl
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      rfl

theorem callViaEVM_static_accountStorageStateEq {evm evm' : EVM.State}
    {target : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm target value calldata (z, evm', out) false) :
    accountStorageStateEq evm.accountMap evm'.accountMap := by
  cases hcall with
  | callMade _hvalue hTheta hevm' _hvalue' _hdepth =>
      rcases hTheta with ⟨_callGas, _A_in, hΘ⟩
      subst hevm'
      exact Theta_static_accountStorageStateEq hΘ.symm
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      exact accountStorageStateEq_refl evm.accountMap

theorem typedCallViaEVM_static_accountStorageStateEq {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    accountStorageStateEq evm.accountMap evm'.accountMap := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  exact callViaEVM_static_accountStorageStateEq hraw

theorem callViaEVM_static_accountCodeStateEq {evm evm' : EVM.State}
    {target : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm target value calldata (z, evm', out) false) :
    accountCodeStateEq evm.accountMap evm'.accountMap := by
  cases hcall with
  | callMade _hvalue hTheta hevm' _hvalue' _hdepth =>
      rcases hTheta with ⟨_callGas, _A_in, hΘ⟩
      subst hevm'
      exact Theta_static_accountCodeStateEq hΘ.symm
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      exact accountCodeStateEq_refl evm.accountMap

theorem typedCallViaEVM_static_accountCodeStateEq {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    accountCodeStateEq evm.accountMap evm'.accountMap := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  exact callViaEVM_static_accountCodeStateEq hraw

/-- A static typed call preserves the caller's storage value when the input
account map is equal to the source map. -/
theorem typedCallViaEVM_static_storage_getD_of_accounts_eq {cfg : Config}
    {σ : AccountMap} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} (slot default : UInt256)
    (hAccounts : σ = evm.accountMap)
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    ((evm'.accountMap.get? evm'.executionEnv.codeOwner).option default
        (fun acc => acc.storage.getD slot default)) =
      ((σ.get? evm.executionEnv.codeOwner).option default
        (fun acc => acc.storage.getD slot default)) := by
  have hStaticAccounts : accountStorageStateEq evm.accountMap evm'.accountMap :=
    typedCallViaEVM_static_accountStorageStateEq hcall
  have henv : evm'.executionEnv = evm.executionEnv :=
    typedCallViaEVM_executionEnv_eq hcall
  have hstaticSlot :=
    accountStorageStateEq_storage_getD hStaticAccounts
      evm.executionEnv.codeOwner slot default
  rw [henv, ← hstaticSlot]
  subst σ
  rfl

/-- A raw call can be replayed from a state with the same inputs to the EVM call relation.
Only the account map, original account map, and execution environment affect the call.
The resulting state keeps the other fields of the new starting state. -/
theorem callViaEVM_sameInputs
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : callViaEVM evm_evm tgt value calldata (z, evm'_evm, out) callPerm)
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM evm_solm tgt value calldata
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      evm'_evm.accountMap = σ'_solm := by
  cases hcall with
  | callMade hvalue hTheta hevm' hbalance hdepth =>
      obtain ⟨callGas, A_in, hTheta⟩ := hTheta
      rename_i valueWord σ' g' A'
      refine ⟨σ', A', ?_, ?_⟩
      · refine callViaEVM.callMade (perm := callPerm) (g' := g') hvalue
          ⟨callGas, A_in, ?_⟩ rfl ?_ ?_
        · simpa [← hAccounts, ← hOriginalAccounts, ← hEnv] using hTheta
        · simpa [← hAccounts, ← hEnv] using hbalance
        · simpa [← hEnv] using hdepth
      · simp [hevm']
  | callNotMade hsubstate hevm' hblocked =>
      let A'_solm := (evm_solm.addAccessedAccount tgt).substate
      refine ⟨evm_solm.accountMap, A'_solm, ?_, ?_⟩
      · apply callViaEVM.callNotMade (perm := callPerm) rfl rfl
        simpa [← hAccounts, ← hEnv] using hblocked
      · simpa [hevm'] using hAccounts

/-- The typed call transports through the same equal EVM call inputs. -/
theorem typedCallViaEVM_sameInputs
    {cfg : Config} {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      evm'_evm.accountMap = σ'_solm := by
  obtain ⟨calldata, hencode, hraw⟩ := hcall
  obtain ⟨σ', A', hraw', hσ'⟩ :=
    callViaEVM_sameInputs hraw hAccounts hOriginalAccounts hEnv
  exact ⟨σ', A', ⟨calldata, hencode, hraw'⟩, hσ'⟩

/-- Replay a typed call from equal call inputs and relate the resulting EVM states. -/
theorem typedCallViaEVM_sameInputs_stateEquiv
    {cfg : Config} {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      EVMStateEquiv evm'_evm
        { evm_solm with accountMap := σ'_solm, substate := A'_solm } := by
  obtain ⟨σ', A', hcall', hσ'⟩ :=
    typedCallViaEVM_sameInputs hcall hAccounts hOriginalAccounts hEnv
  exact ⟨σ', A', hcall', ⟨(typedCallViaEVM_executionEnv_eq hcall).trans hEnv, hσ'⟩⟩

/-- Couple the EVM call trace to a typed call, then replay it from equal call inputs. -/
theorem typedCallViaEVM_callMade_sameInputs {cfg : Config}
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {targetWord : UInt256} {name : Ident} {args : List Value}
    {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool}
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header
          evm_evm.executionEnv.blobVersionedHashes evm_evm.executionEnv.blocks
          (callPerm && evm_evm.executionEnv.perm))
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_evm.executionEnv = evm_solm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name 0 args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      σ' = σ'_solm := by
  have hcall : typedCallViaEVM cfg evm_evm tgt name 0 args
      (z, { evm_evm with accountMap := σ', substate := A' }, out) callPerm :=
    callCoincides hdepth htgt hcd hΘ
  simpa using
    typedCallViaEVM_sameInputs hcall hAccounts hOriginalAccounts hEnv

/-- **Coincidence (call not made).**  At the call-depth limit (`evm.depth = 1024`) the EVM `CALL`
    returns `0` *without* invoking `Θ`; the Solm `typedCallViaEVM` takes the matching
    `callNotMade` branch — `(false, evm[substate], ∅)` — independent of value/balance.  Generic over
    config / callee name / arguments (value `0`). -/
theorem callNotMade_depthLimit {cfg : Config} {evm : EVM.State} {tgt : EVM.Address}
    {name : Ident} {args : List Value} {calldata : ByteArray} {callPerm : Bool}
    (hcd : cfg.externalABI.encode? name args = some calldata)
    (hdepth : evm.executionEnv.depth = 1024) :
    typedCallViaEVM cfg evm tgt name 0 args
      (false, { evm with substate := (evm.addAccessedAccount tgt).substate }, ByteArray.empty)
      callPerm := by
  refine ⟨calldata, hcd, ?_⟩
  apply callViaEVM.callNotMade (perm := callPerm) rfl rfl
  rintro ⟨_, hne⟩
  exact hne hdepth

theorem rawZeroCall_source_of_theta
    {evm : EVM.State} {s0 : State} {I : ExecutionEnv}
    {σ σ' : AccountMap}
    {targetWord callGas : UInt256} {A_in : Substate} {z : Bool} {data out : ByteArray}
    (hAccounts : σ = evm.accountMap) (henv : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hΘ : ∃ (g'' : UInt256) (A' : Substate),
      (σ', g'', A', z, out) =
        Ethereum.EVM.Θ σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 targetWord) (toExecute σ (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩ data (I.depth + 1)
          I.header I.blobVersionedHashes I.blocks I.perm) :
    ∃ evm', callViaEVM evm (AccountAddress.ofUInt256 targetWord) 0 data (z, evm', out) ∧
      σ' = evm'.accountMap ∧ evm'.σ₀ = s0.σ₀ ∧ evm'.executionEnv = I := by
  let evmE : EVM.State :=
    { evm with
      accountMap := σ
      σ₀ := s0.σ₀
      executionEnv := I }
  obtain ⟨g', A', hΘ⟩ := hΘ
  have hcallE : callViaEVM evmE (AccountAddress.ofUInt256 targetWord) 0 data
      (z, { evmE with accountMap := σ', substate := A' }, out) := by
    refine callViaEVM.callMade (perm := true) (g' := g') wordOfInt_zero.symm ?_ rfl ?_ ?_
    · refine ⟨callGas, A_in, ?_⟩
      simpa only [evmE, hperm, accountAddress_roundtrip] using hΘ
    · exact Fin.zero_le _
    · intro h
      have hlt := hdepth
      change I.depth = 1024 at h
      rw [h] at hlt
      exact absurd hlt (by decide)
  have hevmE : evmE = evm := by
    cases evm
    simp_all [evmE]
  refine ⟨{ evm with accountMap := σ', substate := A' }, ?_, rfl, ?_, ?_⟩
  · simpa [hevmE] using hcallE
  · exact hσ0
  · exact henv

structure SourceState (s0 : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (evm : EVM.State) : Prop where
  world : evm.σ₀ = s0.σ₀
  env : evm.executionEnv = I
  accounts : σ = evm.accountMap

theorem SourceState.init {σ σ₀ A I g} :
    SourceState (initState σ σ₀ g A I) I σ (initState σ σ₀ g A I) :=
  ⟨rfl, rfl, rfl⟩

theorem SourceState.storageRead {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = solcSlotWord σ I slot := by
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    ← hs.accounts, hs.env]

def callState (evm : EVM.State) (σ : AccountMap) : EVM.State :=
  { evm with accountMap := σ }

theorem SourceState.callTransport {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target : EVM.Address} {value : Int} {calldata : ByteArray}
    {z : Bool} {evm' : EVM.State} {out : ByteArray}
    (hcall : callViaEVM (callState evm σ) target value calldata (z, evm', out)) :
    ∃ evmS', callViaEVM evm target value calldata (z, evmS', out) ∧
      SourceState s0 I evm'.accountMap evmS' := by
  have hstate : callState evm σ = evm := by
    cases evm
    simpa [callState] using hs.accounts
  rw [hstate] at hcall
  have hpost : evm'.σ₀ = evm.σ₀ ∧ evm'.executionEnv = evm.executionEnv := by
    cases hcall with
    | callMade _ _ hevm' _ _ => simp [hevm']
    | callNotMade _ hevm' _ => simp [hevm']
  exact ⟨evm', hcall, ⟨hpost.1.trans hs.world, hpost.2.trans hs.env, rfl⟩⟩

theorem callStateMade {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target value : UInt256} {calldata : ByteArray}
    {σ' : AccountMap} {gasLeft callGas : UInt256} {AS' AIn : Substate} {z : Bool} {out : ByteArray}
    (hperm : I.perm = true)
    (hbalance : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (hΘ : (σ', gasLeft, AS', z, out) = Θ σ s0.σ₀ AIn
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
      callGas (UInt256.ofNat I.gasPrice) value value calldata (I.depth + 1) I.header
      I.blobVersionedHashes I.blocks I.perm) :
    callViaEVM (callState evm σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (z,
        { callState evm σ with
          accountMap := σ'
          substate := AS' }, out) := by
  apply callViaEVM.callMade (valueWord := value) (g' := gasLeft) (A' := AS')
    (wordOfInt_ofNat_toNat value).symm ?_ rfl ?_ ?_
  · refine ⟨callGas, AIn, ?_⟩
    simp only [callState, hs.env]
    rw [hs.world]
    simpa only [accountAddress_roundtrip, hperm] using hΘ
  · simpa only [callState, hs.env] using hbalance
  · simp only [callState, hs.env]
    intro hd
    have hval := congrArg Fin.val hd
    change I.depth.val = 1024 at hval
    omega

theorem callStateNotMade {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target value : UInt256} {calldata : ByteArray}
    (hn : ¬ (value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024)) :
    callViaEVM (callState evm σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (false,
        { callState evm σ with substate :=
          ((callState evm σ).addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
        ByteArray.empty) := by
  apply callViaEVM.callNotMade rfl rfl
  simpa only [callState, hs.env, wordOfInt_ofNat_toNat] using hn

theorem callBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD code I g s0 pc
      (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
        calldata (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨_, _, rd⟩ := h.callValueDepthLimit hperm hdec hd hov
    have hraw := callStateNotMade (target := target) (value := value) (calldata := calldata)
      hs (fun hn => hn.2 hd)
    obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
    exact ⟨evm', σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := by
        intro hv
        exact hd (Fin.ext hv)
      omega
    by_cases hb : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance))
    · obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨gasLeft, AS', hΘ⟩, rd, _⟩ :=
        h.callValueMade hdec hperm hb hdlt hov
      rw [hcd] at hΘ
      have ho : out.size < 2 ^ 138 :=
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
      have hraw := callStateMade hs hperm hb hdlt hΘ
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', σ', z, out, k', C', hcall, hs', rd, ho⟩
    · obtain ⟨_, _, rd⟩ := h.callValueInsufficientBalance hperm hdec hb hdlt hov
      have hraw := callStateNotMade (target := target) (value := value) (calldata := calldata)
        hs (fun hn => hb hn.1)
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩

theorem SourceState.storageWrite {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot value : UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ slot value)
      (Solm.EVM.storageStore evm I.codeOwner slot value) := by
  refine ⟨?_, (storageStore_executionEnv _ _ _ _).trans hs.env, ?_⟩
  · unfold Solm.EVM.storageStore
    cases evm.lookupAccount I.codeOwner <;> exact hs.world
  · rw [storageStore_accountMap]
    rw [hs.accounts]

theorem SourceState.readModifyWrite {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot : UInt256) (f : UInt256 → UInt256) :
    SourceState s0 I (sstoreAccountMap I.codeOwner σ slot (f (solcSlotWord σ I slot)))
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [hs.storageRead, hs.env]
  exact hs.storageWrite _ _

theorem extCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using Nat.pos_of_ne_zero htoNatNe

theorem extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hword

theorem lowLevelCallSource {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver eth cdata : Expr} {target : AccountAddress} {value : Int} {calldata out : ByteArray}
    {success data : Ident} {z : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hv : evalExpr? cfg frame evm eth = .ok (.int value))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : callViaEVM evm target value calldata (z, evm', out)) :
    ExecStmt cfg frame evm (.lowLevelCall receiver eth cdata success data)
      (.ok { frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out) }
        evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    change target.val % AccountAddress.size = target.val
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.lowLevelCallFailure hr hv hd hc
  | true => exact ExecStmt.lowLevelCallSuccess hr hv hd hc

theorem extCodeSource {cfg frame evm σ target receiver}
    (hs : σ = evm.accountMap)
    (hr : evalExpr? cfg frame evm receiver =
      .ok (.address (AccountAddress.ofUInt256 target))) :
    evalExpr? cfg frame evm (.extCodeSize receiver) =
      .ok (.int (Int.ofNat (extCodeSizeWord σ target).toNat)) := by
  simp only [evalExpr?, hr, pure, bind, EvalResult.bind]
  rw [hs]
  unfold State.lookupAccount extCodeSizeWord
  cases evm.accountMap.get? (AccountAddress.ofUInt256 target) <;> rfl

theorem evalExpr_extCodeGuard_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? cfg { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_extCodeGuard_false {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? cfg { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_codeGuard_of_accounts_eq {cfg : Config}
    {σ : AccountMap} {evm : EVM.State} {frame : Frame} {receiver : Expr}
    {target : UInt256} {addr : AccountAddress}
    (hAccounts : Eq σ evm.accountMap)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address addr)) :
    evalExpr? cfg frame evm (.binary .gt (.extCodeSize receiver) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord σ target).toNat))) := by
  have hword : EVM.Word.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
      extCodeSizeWord σ target := by
    rw [congrArg (fun accounts => extCodeSizeWord accounts target) hAccounts]
    cases hacc : evm.accountMap.get? addr <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, extCodeSizeWord,
        ← haddr, hacc, Option.option] <;> rfl
  simp [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?, hword]

theorem typedCallViaEVM_zero_setSubstate {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A' },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

theorem typedCallViaEVM_zero_substate_irrel {cfg : Config} {evm evm' : EVM.State}
    {A0 : Substate} {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
      (z, evm', out) callPerm)
    (hdepth : evm.executionEnv.depth ≠ 1024) :
    typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) callPerm := by
  rcases hcall with ⟨calldata, henc, hraw⟩
  refine ⟨calldata, henc, ?_⟩
  cases hraw with
  | callMade hvalue hTheta hevm' hvalue' hdepth' =>
      obtain ⟨callGas, A_in, hTheta⟩ := hTheta
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, by simpa using hTheta⟩
        (by simpa using hevm')
        (by simpa using hvalue')
        (by simpa using hdepth')
  | callNotMade _hsubstate _hevm' hvalue =>
      exfalso
      apply hvalue
      constructor
      · rw [wordOfInt_zero]
        show (⟨0⟩ : UInt256) ≤ _
        exact Fin.zero_le _
      · exact hdepth

theorem typedCallViaEVM_preservesBase {cfg : Config}
    {evm evm' : EVM.State} {tgt : EVM.Address} {name : Ident}
    {value : ℤ} {args : List Value} {z : Bool} {out : ByteArray}
    {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name value args
      (z, evm', out) callPerm) :
    evm'.σ₀ = evm.σ₀ ∧ evm'.executionEnv = evm.executionEnv := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  cases hraw with
  | callMade _hvalue _hTheta hevm' _hvalue' _hdepth =>
      subst hevm'
      exact ⟨rfl, rfl⟩
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      exact ⟨rfl, rfl⟩

theorem typedCallViaEVM_syncFromState {cfg : Config}
    {evmEvm evmSolm evmEvm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hAccounts : evmEvm.accountMap = evmSolm.accountMap)
    (hSigma0 : evmSolm.σ₀ = evmEvm.σ₀)
    (hEnv : evmSolm.executionEnv = evmEvm.executionEnv)
    (hcall : typedCallViaEVM cfg evmEvm tgt name value args
      (z, evmEvm', out) callPerm) :
    ∃ evmSolm',
      typedCallViaEVM cfg evmSolm tgt name value args
        (z, evmSolm', out) callPerm ∧
      evmEvm'.accountMap = evmSolm'.accountMap ∧
      evmSolm'.σ₀ = evmEvm'.σ₀ ∧
      evmSolm'.executionEnv = evmEvm'.executionEnv := by
  have hbase := typedCallViaEVM_preservesBase hcall
  obtain ⟨σSolm', ASolm', hcallSolm, hAccounts'⟩ :=
    Reasoning.Theory.typedCallViaEVM_sameInputs hcall hAccounts hSigma0.symm hEnv.symm
  let evmSolm' : EVM.State :=
    { evmSolm with accountMap := σSolm', substate := ASolm' }
  refine ⟨evmSolm', ?_, ?_⟩
  · simpa [evmSolm'] using hcallSolm
  · refine ⟨?_, ?_, ?_⟩
    · simpa [evmSolm'] using hAccounts'
    · simpa [evmSolm'] using hSigma0.trans hbase.1.symm
    · simpa [evmSolm'] using (hbase.2.trans hEnv.symm).symm

theorem callMade_accountMapEq_with_substate {cfg : Config}
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {targetWord : UInt256} {name : Ident} {args : List Value}
    {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool}
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header
          evm_evm.executionEnv.blobVersionedHashes evm_evm.executionEnv.blocks
          (callPerm && evm_evm.executionEnv.perm))
    (hAccounts : evm_evm.accountMap = evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name 0 args
        (z, { evm_solm with accountMap := σ'_solm, substate := A'_solm }, out)
        callPerm ∧
      σ' = σ'_solm ∧ A' = A'_solm := by
  have hΘ_s :
      (σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_solm.accountMap evm_solm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_solm.executionEnv.codeOwner))
          evm_solm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_solm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_solm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
          evm_solm.executionEnv.blobVersionedHashes evm_solm.executionEnv.blocks
          (callPerm && evm_solm.executionEnv.perm) := by
    rw [← hAccounts, ← hOriginalAccounts, hEnv]
    exact hΘ
  have hdepthSolm : evm_solm.executionEnv.depth ≠ 1024 := by
    rw [hEnv]
    exact hdepth
  refine ⟨σ', A', ?_, rfl, rfl⟩
  exact callCoincides hdepthSolm htgt hcd hΘ_s

end Reasoning.Theory

/-! ## Code-size guards and precompile results -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

/-- Code size at an address transports across `EVMStateEquiv` (`Eq` preserves code). -/
theorem codeW_eq_of_equiv {a b : EVM.State} (addr : AccountAddress) (h : EVMStateEquiv a b) :
    UInt256.ofNat ((a.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
      UInt256.ofNat ((b.lookupAccount addr).option 0 (fun acc => acc.code.size)) := by
  simpa only [State.lookupAccount, h.accountMap]

/-- `extCodeSizeWord` reads only an account's `.code` (as `ofNat · .code.size`), so it is a
    function of `(σ.getD a default).code` — the projection `accountCodeStateEq` preserves. -/
theorem extCodeSizeWord_eq_ofNat_getD (σ : AccountMap) (target : UInt256) :
    Reasoning.Theory.extCodeSizeWord σ target
      = UInt256.ofNat (σ.getD (AccountAddress.ofUInt256 target) default).code.size := by
  unfold Reasoning.Theory.extCodeSizeWord
  cases h : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      have hdefault : (default : Account).code.size = 0 := by
        decide
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
        ← Std.ExtTreeMap.get?_eq_getElem?, Option.option, hdefault, h]
      rfl
  | some acc =>
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
        ← Std.ExtTreeMap.get?_eq_getElem?, Option.option, h]

/-- Code preservation transfers to `extCodeSizeWord`: static calls leave every account's
    `EXTCODESIZE` word unchanged. -/
theorem extCodeSizeWord_eq_of_accountCodeStateEq {σ σ' : AccountMap} (target : UInt256)
    (h : accountCodeStateEq σ σ') :
    Reasoning.Theory.extCodeSizeWord σ' target
      = Reasoning.Theory.extCodeSizeWord σ target := by
  rw [extCodeSizeWord_eq_ofNat_getD, extCodeSizeWord_eq_ofNat_getD,
    (h (AccountAddress.ofUInt256 target)).symm]

theorem extCodeSizeWord_eq (σ : AccountMap) (target : UInt256) :
    extCodeSizeWord σ target =
      UInt256.ofNat ((σ.get? (AccountAddress.ofUInt256 target)).option 0
        (fun acc => acc.code.size)) := by
  unfold extCodeSizeWord
  cases σ.get? (AccountAddress.ofUInt256 target) <;> rfl

theorem toExecute_ecrecover_precompile (σ : AccountMap) :
    toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
  unfold toExecute
  have hmem : AccountAddress.ofUInt256 (⟨1⟩ : UInt256) ∈ π := by
    unfold π
    decide
  rw [if_pos hmem]

theorem ecrecover_output_size (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    let r := Ξ_ECREC σ g A I
    r.2.2.2.size = 0 ∨ r.2.2.2.size = 32 := by
  unfold Ξ_ECREC
  dsimp
  split
  · left
    rfl
  · split
    · left
      rfl
    · split
      · right
        rw [ByteArray.size_append]
        rw [ByteArray_zeroes_size]
        rw [ByteArray.size_extract]
        rw [keccak_size]
        decide
      · left
        rfl

theorem staticcallTheta_ecrecover_output_size
    {blobVersionedHashes blocks σ σ₀ A_in r s g p v v' d e H w σ' g' A' z o}
    (hΘ : (σ', g', A', z, o) =
      Θ σ σ₀ A_in r s
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          g p v v' d e H blobVersionedHashes blocks w) :
    o.size = 0 ∨ o.size = 32 := by
  have hpre : toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
    exact toExecute_ecrecover_precompile σ
  have hone : (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) = 1 := by
    decide
  have hout := congrArg (fun x => x.2.2.2.2.size) hΘ
  have hout' :
      o.size =
        (Θ σ σ₀ A_in r s
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          g p v v' d e H blobVersionedHashes blocks w).2.2.2.2.size := by
    simpa using hout
  rw [hout']
  unfold Θ
  rw [hpre, hone]
  dsimp
  exact ecrecover_output_size _ g A_in _

theorem code_zero_of_codeSize_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) haddr hzero

theorem code_pos_of_codeSize_ne_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord evm.accountMap target := by
    subst addr
    cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 target) <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount,
        Reasoning.Theory.extCodeSizeWord, hacc,
        Option.option] <;>
      decide
  exact hne (by rw [← hword, hwordZero])

theorem code_zero_of_state_codeSize_zero {evm : EVM.State} {targetWord : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap targetWord = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat targetWord]
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 targetWord) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc] using hword

theorem code_pos_of_state_codeSize_ne {evm : EVM.State} {targetWord : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap targetWord ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat targetWord]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 targetWord) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount,
        hacc] using Nat.pos_of_ne_zero htoNatNe

theorem addressWordCode_zero_of_state {evm : EVM.State} (target : UInt256)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hzero

theorem addressWordCode_pos_of_state {evm : EVM.State} (target : UInt256)
    (hne : Reasoning.Theory.extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hne

theorem depth_ne_1024_of_lt {d : Fin 1025} (h : d.val < 1024) : d ≠ 1024 := by
  intro hd
  have hdval : d.val = (1024 : Fin 1025).val := congrArg Fin.val hd
  have h1024 : (1024 : Fin 1025).val = 1024 := by decide
  omega

theorem initStateDepth_ne_1024_of_lt {σ σ₀ A I g}
    (h : I.depth.val < 1024) :
    (initState σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
  simpa [initState] using depth_ne_1024_of_lt h

end Reasoning.Theory
