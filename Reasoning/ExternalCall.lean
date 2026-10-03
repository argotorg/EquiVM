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
The initState call bridges now reuse one account map, so their call result is the same by rewriting
the map equality. The generic bridge only transports the fields that the call relation reads.
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

/-- **Coincidence (call made).**  Given the EVM-side `Θ`-link produced by `RD.call` (with witnesses
    `A_in`, `callGas`) and the trace couplings — the Solm target `tgt` is the cleaned stack address
    (`htgt`), and the ABI encoding of `name args` is exactly the calldata the bytecode placed in
    memory (`hcd`) — the Solm `typedCallViaEVM` holds for the *same* opaque `(z, σ', o)`.
    Instantiate the Solm existentials with the EVM witnesses; `Θ`'s determinism does the rest.
    Generic over the config / callee name / arguments (value `0`). -/
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
          evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks callPerm) :
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
theorem typedCallViaEVM_static_storage_findD_of_accounts_eq {cfg : Config}
    {σ : AccountMap} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} (slot default : UInt256)
    (hAccounts : σ = evm.accountMap)
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    ((evm'.accountMap.find? evm'.executionEnv.codeOwner).option default
        (fun acc => acc.storage.findD slot default)) =
      ((σ.find? evm.executionEnv.codeOwner).option default
        (fun acc => acc.storage.findD slot default)) := by
  have hStaticAccounts : accountStorageStateEq evm.accountMap evm'.accountMap :=
    typedCallViaEVM_static_accountStorageStateEq hcall
  have henv : evm'.executionEnv = evm.executionEnv :=
    typedCallViaEVM_executionEnv_eq hcall
  have hstaticSlot :=
    accountStorageStateEq_storage_findD hStaticAccounts
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
          evm_evm.executionEnv.blobVersionedHashes evm_evm.executionEnv.blocks callPerm)
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

end Reasoning.Theory
