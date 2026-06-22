import Reasoning.SolmBody

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

/-- Trusted bridge: `Θ` respects observationally equivalent account maps.

If a typed external call is possible from an EVM state, and a Solm-side state differs only by
`accountMapEquiv`-equivalent current/original account maps, then the same success flag and return
data are possible on the Solm side, with a post-call account map equivalent to the EVM post-call
map.  This is the narrow interface needed by examples; it should be replaced by the direct proof
about `Ethereum.EVM.Θ` once that proof lands. -/
axiom typedCallViaEVM_accountMapEquiv {cfg : Config} {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value} {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm_evm tgt name 0 args (z, evm'_evm, out))
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : accountMapEquiv evm_evm.σ₀ evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hSubstate : evm_solm.substate = evm_evm.substate)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name 0 args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm

/-- `initState`-specialized form of `typedCallViaEVM_accountMapEquiv`.

This is the shape runtime-equivalence examples usually need: the EVM and Solm runs start from
split-but-equivalent account maps while all other transaction fields are shared. -/
theorem typedCallViaEVM_initState_accountMapEquiv {cfg : Config}
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : Sat256}
    {evm'_evm : EVM.State} {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg (initState cA gh bl σ_evm σ₀_evm g A I) tgt name 0 args
      (z, evm'_evm, out))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg (initState cA gh bl σ_solm σ₀_solm g A I) tgt name 0 args
        (z,
          { initState cA gh bl σ_solm σ₀_solm g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm :=
  typedCallViaEVM_accountMapEquiv
    (evm_solm := initState cA gh bl σ_solm σ₀_solm g A I) hcall
    (by simpa [initState] using hAccounts)
    (by simpa [initState] using hOriginalAccounts)
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])
    (by simp [initState])

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
