import Solm.Equiv

/-!
# Behavioral inclusion

`runtimeEquivalence` is a refinement: on every admissible input, the behavior of the bytecode is
a behavior of the specification.  The relation is defined by four cases; this file states the
inclusion as a theorem, so that it can be cited on its own.

A specification behavior at fixed inputs is either an outcome of the message-level judgment
`solmExec`, or the rejection of calldata that selects no transition or does not decode.  The
bytecode's result is captured by the first through `execResultsEquiv`, and by the second by
reverting.  The only bytecode behavior outside the inclusion is running out of gas.
-/

namespace Solm

open ABI

/-- The EVM result type of `Ethereum.EVM.Ξ`. -/
abbrev EVMResult :=
  Except Ethereum.EVM.ExecutionException
    (Ethereum.ExecutionResult
      (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap ×
        Ethereum.UInt256 × Ethereum.Substate))

/-- The specification rejects the calldata: no transition (nor `receive`/`fallback`) accepts it,
    or the selected transition's calldata does not decode. -/
def specRejects (cfg : Config) (contract : ContractDecl) (calldata : ByteArray) : Prop :=
  dispatchMsg contract calldata = .none ∨
  ∃ transition, selectorDispatchMsg contract calldata = .some transition ∧
    decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      (transitionSignature transition).paramTypes calldata = .none

/-- A bytecode result `r` is captured by the specification, run from the Solm-side inputs:
    either some run of the specification is `execResultsEquiv`-related to `r`, or the
    specification rejects the calldata and `r` is a revert. -/
def capturedBySpec (cfg : Config) (contract : ContractDecl)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_solm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (r : EVMResult) : Prop :=
  (∃ solmRes returnConvention,
      solmExec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
        solmRes returnConvention ∧
      execResultsEquiv r solmRes returnConvention) ∨
  (specRejects cfg contract I.calldata ∧ ∃ g' o, r = .ok (.revert g' o))

/-- Behavioral inclusion at fixed inputs: a `runtimeEquivalenceFor` derivation says that the
    bytecode's result is out of gas or captured by the specification. -/
theorem runtimeEquivalenceFor_captured {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader} {blocks : Ethereum.ProcessedBlocks}
    {σ_evm σ_solm σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (h : runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks
      σ_evm σ_solm σ₀ g A I) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
      (Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I) := by
  cases h with
  | execution hΞ hsolm hequiv =>
      right; left
      exact ⟨_, _, hsolm, by rw [hΞ]; exact hequiv⟩
  | noDispatch hdisp hΞ =>
      right; right
      exact ⟨Or.inl hdisp, _, _, hΞ⟩
  | decodingFailed hsel hsig hdec hΞ =>
      right; right
      subst hsig
      exact ⟨Or.inr ⟨_, hsel, hdec⟩, _, _, hΞ⟩
  | outOfGas hΞ =>
      left; exact hΞ

/-- **Behavioral inclusion.**  If the bytecode refines the specification, then on every admissible
    input (the deployed code, calldata shorter than `2^256` bytes, write permission set, related
    initial account maps) the bytecode's unique result is either out of gas or captured by a
    behavior of the specification.  No other behavior of the bytecode exists. -/
theorem runtimeEquivalence_behaviors_included {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} (h : runtimeEquivalence cfg bytecode contract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_solm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
      (Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I) := by
  obtain ⟨hrun⟩ := h
  exact runtimeEquivalenceFor_captured
    (hrun createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts)

/-- The same inclusion for relations carrying a storage well-formedness precondition. -/
theorem runtimeEquivalenceWithWF_behaviors_included {wf : StorageWF} {cfg : Config}
    {bytecode : ByteArray} {contract : ContractDecl}
    (h : runtimeEquivalenceWithWF wf cfg bytecode contract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ_solm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true) (hAccounts : accountMapEquiv σ_evm σ_solm) (hwf : wf σ_evm I) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
      (Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I) := by
  obtain ⟨hrun⟩ := h
  exact runtimeEquivalenceFor_captured
    (hrun createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts hwf)

/-- A captured result is never an exceptional halt other than `INVALID`. -/
theorem capturedBySpec_error {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader} {blocks : Ethereum.ProcessedBlocks}
    {σ_solm σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {e : Ethereum.EVM.ExecutionException}
    (h : capturedBySpec cfg contract createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
      (.error e)) :
    e = .InvalidInstruction := by
  rcases h with ⟨_, _, _, hequiv⟩ | ⟨_, _, _, hrev⟩
  · cases hequiv with
    | success h1 _ _ _ _ => exact absurd h1 (by simp)
    | revert h1 _ => exact absurd h1 (by simp)
    | invalidHalt h1 _ => exact Except.error.inj h1
  · exact absurd hrev (by simp)

/-- **No crash.**  A refined bytecode never halts with an exception other than out-of-gas or
    `INVALID` on an admissible input: no stack under- or overflow, invalid jump, invalid opcode,
    or static-mode violation is reachable. -/
theorem runtimeEquivalence_no_crash {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} (h : runtimeEquivalence cfg bytecode contract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_evm σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true) {e : Ethereum.EVM.ExecutionException}
    (herr : Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I = .error e) :
    e = .OutOfGass ∨ e = .InvalidInstruction := by
  rcases runtimeEquivalence_behaviors_included h createdAccounts genesisBlockHeader blocks
      σ_evm σ_evm σ₀ g A I hcode hsize hperm (accountMapEquiv.refl σ_evm) with hoog | hcap
  · left; rw [herr] at hoog; exact Except.error.inj hoog
  · right; rw [herr] at hcap; exact capturedBySpec_error hcap

end Solm
