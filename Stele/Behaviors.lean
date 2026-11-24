import Stele.Refine

variable {fork : Ethereum.Fork}

/-!
# Behavioral inclusion

`runtimeRefinement` relates every bytecode result on admissible inputs to a Stele execution,
except for out-of-gas. This file states the inclusion as a theorem, so that it can be cited on
its own.

A specification behavior at fixed inputs is an outcome of the message-level judgment
`steleExec`, including `.noMatch` and `.decodingFailed`. The bytecode's result is captured
through `execResultsEquiv`; these two rejection outcomes match only EVM reverts. The only
bytecode behavior outside the inclusion is running out of gas.
-/

namespace Stele

open ABI

/-- The EVM result type of `Ethereum.EVM.Ξ`. -/
abbrev EVMResult :=
  Except Ethereum.EVM.ExecutionException
    (Ethereum.ExecutionResult
      (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate))

/-- A bytecode result `r` is captured by the specification, run from the Stele-side inputs:
    some run of `steleExec` produces a result `execResultsEquiv`-related to `r`. This includes
    dispatch and calldata-decoding failures as explicit Stele execution outcomes. -/
def capturedBySpec (fork : Ethereum.Fork) (cfg : Config) (contract : ContractDecl)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (r : EVMResult) (immutables : Store := ∅) : Prop :=
  ∃ steleRes returnConvention,
    steleExec fork cfg contract immutables σ σ₀ g A I steleRes returnConvention ∧
    execResultsEquiv r steleRes returnConvention

/-- Behavioral inclusion at fixed inputs: a `runtimeRefinementFor` derivation says that the
    bytecode's result is out of gas or captured by the specification. -/
theorem runtimeRefinementFor_captured {cfg : Config} {contract : ContractDecl}
    {σ σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {immutables : Store}
    (h : runtimeRefinementFor fork cfg contract σ σ₀ g A I immutables) :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec fork cfg contract σ σ₀ g A I
      (Ethereum.EVM.Ξ fork σ σ₀ g A I) immutables := by
  cases h with
  | execution hΞ hstele hequiv =>
      right
      exact ⟨_, _, hstele, by rw [hΞ]; exact hequiv⟩
  | outOfGas hΞ =>
      left; exact hΞ

/-- **Behavioral inclusion.**  If the bytecode refines the specification under the forks `forks`,
    then under each of them, on every admissible input (the deployed code and calldata shorter
    than `2^256` bytes), in either permission mode, the bytecode's unique result is either out of
    gas or captured by a behavior of the specification.  No other behavior of the bytecode
    exists. -/
theorem runtimeRefinement_behaviors_included {forks : ForkSet} {cfg : Config}
    {bytecode : ByteArray} {contract : ContractDecl} {immutables : Store}
    (h : runtimeRefinementOn forks cfg bytecode contract immutables)
    (fork : Ethereum.Fork) (hfork : forks fork) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size) :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec fork cfg contract σ σ₀ g A I
      (Ethereum.EVM.Ξ fork σ σ₀ g A I) immutables := by
  obtain ⟨hrun⟩ := h
  exact runtimeRefinementFor_captured
    (hrun fork hfork σ σ₀ g A I hcode hsize)

/-- The same inclusion for relations carrying a storage well-formedness precondition and a gas
    bound. -/
theorem runtimeRefinementWithWF_behaviors_included {forks : ForkSet} {wf : StorageWF}
    {gasBound : GasBound} {cfg : Config} {bytecode : ByteArray} {contract : ContractDecl}
    {immutables : Store}
    (h : runtimeRefinementWithWFOn forks wf gasBound cfg bytecode contract immutables)
    (fork : Ethereum.Fork) (hfork : forks fork) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwf : wf σ I) (hgas : gasBound g) :
    Ethereum.EVM.Ξ fork σ σ₀ g A I = .error .OutOfGass ∨
    capturedBySpec fork cfg contract σ σ₀ g A I
      (Ethereum.EVM.Ξ fork σ σ₀ g A I) immutables := by
  obtain ⟨hrun⟩ := h
  exact runtimeRefinementFor_captured
    (hrun fork hfork σ σ₀ g A I hcode hsize hwf hgas)

/-- A captured exceptional halt is `INVALID`, or a static-mode violation matched by a Stele
    `.staticViolation`. -/
theorem capturedBySpec_error {cfg : Config} {contract : ContractDecl}
    {σ_stele σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {e : Ethereum.EVM.ExecutionException} {immutables : Store}
    (h : capturedBySpec fork cfg contract σ_stele σ₀ g A I
      (.error e) immutables) :
    e = .InvalidInstruction ∨ e = .StaticModeViolation := by
  rcases h with ⟨_, _, _, hequiv⟩
  cases hequiv with
  | success h1 _ _ _ => exact absurd h1 (by simp)
  | revert h1 _ => exact absurd h1 (by simp)
  | noMatch h1 _ => exact absurd h1 (by simp)
  | decodingFailed h1 _ => exact absurd h1 (by simp)
  | invalidHalt h1 _ => exact Or.inl (Except.error.inj h1)
  | staticHalt h1 _ => exact Or.inr (Except.error.inj h1)

/-- A static-mode violation is captured only through a Stele run ending in `.staticViolation`. -/
theorem capturedBySpec_static {cfg : Config} {contract : ContractDecl}
    {σ_stele σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256} {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} {immutables : Store}
    (h : capturedBySpec fork cfg contract σ_stele σ₀ g A I (.error .StaticModeViolation) immutables) :
    ∃ returnConvention,
      steleExec fork cfg contract immutables σ_stele σ₀ g A I .staticViolation returnConvention := by
  rcases h with ⟨steleRes, rc, hstele, hequiv⟩
  cases hequiv with
  | success h1 _ _ _ => exact absurd h1 (by simp)
  | revert h1 _ => exact absurd h1 (by simp)
  | noMatch h1 _ => exact absurd h1 (by simp)
  | decodingFailed h1 _ => exact absurd h1 (by simp)
  | invalidHalt h1 _ => exact absurd (Except.error.inj h1) (by simp)
  | staticHalt _ h2 => exact ⟨rc, h2 ▸ hstele⟩

/-- **No crash.**  A refined bytecode never halts with an exception other than out-of-gas,
    `INVALID`, or a static-mode violation on an admissible input: no stack under- or overflow,
    invalid jump, or invalid opcode is reachable.  A static-mode violation in turn requires a Stele
    run ending in `.staticViolation` (`capturedBySpec_static`), which only a state-changing
    statement produces.  This holds under every fork the refinement is stated for. -/
theorem runtimeRefinement_no_crash {forks : ForkSet} {cfg : Config} {bytecode : ByteArray}
    {contract : ContractDecl} {immutables : Store}
    (h : runtimeRefinementOn forks cfg bytecode contract immutables)
    (fork : Ethereum.Fork) (hfork : forks fork) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    {e : Ethereum.EVM.ExecutionException}
    (herr : Ethereum.EVM.Ξ fork σ σ₀ g A I = .error e) :
    e = .OutOfGass ∨ e = .InvalidInstruction ∨ e = .StaticModeViolation := by
  rcases runtimeRefinement_behaviors_included h
      fork hfork σ σ₀ g A I hcode hsize with hoog | hcap
  · left; rw [herr] at hoog; exact Except.error.inj hoog
  · right; rw [herr] at hcap; exact capturedBySpec_error hcap

end Stele
