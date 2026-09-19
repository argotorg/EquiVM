import Solidity.Equiv

/-!
# Behavioural corollaries of runtime equivalence

Every result the bytecode can produce is either out-of-gas or captured by the spec: a spec
execution (under some oracle) that agrees on accounts, return/revert data and logs, or a
spec-side rejection (no dispatch / undecodable calldata) matched by an empty revert.  In
particular the bytecode never crashes: the only EVM exception it can raise is out-of-gas.
-/

namespace Solidity

/-- The spec rejects the calldata before running any code. -/
def specRejects (cfg : Config) (fc : FlatContract) (I : Ethereum.ExecutionEnv) : Prop :=
  dispatches fc I.calldata = false ∨
  ∃ e fn, selectorDispatch fc I.calldata = some e ∧ fc.fns[e.fn]? = some fn ∧
    payableOrNoValue fn.decl I ∧ decodeArgs cfg fc.types fn.decl I.calldata = none

def capturedBySpec (cfg : Config) (fc : FlatContract)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (r : EVMResult) : Prop :=
  (∃ (o : Oracle) (res : TopResult) (conv : Refinement.ReturnConvention),
      solidityExec cfg o fc createdAccounts genesisBlockHeader blocks σ_spec σ₀ g A I res conv ∧
      execResultsEquiv r res conv) ∨
  (specRejects cfg fc I ∧ ∃ g', r = .ok (.revert g' ByteArray.empty))

theorem runtimeEquivalenceFor_captured {cfg fc cA gh bl σ_evm σ_spec σ₀ g A I}
    (h : runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I) :
    Ethereum.EVM.Ξ cA gh bl σ_evm σ₀ g A I = .error .OutOfGass ∨
      capturedBySpec cfg fc cA gh bl σ_spec σ₀ g A I (Ethereum.EVM.Ξ cA gh bl σ_evm σ₀ g A I) := by
  cases h with
  | execution hΞ hex =>
    obtain ⟨o, hexec, hequiv⟩ := hex
    exact Or.inr (Or.inl ⟨o, _, _, hexec, hΞ ▸ hequiv⟩)
  | noDispatch hd hΞ => exact Or.inr (Or.inr ⟨Or.inl hd, _, hΞ⟩)
  | decodingFailed h1 h2 h3 h4 hΞ => exact Or.inr (Or.inr ⟨Or.inr ⟨_, _, h1, h2, h3, h4⟩, _, hΞ⟩)
  | outOfGas hΞ => exact Or.inl hΞ

/-- Under runtime equivalence, every admissible execution of the bytecode is out-of-gas or
    captured by the spec. -/
theorem runtimeEquivalence_behaviors_included {cfg bytecode fc}
    (h : runtimeEquivalence cfg bytecode fc)
    (cA : Batteries.RBSet Ethereum.AccountAddress compare) (gh : Ethereum.BlockHeader)
    (bl : Ethereum.ProcessedBlocks) (σ_evm σ_spec σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true) (hacc : Refinement.accountMapEquiv σ_evm σ_spec) :
    Ethereum.EVM.Ξ cA gh bl σ_evm σ₀ g A I = .error .OutOfGass ∨
      capturedBySpec cfg fc cA gh bl σ_spec σ₀ g A I (Ethereum.EVM.Ξ cA gh bl σ_evm σ₀ g A I) := by
  cases h with
  | intro hrun => exact runtimeEquivalenceFor_captured (hrun cA gh bl σ_evm σ_spec σ₀ g A I hcode hsize hperm hacc)

/-- The bytecode never crashes: the only exception it can raise is out-of-gas. -/
theorem runtimeEquivalence_no_crash {cfg bytecode fc}
    (h : runtimeEquivalence cfg bytecode fc)
    (cA : Batteries.RBSet Ethereum.AccountAddress compare) (gh : Ethereum.BlockHeader)
    (bl : Ethereum.ProcessedBlocks) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256)
    (A : Ethereum.Substate) (I : Ethereum.ExecutionEnv)
    (hcode : I.code = bytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true) (e : Ethereum.EVM.ExecutionException)
    (hΞ : Ethereum.EVM.Ξ cA gh bl σ σ₀ g A I = .error e) : e = .OutOfGass := by
  rcases h with ⟨hrun⟩
  have hfor := hrun cA gh bl σ σ σ₀ g A I hcode hsize hperm (Refinement.accountMapEquiv.refl σ)
  cases hfor with
  | execution hΞ' hex =>
    obtain ⟨_, _, hequiv⟩ := hex
    cases hequiv with
    | success h1 => rw [hΞ'] at hΞ; rw [h1] at hΞ; cases hΞ
    | revert h1 => rw [hΞ'] at hΞ; rw [h1] at hΞ; cases hΞ
  | noDispatch _ hΞ' => rw [hΞ'] at hΞ; cases hΞ
  | decodingFailed _ _ _ _ hΞ' => rw [hΞ'] at hΞ; cases hΞ
  | outOfGas hΞ' => rw [hΞ'] at hΞ; cases hΞ; rfl

end Solidity
