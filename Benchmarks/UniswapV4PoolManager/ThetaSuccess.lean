import Benchmarks.UniswapV4PoolManager.MemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem toExecute_nonprecompile_code {σ : AccountMap} {target : AccountAddress} (hn : target ∉ π) :
    ∃ code, toExecute σ target = .Code code := by
  unfold toExecute
  rw [if_neg hn]
  simp only [Id.run]
  split <;> exact ⟨_, rfl⟩

-- LIBRARY CANDIDATE: a successful code message call exposes a successful fresh EVM execution.
theorem thetaCode_success_Xi
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {code d : ByteArray} {g p v v' : UInt256} {e : Fin 1025} {H : BlockHeader}
    {blob : List ByteArray} {blocks : ProcessedBlocks} {perm : Bool}
    {σ' : AccountMap} {g' : UInt256} {A' : Substate} {out : ByteArray}
    (h : Ethereum.EVM.Θ σ σ₀ A s o r (.Code code) g p v v' d e H blob blocks perm =
      (σ', g', A', true, out)) :
    ∃ (inputAccounts : AccountMap) (I : ExecutionEnv) (accounts : AccountMap) (substate : Substate),
      Ξ inputAccounts σ₀ g A I = .ok (.success (accounts, g', substate) out) := by
  let σ'₁ := match σ.get? r with
    | none => if v != UInt256.ofNat 0 then σ.insert r {(default : Account) with balance := v} else σ
    | some acc => σ.insert r {acc with balance := acc.balance+v}
  let σ₁ := match σ'₁.get? s with
    | none => σ'₁
    | some acc => σ'₁.insert s {acc with balance := acc.balance-v}
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
      source := s, weiValue := v', depth := e, perm := perm, code := code,
      header := H, blobVersionedHashes := blob, blocks := blocks }
  unfold Ethereum.EVM.Θ at h
  change (let answer : AccountMap × UInt256 × Substate × ByteArray :=
      match Ξ σ₁ σ₀ g A I with
      | .error _ => (∅, ⟨0⟩, A, .empty)
      | .ok (.revert gas data) => (∅, gas, A, data)
      | .ok (.success (acc, gas, sub) data) => (acc, gas, sub, data)
    (if answer.1 == ∅ then σ else answer.1, answer.2.1,
      if answer.1 == ∅ then A else answer.2.2.1,
      if answer.1 == ∅ then false else true, answer.2.2.2)) = (σ', g', A', true, out) at h
  generalize hxi : Ξ σ₁ σ₀ g A I = res at h
  cases res with
  | error err => simp at h
  | ok result =>
    cases result with
    | revert gas data => simp at h
    | success result data =>
      obtain ⟨acc, gas, sub⟩ := result
      simp only at h
      have hg : gas = g' := congrArg (fun x => x.2.1) h
      have ho : data = out := congrArg (fun x => x.2.2.2.2) h
      exact ⟨σ₁, I, acc, sub, by simpa only [hg, ho] using hxi⟩

end Benchmarks.UniswapV4PoolManager
