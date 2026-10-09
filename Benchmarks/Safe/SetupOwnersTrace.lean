import Benchmarks.Safe.SetupOwnersPrepare
import Benchmarks.Safe.SetupOwnersLoop
import Benchmarks.Safe.SetupOwnersFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSetupOwnersTrace (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7975⟩
      (p.threshold :: UInt256.ofNat ptr :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (ho : ∀ j (hj : j < p.owners.length), p.owners[j].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧ ExecFuncBody config p.frame evm setupOwnersFunction.body .reverted) ∨
    ∃ f' evm' mem' aw' k' C',
      ExecFuncBody config p.frame evm setupOwnersFunction.body (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata evm'.accountMap k' C' ∧
      mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) := by
  obtain ⟨hrev, hsource⟩ | ⟨aw₁, k₁, C₁, hz, hle, hnz, h₁⟩ :=
    safeSetupOwnersPrepare p evm h hee hacc hm hb hov
  · exact .inl ⟨hrev, hsource⟩
  rw [← hacc] at h₁
  obtain ⟨hrev, hloop⟩ | ⟨locals₂, evm₂, current₂, mem₂, aw₂, k₂, C₂, hloop, hl₂, hc₂,
      hee₂, hw₂, h₂, hsize₂, hr₂⟩ :=
    safeSetupOwnersLoop p.owners.length p evm h₁ (SetupOwnersLocals.initial p) (Nat.zero_add _)
      hee hm hp hb (by decide) ho hperm hov
  · exact .inl ⟨hrev, .execBlockRevert (safeSetupOwnersPrefix p evm hz hle hnz
      (.consRevert hloop))⟩
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeSetupOwnersFinishTrace p evm₂ h₂ hee₂ rfl hc₂
    hperm (by omega) hret
  refine .inr ⟨{ contract := contract, locals := locals₂ },
    setupOwnersFinishState p evm₂ current₂, twoWordHashMem current₂ ⟨2⟩ mem₂, aw₃, k₃, C₃,
    .execBlockOK (safeSetupOwnersPrefix p evm hz hle hnz
      (.consNormal hloop (safeSetupOwnersFinishSource evm₂ hl₂ hc₂ (by omega)))), ?_, ?_,
    h₃, ?_, ?_⟩
  · simpa only [setupOwnersFinishState, writeOwnerLink, storageStore_executionEnv] using hee₂
  · simpa only [setupOwnersFinishState, writeOwnerLink, storageStore_σ₀] using hw₂
  · rw [twoWordHashMem_size_of_ge64 _ _ (by have := hm.size; omega), hsize₂]
  · intro off count hlo hin
    rw [twoWordHashRead _ _ _ _ _ (by omega) hlo, hr₂ off count hlo hin]

theorem safeInternalSetupOwners {caller : Frame} {evm : EVM.State}
    {owners threshold : Expr} {retVar : Ident} {p : SetupOwnersInput} {result : ExecResult}
    (hc : caller.contract = contract) (him : caller.immutables = ∅)
    (ho : evalExpr? config caller evm owners = .ok (.array (p.owners.map addressArrayValue)))
    (ht : evalExpr? config caller evm threshold = .ok (uint256Value p.threshold))
    (hb : ExecFuncBody config p.frame evm setupOwnersFunction.body result) :
    ExecStmt config caller evm (.internalCall "setupOwners" [owners, threshold] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := setupOwnersFunction) (locals := p.args)
    (argVals := [.array (p.owners.map addressArrayValue), uint256Value p.threshold])
  · simp only [evalExprs?, ho, ht, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc, him] using hb

end Benchmarks.Safe
