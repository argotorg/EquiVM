import Benchmarks.Safe.ViaIR.SetupOwnersPrepare
import Benchmarks.Safe.ViaIR.SetupOwnersLoop
import Benchmarks.Safe.ViaIR.SetupOwnersFinish

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

theorem safeSetupOwnersTrace (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr}
    {a b c handler len dataStart target token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3302⟩
      (a :: b :: c :: p.threshold :: handler :: handler :: len :: dataStart :: target :: target ::
        token :: receiver :: payment :: UInt256.ofNat ptr :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (ho : ∀ j (hj : j < p.owners.length), p.owners[j].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecFuncBody fork config p.frame evm setupOwnersFunction.body .reverted) ∨
    ∃ f' evm' mem' aw' k' C',
      ExecFuncBody fork config p.frame evm setupOwnersFunction.body (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD fork safeBytecode I g s0 (if handler = ⟨0⟩ then ⟨3401⟩ else ⟨3671⟩)
        (handler :: len :: dataStart :: ⟨3409⟩ :: target :: target :: token :: receiver ::
          payment :: ⟨0⟩ :: R) mem' aw' rdata evm'.accountMap k' C' ∧
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
    hperm (by omega)
  refine .inr ⟨{ contract := contract, locals := locals₂ },
    setupOwnersFinishState p evm₂ current₂, twoWordHashMem current₂ ⟨2⟩ mem₂, aw₃, k₃, C₃,
    .execBlockOK (safeSetupOwnersPrefix p evm hz hle hnz
      (.consNormal hloop (safeSetupOwnersFinishSource (fork := fork) (hperm := by simpa only [hee₂] using hperm) evm₂ hl₂ hc₂ (by omega)))), ?_, ?_,
    h₃, ?_, ?_⟩
  · simpa only [setupOwnersFinishState, writeOwnerLink, storageStore_executionEnv] using hee₂
  · simpa only [setupOwnersFinishState, writeOwnerLink, storageStore_σ₀] using hw₂
  · rw [twoWordHashMem_size_of_ge64 _ _ (by have := hm.size; omega), hsize₂]
  · intro off count hlo hin
    rw [twoWordHashRead _ _ _ _ _ (by omega) hlo, hr₂ off count hlo hin]


end Benchmarks.Safe.ViaIR
