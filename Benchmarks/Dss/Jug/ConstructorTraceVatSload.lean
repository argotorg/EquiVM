import Benchmarks.Dss.Jug.ConstructorBase

/-!
# MakerDAO/Sky DSS Jug constructor vat slot load trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

theorem jugCtorVatSloadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd73 :
      RD (jugCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨73⟩
        [EVM.word vat.val] (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (jugCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨77⟩
      [solcSlotWord σWards I ⟨2⟩, ⟨2⟩, EVM.word vat.val]
      (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdBeforeSload := jug_ctor_run rd73 with [push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd77⟩ := rdBeforeSload.sload (by jug_ctor_decode) (by evm_ov)
  have hload :
      (σWards.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        solcSlotWord σWards I ⟨2⟩ := by
    rfl
  rw [hload] at rd77
  have hpc77 : (⟨73⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨77⟩ := by
    native_decide
  rw [hpc77] at rd77
  exact ⟨_, _, rd77⟩

end Benchmarks.Dss.Jug
