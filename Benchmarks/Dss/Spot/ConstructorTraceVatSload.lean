import Benchmarks.Dss.Spot.ConstructorBase

/-!
# MakerDAO/Sky DSS Spotter constructor vat slot load trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorVatSloadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd75 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
      [solcSlotWord σWards I ⟨2⟩, ⟨2⟩, ⟨1⟩, EVM.word vat.val]
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdBeforeSload := spot_ctor_run rd75 with [push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd79⟩ := rdBeforeSload.sload (by spot_ctor_decode) (by evm_ov)
  have hload :
      (σWards.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        solcSlotWord σWards I ⟨2⟩ := by
    rfl
  rw [hload] at rd79
  have hpc79 : (⟨75⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨79⟩ := by
    decide +native
  rw [hpc79] at rd79
  exact ⟨_, _, rd79⟩

end Benchmarks.Dss.Spot
