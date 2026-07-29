import Benchmarks.Dss.Jug.ConstructorTraceVatMaskHigh

/-!
# MakerDAO/Sky DSS Jug constructor vat mask trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

theorem jugCtorVatMaskJoinReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd100 :
      RD (jugCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨100⟩
        [UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask), ⟨2⟩,
          UInt256.land (EVM.word vat.val) solcAddrMask]
        (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (jugCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨105⟩
      [⟨2⟩, jugCtorVatStored σWards I vat]
      (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd105 := jug_ctor_run rd100 with [
    swap2, swap1, swap2, or, swap1]
  have hpc105 :
      (⟨100⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨105⟩ := by
    native_decide
  rw [hpc105] at rd105
  exact ⟨_, _, by
    simpa [jugCtorVatStored, setAddressOffset0Word] using rd105⟩

theorem jugCtorVatBeforeStoreReach
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
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨105⟩
      [⟨2⟩, jugCtorVatStored σWards I vat]
      (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  obtain ⟨_, _, rd77⟩ := jugCtorVatSloadReach vat rd73
  obtain ⟨_, _, rd88⟩ := jugCtorVatMaskLowReach vat rd77
  obtain ⟨_, _, rd100⟩ := jugCtorVatMaskHighReach vat rd88
  exact jugCtorVatMaskJoinReach vat rd100

end Benchmarks.Dss.Jug
