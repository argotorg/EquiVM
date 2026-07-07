import Benchmarks.Dss.Spot.ConstructorTraceVatMaskHigh

/-!
# MakerDAO/Sky DSS Spotter constructor vat mask trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorVatMaskJoinReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd102 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
        [UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask), ⟨2⟩,
          ⟨1⟩, UInt256.land (EVM.word vat.val) solcAddrMask]
        (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨2⟩, spotCtorVatStored σWards I vat, ⟨1⟩]
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd108 := spot_ctor_run rd102 with [
    swap3, swap1, swap3, lor, swap1, swap2]
  have hpc108 :
      (⟨102⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨108⟩ := by
    native_decide
  rw [hpc108] at rd108
  exact ⟨_, _, by
    simpa [spotCtorVatStored, setAddressOffset0Word] using rd108⟩

theorem spotCtorVatBeforeStoreReach
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
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨2⟩, spotCtorVatStored σWards I vat, ⟨1⟩]
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  obtain ⟨_, _, rd79⟩ := spotCtorVatSloadReach vat rd75
  obtain ⟨_, _, rd90⟩ := spotCtorVatMaskLowReach vat rd79
  obtain ⟨_, _, rd102⟩ := spotCtorVatMaskHighReach vat rd90
  exact spotCtorVatMaskJoinReach vat rd102

end Benchmarks.Dss.Spot
