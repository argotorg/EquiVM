import Benchmarks.Dss.Spot.ConstructorTraceVatMask

/-!
# MakerDAO/Sky DSS Spotter constructor vat storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd75 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨109⟩
      [⟨1⟩] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σWards ⟨2⟩ (spotCtorVatStored σWards I vat)) k' C' := by
  obtain ⟨_, _, rd108⟩ := spotCtorVatBeforeStoreReach vat rd75
  obtain ⟨k', C', rd109⟩ := rd108.sstore hperm (by spot_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨108⟩ : UInt256) + ⟨1⟩ = ⟨109⟩ from by native_decide] using rd109⟩

end Benchmarks.Dss.Spot
