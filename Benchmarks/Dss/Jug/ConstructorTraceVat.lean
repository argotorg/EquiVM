import Benchmarks.Dss.Jug.ConstructorTraceVatMask

/-!
# MakerDAO/Sky DSS Jug constructor vat storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

theorem jugCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd73 :
      RD (jugCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨73⟩
        [EVM.word vat.val] (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (jugCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨106⟩
      [] (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σWards ⟨2⟩ (jugCtorVatStored σWards I vat)) k' C' := by
  obtain ⟨_, _, rd105⟩ := jugCtorVatBeforeStoreReach vat rd73
  obtain ⟨k', C', rd106⟩ := rd105.sstore hperm (by jug_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨105⟩ : UInt256) + ⟨1⟩ = ⟨106⟩ from by native_decide] using rd106⟩

end Benchmarks.Dss.Jug
