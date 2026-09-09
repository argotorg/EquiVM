import Benchmarks.Dss.Spot.ConstructorTraceVat

/-!
# MakerDAO/Sky DSS Spotter constructor par/live storage traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorParStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd109 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨109⟩
        [⟨1⟩] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨125⟩
      [⟨1⟩] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σVat ⟨3⟩ spotCtorOneWord) k' C' := by
  have rd122 := rd109.pushConst spotCtorOneWord
    (width := 12) (op := .PUSH12) (by decide) (by spot_ctor_decode) (by evm_ov)
  have rd124 := rd122.push1 ⟨3⟩ (by spot_ctor_decode) (by evm_ov)
  obtain ⟨k', C', rd125⟩ := rd124.sstore hperm (by spot_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨124⟩ : UInt256) + ⟨1⟩ = ⟨125⟩ from by decide +native] using rd125⟩

theorem spotCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σPar σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd125 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨125⟩
        [⟨1⟩] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σPar) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
      [] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σPar ⟨4⟩ ⟨1⟩) k' C' := by
  have rd127 := rd125.push1 ⟨4⟩ (by spot_ctor_decode) (by evm_ov)
  obtain ⟨k', C', rd128⟩ := rd127.sstore hperm (by spot_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨127⟩ : UInt256) + ⟨1⟩ = ⟨128⟩ from by decide +native] using rd128⟩

theorem spotCtorTailStoresReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd109 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨109⟩
        [⟨1⟩] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
      [] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σVat ⟨3⟩ spotCtorOneWord)
          ⟨4⟩ ⟨1⟩) k' C' := by
  obtain ⟨_, _, rd125⟩ := spotCtorParStoreReach vat hperm rd109
  exact spotCtorLiveStoreReach vat hperm rd125

end Benchmarks.Dss.Spot
