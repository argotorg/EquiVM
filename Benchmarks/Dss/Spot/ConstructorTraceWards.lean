import Benchmarks.Dss.Spot.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Spotter constructor wards storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem spotCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd54 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
        [EVM.word vat.val] (spotCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
      [⟨1⟩, EVM.word vat.val] (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (spotCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := spot_ctor_run rd54 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (spotCtorArgFreeMem vat))
      (UInt256.ofNat 5) (by spot_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (spotCtorWardsHashMem I vat)
      (UInt256.ofNat 5) (by spot_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1]
  have rdSlot := rdBeforeHash.keccak256 0 (spotCtorCallerWardsSlot I) (UInt256.ofNat 5)
    (by spot_ctor_decode) mem_cost (spotCtorWardsHashSlot I vat) (by decide) (by evm_ov)
  have rdBeforeStore := spot_ctor_run rdSlot with [push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd75⟩ := rdBeforeStore.sstore hperm (by spot_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨74⟩ : UInt256) + ⟨1⟩ = ⟨75⟩ from by decide +native] using rd75⟩

end Benchmarks.Dss.Spot
