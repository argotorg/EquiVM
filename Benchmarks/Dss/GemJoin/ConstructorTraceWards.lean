import Benchmarks.Dss.GemJoin.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS GemJoin constructor wards storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem gemJoinCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd68 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨68⟩
        [solcSourceWord I, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨85⟩
      [⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (gemJoinCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := gem_ctor_run rd68 with [
    push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (gemJoinCtorArgFreeMem vat ilk gem))
      (UInt256.ofNat 7) (by gem_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup1, dup5,
    raw mstore 0 (gemJoinCtorWardsHashMem I vat ilk gem)
      (UInt256.ofNat 7) (by gem_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    dup6, swap1]
  have rdSlot := rdBeforeHash.keccak256 0 (gemJoinCtorCallerWardsSlot I) (UInt256.ofNat 7)
    (by gem_ctor_decode) mem_cost (gemJoinCtorWardsHashSlot I vat ilk gem)
    (by decide) (by evm_ov)
  have rdBeforeStore := gem_ctor_run rdSlot with [push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd85⟩ := rdBeforeStore.sstore hperm (by gem_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd85⟩

end Benchmarks.Dss.GemJoin
