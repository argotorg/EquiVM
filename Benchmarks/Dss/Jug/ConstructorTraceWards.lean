import Benchmarks.Dss.Jug.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Jug constructor wards storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem jugCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd54 :
      RD (jugCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
        [EVM.word vat.val] (jugCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (jugCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨73⟩
      [EVM.word vat.val] (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (jugCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := jug_ctor_run rd54 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (jugCtorArgFreeMem vat))
      (UInt256.ofNat 5) (by jug_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (jugCtorWardsHashMem I vat)
      (UInt256.ofNat 5) (by jug_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1]
  have rdSlot := rdBeforeHash.keccak256 0 (jugCtorCallerWardsSlot I) (UInt256.ofNat 5)
    (by jug_ctor_decode) mem_cost (jugCtorWardsHashSlot I vat) (by decide) (by evm_ov)
  have rdBeforeStore := jug_ctor_run rdSlot with [push1 ⟨1⟩, swap1]
  obtain ⟨k', C', rd73⟩ := rdBeforeStore.sstore hperm (by jug_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd73⟩

end Benchmarks.Dss.Jug
