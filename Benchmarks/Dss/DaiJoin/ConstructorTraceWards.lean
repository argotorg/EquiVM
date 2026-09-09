import Benchmarks.Dss.DaiJoin.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS DaiJoin constructor wards storage trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem daiJoinCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress) {k C : Nat}
    (hperm : I.perm = true)
    (rd61 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨61⟩
        [EVM.word dai.val, EVM.word vat.val, ⟨32⟩]
        (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨82⟩
      [⟨1⟩, EVM.word vat.val, EVM.word dai.val]
      (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := daiJoin_ctor_run rd61 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (daiJoinCtorArgFreeMem vat dai))
      (UInt256.ofNat 6) (by daiJoin_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    swap3, dup4, swap1,
    raw mstore 0 (daiJoinCtorWardsHashMem I vat dai)
      (UInt256.ofNat 6) (by daiJoin_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap3]
  have rdSlot := rdBeforeHash.keccak256 0 (daiJoinCtorCallerWardsSlot I) (UInt256.ofNat 6)
    (by daiJoin_ctor_decode) mem_cost (daiJoinCtorWardsHashSlot I vat dai)
    (by decide) (by evm_ov)
  have rdBeforeStore := daiJoin_ctor_run rdSlot with [push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd82⟩ := rdBeforeStore.sstore hperm (by daiJoin_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨81⟩ : UInt256) + ⟨1⟩ = ⟨82⟩ from by decide +native] using rd82⟩

end Benchmarks.Dss.DaiJoin
