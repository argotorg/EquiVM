import Benchmarks.Dss.Cat.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Cat constructor wards storage trace

Cat's `wards[caller] = 1` store keeps a stray `1` on the stack (`… PUSH1 1; SWAP1; DUP2; SWAP1;
SSTORE`); the optimizer reuses that `1` as the `live = 1` value later.  So the reached stack after
the wards store is `[⟨1⟩, vat_]`.  Byte-for-byte identical to the Pot constructor's wards store.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem catCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd54 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
        [EVM.word vat.val] (catCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
      [⟨1⟩, EVM.word vat.val] (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (catCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := cat_ctor_run rd54 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (catCtorArgFreeMem vat))
      (UInt256.ofNat 5) (by cat_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (catCtorWardsHashMem I vat)
      (UInt256.ofNat 5) (by cat_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1]
  have rdSlot := rdBeforeHash.keccak256 0 (catCtorCallerWardsSlot I) (UInt256.ofNat 5)
    (by cat_ctor_decode) mem_cost (catCtorWardsHashSlot I vat) (by decide) (by evm_ov)
  have rdBeforeStore := cat_ctor_run rdSlot with [push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd75⟩ := rdBeforeStore.sstore hperm (by cat_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd75⟩

end Benchmarks.Dss.Cat
