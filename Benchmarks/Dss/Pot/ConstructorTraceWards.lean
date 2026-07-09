import Benchmarks.Dss.Pot.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Pot constructor wards storage trace

Unlike Jug, Pot's `wards[caller] = 1` store keeps a stray `1` on the stack (`… PUSH1 1; SWAP1;
DUP2; SWAP1; SSTORE`); the optimizer reuses that `1` as the `live = 1` value later.  So the reached
stack after the wards store is `[⟨1⟩, vat_]` rather than Jug's `[vat_]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem potCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd54 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
        [EVM.word vat.val] (potCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
      [⟨1⟩, EVM.word vat.val] (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (potCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := pot_ctor_run rd54 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (potCtorArgFreeMem vat))
      (UInt256.ofNat 5) (by pot_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (potCtorWardsHashMem I vat)
      (UInt256.ofNat 5) (by pot_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1]
  have rdSlot := rdBeforeHash.keccak256 0 (potCtorCallerWardsSlot I) (UInt256.ofNat 5)
    (by pot_ctor_decode) mem_cost (potCtorWardsHashSlot I vat) (by decide) (by evm_ov)
  have rdBeforeStore := pot_ctor_run rdSlot with [push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd75⟩ := rdBeforeStore.sstore hperm (by pot_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd75⟩

end Benchmarks.Dss.Pot
