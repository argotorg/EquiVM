import Benchmarks.Dss.Flapper.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Flapper constructor storage traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem flapperCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σDefaults σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd122 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨122⟩
        [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
        (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σDefaults) k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨143⟩
      [⟨1⟩, EVM.word vat.val, EVM.word gem.val]
      (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σDefaults (flapperCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := flapper_ctor_run rd122 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (flapperCtorArgsMem vat gem))
      (UInt256.ofNat 6) (by flapper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    swap3, dup4, swap1,
    raw mstore 0 (flapperCtorWardsHashMem I vat gem)
      (UInt256.ofNat 6) (by flapper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap3]
  have rdSlot := rdBeforeHash.keccak256 0 (flapperCtorCallerWardsSlot I)
    (UInt256.ofNat 6) (by flapper_ctor_decode) mem_cost
    (flapperCtorWardsHashSlot I vat gem) (by decide) (by evm_ov)
  have rdBeforeStore := flapper_ctor_run rdSlot with [
    push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd143⟩ := rdBeforeStore.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨142⟩ : UInt256) + ⟨1⟩ = ⟨143⟩ from by decide +native] using rd143⟩

set_option maxHeartbeats 1000000 in
theorem flapperCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd143 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨143⟩
        [⟨1⟩, EVM.word vat.val, EVM.word gem.val]
        (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨174⟩
      [UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask, EVM.word gem.val]
      (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σWards ⟨2⟩
        (flapperCtorVatStored σWards I vat)) k' C' := by
  have rdBeforeSload := flapper_ctor_run rd143 with [push1 ⟨2⟩, dup1]
  obtain ⟨k147, C147, rd147raw⟩ := rdBeforeSload.sload (by flapper_ctor_decode) (by evm_ov)
  have rd147 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨147⟩
        [solcSlotWord σWards I ⟨2⟩, ⟨2⟩, ⟨1⟩, EVM.word vat.val, EVM.word gem.val]
        (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k147 C147 := by
    have hload :
        (σWards.find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
          solcSlotWord σWards I ⟨2⟩ := by
      rfl
    simpa [hload] using rd147raw
  have rd173 := flapper_ctor_run rd147 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap4, dup5, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap2, dup3, and,
    or, swap1, swap2]
  obtain ⟨k', C', rd174raw⟩ := rd173.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  have holdComm :
      UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨2⟩) =
        UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask) := by
    exact u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨2⟩)
  have hvatComm :
      UInt256.land solcAddrMask (EVM.word vat.val) =
        UInt256.land (EVM.word vat.val) solcAddrMask := by
    exact u256_land_comm solcAddrMask (EVM.word vat.val)
  exact ⟨k', C', by
    simpa [flapperCtorVatStored, setAddressOffset0Word,
      holdComm, hvatComm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨173⟩ : UInt256) + ⟨1⟩ = ⟨174⟩ from by decide +native] using rd174raw⟩

set_option maxHeartbeats 1000000 in
theorem flapperCtorGemStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd174 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨174⟩
        [UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask, EVM.word gem.val]
        (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨191⟩
      [⟨1⟩]
      (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σVat ⟨3⟩ (flapperCtorGemStored σVat I gem)) k' C' := by
  have rdBeforeSload := flapper_ctor_run rd174 with [push1 ⟨3⟩, dup1]
  obtain ⟨k178, C178, rd178raw⟩ := rdBeforeSload.sload (by flapper_ctor_decode) (by evm_ov)
  have rd178 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨178⟩
        [solcSlotWord σVat I ⟨3⟩, ⟨3⟩, UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask,
          EVM.word gem.val]
        (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σVat) k178 C178 := by
    have hload :
        (σVat.find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
          solcSlotWord σVat I ⟨3⟩ := by
      rfl
    simpa [hload] using rd178raw
  have rd190 := flapper_ctor_run rd178 with [
    swap4, swap1, swap5, and, swap3, and, swap2, swap1, swap2, or, swap1, swap2]
  obtain ⟨k', C', rd191raw⟩ := rd190.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [flapperCtorGemStored, setAddressOffset0Word,
      show (⟨190⟩ : UInt256) + ⟨1⟩ = ⟨191⟩ from by decide +native] using rd191raw⟩

theorem flapperCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σGem σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd191 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨191⟩
        [⟨1⟩]
        (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σGem) k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨194⟩
      []
      (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σGem ⟨7⟩ ⟨1⟩) k' C' := by
  have rd193 := flapper_ctor_run rd191 with [push1 ⟨7⟩]
  obtain ⟨k', C', rd194⟩ := rd193.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨193⟩ : UInt256) + ⟨1⟩ = ⟨194⟩ from by decide +native] using rd194⟩

theorem flapperCtorStoresReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σDefaults σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd122 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨122⟩
        [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
        (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σDefaults) k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨194⟩
      [] (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, flapperCtorFinalMap σDefaults I vat gem) k' C' := by
  obtain ⟨_, _, rd143⟩ := flapperCtorWardsStoreReach vat gem hperm rd122
  obtain ⟨_, _, rd174⟩ := flapperCtorVatStoreReach vat gem hperm rd143
  obtain ⟨_, _, rd191⟩ := flapperCtorGemStoreReach vat gem hperm rd174
  simpa [flapperCtorFinalMap, flapperCtorAfterGemMap, flapperCtorAfterVatMap,
    flapperCtorAfterWardsMap] using flapperCtorLiveStoreReach vat gem hperm rd191

end Benchmarks.Dss.Flapper
