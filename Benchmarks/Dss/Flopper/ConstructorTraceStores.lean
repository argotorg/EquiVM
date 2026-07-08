import Benchmarks.Dss.Flopper.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Flopper constructor storage traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem flopperCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σDefaults σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd134 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨134⟩
        [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
        (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σDefaults) k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨155⟩
      [⟨1⟩, EVM.word vat.val, EVM.word gem.val]
      (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σDefaults (flopperCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  have rdBeforeHash := flopper_ctor_run rd134 with [
    caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (flopperCtorArgsMem vat gem))
      (UInt256.ofNat 6) (by flopper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    swap3, dup4, swap1,
    raw mstore 0 (flopperCtorWardsHashMem I vat gem)
      (UInt256.ofNat 6) (by flopper_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap3]
  have rdSlot := rdBeforeHash.keccak256 0 (flopperCtorCallerWardsSlot I)
    (UInt256.ofNat 6) (by flopper_ctor_decode) mem_cost
    (flopperCtorWardsHashSlot I vat gem) (by decide) (by evm_ov)
  have rdBeforeStore := flopper_ctor_run rdSlot with [
    push1 ⟨1⟩, swap1, dup2, swap1]
  obtain ⟨k', C', rd155⟩ := rdBeforeStore.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨154⟩ : UInt256) + ⟨1⟩ = ⟨155⟩ from by native_decide] using rd155⟩

set_option maxHeartbeats 1000000 in
theorem flopperCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd155 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨155⟩
        [⟨1⟩, EVM.word vat.val, EVM.word gem.val]
        (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨186⟩
      [UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask, EVM.word gem.val]
      (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σWards ⟨2⟩
        (flopperCtorVatStored σWards I vat)) k' C' := by
  have rdBeforeSload := flopper_ctor_run rd155 with [push1 ⟨2⟩, dup1]
  obtain ⟨k159, C159, rd159raw⟩ := rdBeforeSload.sload (by flopper_ctor_decode) (by evm_ov)
  have rd159 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨159⟩
        [solcSlotWord σWards I ⟨2⟩, ⟨2⟩, ⟨1⟩, EVM.word vat.val, EVM.word gem.val]
        (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k159 C159 := by
    have hload :
        (σWards.find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
          solcSlotWord σWards I ⟨2⟩ := by
      rfl
    simpa [hload] using rd159raw
  have rd185 := flopper_ctor_run rd159 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap4, dup5, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap2, dup3, and,
    lor, swap1, swap2]
  obtain ⟨k', C', rd186raw⟩ := rd185.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  have holdComm :
      UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨2⟩) =
        UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask) := by
    exact u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨2⟩)
  have hvatComm :
      UInt256.land solcAddrMask (EVM.word vat.val) =
        UInt256.land (EVM.word vat.val) solcAddrMask := by
    exact u256_land_comm solcAddrMask (EVM.word vat.val)
  exact ⟨k', C', by
    simpa [flopperCtorVatStored, setAddressOffset0Word,
      holdComm, hvatComm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
      show (⟨185⟩ : UInt256) + ⟨1⟩ = ⟨186⟩ from by native_decide] using rd186raw⟩

set_option maxHeartbeats 1000000 in
theorem flopperCtorGemStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd186 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨186⟩
        [UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask, EVM.word gem.val]
        (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨203⟩
      [⟨1⟩]
      (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σVat ⟨3⟩ (flopperCtorGemStored σVat I gem)) k' C' := by
  have rdBeforeSload := flopper_ctor_run rd186 with [push1 ⟨3⟩, dup1]
  obtain ⟨k190, C190, rd190raw⟩ := rdBeforeSload.sload (by flopper_ctor_decode) (by evm_ov)
  have rd190 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨190⟩
        [solcSlotWord σVat I ⟨3⟩, ⟨3⟩, UInt256.lnot solcAddrMask, ⟨1⟩, solcAddrMask,
          EVM.word gem.val]
        (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σVat) k190 C190 := by
    have hload :
        (σVat.find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
          solcSlotWord σVat I ⟨3⟩ := by
      rfl
    simpa [hload] using rd190raw
  have rd202 := flopper_ctor_run rd190 with [
    swap4, swap1, swap5, and, swap3, and, swap2, swap1, swap2, lor, swap1, swap2]
  obtain ⟨k', C', rd203raw⟩ := rd202.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [flopperCtorGemStored, setAddressOffset0Word,
      show (⟨202⟩ : UInt256) + ⟨1⟩ = ⟨203⟩ from by native_decide] using rd203raw⟩

theorem flopperCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σGem σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd203 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨203⟩
        [⟨1⟩]
        (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σGem) k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨206⟩
      []
      (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σGem ⟨8⟩ ⟨1⟩) k' C' := by
  have rd205 := flopper_ctor_run rd203 with [push1 ⟨8⟩]
  obtain ⟨k', C', rd206⟩ := rd205.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨205⟩ : UInt256) + ⟨1⟩ = ⟨206⟩ from by native_decide] using rd206⟩

theorem flopperCtorStoresReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σDefaults σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd134 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨134⟩
        [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
        (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σDefaults) k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨206⟩
      [] (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, flopperCtorFinalMap σDefaults I vat gem) k' C' := by
  obtain ⟨_, _, rd155⟩ := flopperCtorWardsStoreReach vat gem hperm rd134
  obtain ⟨_, _, rd186⟩ := flopperCtorVatStoreReach vat gem hperm rd155
  obtain ⟨_, _, rd203⟩ := flopperCtorGemStoreReach vat gem hperm rd186
  simpa [flopperCtorFinalMap, flopperCtorAfterGemMap, flopperCtorAfterVatMap,
    flopperCtorAfterWardsMap] using flopperCtorLiveStoreReach vat gem hperm rd203

end Benchmarks.Dss.Flopper
