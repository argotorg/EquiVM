import Benchmarks.Dss.DaiJoin.ConstructorTraceWards

/-!
# MakerDAO/Sky DSS DaiJoin constructor live/vat/dai storage traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

theorem daiJoinCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress) {k C : Nat}
    (hperm : I.perm = true)
    (rd82 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨82⟩
        [⟨1⟩, EVM.word vat.val, EVM.word dai.val]
        (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨87⟩
      [⟨1⟩, EVM.word vat.val, EVM.word dai.val]
      (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩) k' C' := by
  have rdBeforeStore := daiJoin_ctor_run rd82 with [push1 ⟨3⟩, dup2, swap1]
  obtain ⟨k', C', rd87⟩ := rdBeforeStore.sstore hperm (by daiJoin_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨86⟩ : UInt256) + ⟨1⟩ = ⟨87⟩ from by native_decide] using rd87⟩

theorem daiJoinCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress) {k C : Nat}
    (hperm : I.perm = true)
    (rd87 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨87⟩
        [⟨1⟩, EVM.word vat.val, EVM.word dai.val]
        (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σLive) k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨116⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word dai.val]
      (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σLive ⟨1⟩ (daiJoinCtorVatStored σLive I vat))
      k' C' := by
  let oldVat := (σLive.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩))
  obtain ⟨_, _, rd89⟩ := (daiJoin_ctor_run rd87 with [dup1]).sload
    (by daiJoin_ctor_decode) (by evm_ov)
  have rdBeforeStore := daiJoin_ctor_run rd89 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, raw not (by daiJoin_ctor_decode) (by evm_ov),
    swap2, dup3, and, raw or (by daiJoin_ctor_decode) (by evm_ov), swap1, swap2]
  obtain ⟨k', C', rd116⟩ := rdBeforeStore.sstore hperm (by daiJoin_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [oldVat, daiJoinCtorVatStored, setAddressOffset0Word, solcSlotWord, solcAddrMask,
      u256_land_comm,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) (⟨160⟩ : UInt256) - ⟨1⟩ = solcAddrMask
        from by native_decide,
      show (⟨87⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨116⟩ from by native_decide] using rd116⟩

theorem daiJoinCtorDaiStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress) {k C : Nat}
    (hperm : I.perm = true)
    (rd116 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨116⟩
        [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word dai.val]
        (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨129⟩
      [] (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σVat ⟨2⟩ (daiJoinCtorDaiStored σVat I dai))
      k' C' := by
  let oldDai := (σVat.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩))
  obtain ⟨_, _, rd120⟩ := (daiJoin_ctor_run rd116 with [push1 ⟨2⟩, dup1]).sload
    (by daiJoin_ctor_decode) (by evm_ov)
  have rdBeforeStore := daiJoin_ctor_run rd120 with [
    swap3, swap1, swap4, and, swap2, and, raw or (by daiJoin_ctor_decode) (by evm_ov),
    swap1]
  obtain ⟨k', C', rd129⟩ := rdBeforeStore.sstore hperm (by daiJoin_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [oldDai, daiJoinCtorDaiStored, setAddressOffset0Word, solcSlotWord,
      u256_land_comm,
      show (⟨116⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨129⟩ from by native_decide]
      using rd129⟩

theorem daiJoinCtorStoresReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress) {k C : Nat}
    (hperm : I.perm = true)
    (rd82 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨82⟩
        [⟨1⟩, EVM.word vat.val, EVM.word dai.val]
        (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨129⟩
      [] (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩)
            ⟨1⟩ (daiJoinCtorVatStored (sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩) I vat))
          ⟨2⟩
          (daiJoinCtorDaiStored
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩)
              ⟨1⟩ (daiJoinCtorVatStored (sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩) I vat))
            I dai)) k' C' := by
  obtain ⟨_, _, rd87⟩ := daiJoinCtorLiveStoreReach vat dai hperm rd82
  obtain ⟨_, _, rd116⟩ := daiJoinCtorVatStoreReach vat dai hperm rd87
  exact daiJoinCtorDaiStoreReach vat dai hperm rd116

end Benchmarks.Dss.DaiJoin
