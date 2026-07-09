import Benchmarks.Dss.GemJoin.ConstructorTraceWards

/-!
# MakerDAO/Sky DSS GemJoin constructor storage-write traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

theorem gemJoinCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd85 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨85⟩
        [⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨90⟩
      [⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σWards ⟨5⟩ ⟨1⟩) k' C' := by
  have rd89 := gem_ctor_run rd85 with [push1 ⟨5⟩, dup2, swap1]
  obtain ⟨k', C', rd90⟩ := rd89.sstore hperm (by gem_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨89⟩ : UInt256) + ⟨1⟩ = ⟨90⟩ from by native_decide] using rd90⟩

theorem gemJoinCtorVatSloadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (rd90 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨90⟩
        [⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σLive) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨92⟩
      [solcSlotWord σLive I ⟨1⟩, ⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩,
        EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σLive) k' C' := by
  have rd91 := rd90.dup1 (by gem_ctor_decode) (by evm_ov)
  obtain ⟨_, _, rd92⟩ := rd91.sload (by gem_ctor_decode) (by evm_ov)
  have hload :
      (σLive.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩)) =
        solcSlotWord σLive I ⟨1⟩ := by
    rfl
  rw [hload] at rd92
  exact ⟨_, _, by
    simpa [show (⟨90⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨92⟩ from by native_decide] using rd92⟩

theorem gemJoinCtorVatMaskLowReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (rd92 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨92⟩
        [solcSlotWord σLive I ⟨1⟩, ⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σLive) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨103⟩
      [UInt256.land (EVM.word vat.val) solcAddrMask, solcAddrMask,
        solcSlotWord σLive I ⟨1⟩, ⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩,
        EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σLive) k' C' := by
  have rd103 := gem_ctor_run rd92 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup8,
    raw and (by gem_ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide,
        show (⟨92⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨103⟩
          from by native_decide] using rd103⟩

theorem gemJoinCtorVatMaskHighReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (rd103 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨103⟩
        [UInt256.land (EVM.word vat.val) solcAddrMask, solcAddrMask,
          solcSlotWord σLive I ⟨1⟩, ⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σLive) k C) :
      ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨116⟩
        [UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σLive I ⟨1⟩))
          (UInt256.land (EVM.word vat.val) solcAddrMask),
          solcAddrMask, UInt256.lnot solcAddrMask, ⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σLive) k' C' := by
  have rd116 := gem_ctor_run rd103 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap3, dup4,
    raw and (by gem_ctor_decode) (by evm_ov),
    lor]
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
      show (⟨103⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨116⟩
        from by native_decide] using rd116⟩

theorem gemJoinCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd90 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨90⟩
        [⟨1⟩, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σLive) k C) :
      ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨119⟩
        [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts,
        sstoreAccountMap I.codeOwner σLive ⟨1⟩ (gemJoinCtorVatStored σLive I vat)) k' C' := by
    obtain ⟨_, _, rd92⟩ := gemJoinCtorVatSloadReach vat ilk gem rd90
    obtain ⟨_, _, rd103⟩ := gemJoinCtorVatMaskLowReach vat ilk gem rd92
    obtain ⟨_, _, rd116⟩ := gemJoinCtorVatMaskHighReach vat ilk gem rd103
    have rd118 := gem_ctor_run rd116 with [swap1, swap3]
    obtain ⟨k', C', rd119⟩ := rd118.sstore hperm (by gem_ctor_decode) (by evm_ov)
    exact ⟨k', C', by
      simpa [gemJoinCtorVatStored, setAddressOffset0Word, u256_land_comm,
        show (⟨116⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨119⟩ from by native_decide]
        using rd119⟩

theorem gemJoinCtorIlkStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd119 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨119⟩
        [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨124⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
        EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σVat ⟨2⟩ ilk) k' C' := by
  have rd123 := gem_ctor_run rd119 with [push1 ⟨2⟩, dup5, swap1]
  obtain ⟨k', C', rd124⟩ := rd123.sstore hperm (by gem_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨119⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨124⟩
      from by native_decide] using rd124⟩

theorem gemJoinCtorGemStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σIlk σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd124 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨124⟩
        [UInt256.lnot solcAddrMask, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
          EVM.word vat.val, ⟨64⟩]
        (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σIlk) k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨141⟩
      [gemJoinCtorGemStored σIlk I gem, solcAddrMask, EVM.word gem.val, ilk, ⟨32⟩,
        EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorWardsHashMem I vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σIlk ⟨3⟩ (gemJoinCtorGemStored σIlk I gem)) k' C' := by
  have rd127 := gem_ctor_run rd124 with [push1 ⟨3⟩, dup1]
  obtain ⟨_, _, rd128⟩ := rd127.sload (by gem_ctor_decode) (by evm_ov)
  have hload :
      (σIlk.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
        solcSlotWord σIlk I ⟨3⟩ := by
    rfl
  rw [hload] at rd128
  have rd140 := gem_ctor_run rd128 with [
    dup4, dup6, raw and (by gem_ctor_decode) (by evm_ov), swap3,
    raw and (by gem_ctor_decode) (by evm_ov), swap2, swap1, swap2, lor, swap1,
    dup2, swap1]
  obtain ⟨k', C', rd141⟩ := rd140.sstore hperm (by gem_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [gemJoinCtorGemStored, setAddressOffset0Word, u256_land_comm,
      show (⟨124⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨141⟩ from by native_decide]
      using rd141⟩

end Benchmarks.Dss.GemJoin
