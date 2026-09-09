import Benchmarks.Dss.Cat.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Cat constructor vat storage trace

`vat = vat_` packs the address into slot 3 via read-mask-OR.  Same shape as the Pot constructor's
slot-5 pack (`PUSH1 slot; DUP1; SLOAD; …mask…; SSTORE`), with the stray `1` from the wards store
sitting at the bottom of the stack.  The store leaves `[⟨1⟩]` on the stack.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

theorem catCtorVatSloadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd75 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
      [solcSlotWord σWards I ⟨3⟩, ⟨3⟩, ⟨1⟩, EVM.word vat.val]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdBeforeSload := cat_ctor_run rd75 with [push1 ⟨3⟩, dup1]
  obtain ⟨_, _, rd79⟩ := rdBeforeSload.sload (by cat_ctor_decode) (by evm_ov)
  have hload :
      (σWards.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
        solcSlotWord σWards I ⟨3⟩ := by
    rfl
  rw [hload] at rd79
  have hpc79 : (⟨75⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨79⟩ := by
    decide +native
  rw [hpc79] at rd79
  exact ⟨_, _, rd79⟩

theorem catCtorVatMaskLowReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd79 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
        [solcSlotWord σWards I ⟨3⟩, ⟨3⟩, ⟨1⟩, EVM.word vat.val]
        (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
      [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨3⟩, ⟨1⟩, solcSlotWord σWards I ⟨3⟩]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd90 := cat_ctor_run rd79 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap4,
    raw and (by cat_ctor_decode) (by evm_ov)]
  have hpc90 :
      (⟨79⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨90⟩ := by
    decide +native
  rw [hpc90] at rd90
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd90⟩

theorem catCtorVatMaskHighReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd90 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
        [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨3⟩, ⟨1⟩, solcSlotWord σWards I ⟨3⟩]
        (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
      [UInt256.land (solcSlotWord σWards I ⟨3⟩) (UInt256.lnot solcAddrMask), ⟨3⟩, ⟨1⟩,
        UInt256.land (EVM.word vat.val) solcAddrMask]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd102 := cat_ctor_run rd90 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, swap4,
    raw and (by cat_ctor_decode) (by evm_ov)]
  have hpc102 :
      (⟨90⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨102⟩ := by
    decide +native
  rw [hpc102] at rd102
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd102⟩

theorem catCtorVatMaskJoinReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd102 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
        [UInt256.land (solcSlotWord σWards I ⟨3⟩) (UInt256.lnot solcAddrMask), ⟨3⟩, ⟨1⟩,
          UInt256.land (EVM.word vat.val) solcAddrMask]
        (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨3⟩, catCtorVatStored σWards I vat, ⟨1⟩]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd108 := cat_ctor_run rd102 with [
    swap3, swap1, swap3, or, swap1, swap2]
  have hpc108 :
      (⟨102⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨108⟩ := by
    decide +native
  rw [hpc108] at rd108
  exact ⟨_, _, by
    simpa [catCtorVatStored, setAddressOffset0Word] using rd108⟩

theorem catCtorVatBeforeStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd75 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨3⟩, catCtorVatStored σWards I vat, ⟨1⟩]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  obtain ⟨_, _, rd79⟩ := catCtorVatSloadReach vat rd75
  obtain ⟨_, _, rd90⟩ := catCtorVatMaskLowReach vat rd79
  obtain ⟨_, _, rd102⟩ := catCtorVatMaskHighReach vat rd90
  exact catCtorVatMaskJoinReach vat rd102

theorem catCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd75 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨109⟩
      [⟨1⟩] (catCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σWards ⟨3⟩ (catCtorVatStored σWards I vat)) k' C' := by
  obtain ⟨_, _, rd108⟩ := catCtorVatBeforeStoreReach vat rd75
  obtain ⟨k', C', rd109⟩ := rd108.sstore hperm (by cat_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨108⟩ : UInt256) + ⟨1⟩ = ⟨109⟩ from by decide +native] using rd109⟩

end Benchmarks.Dss.Cat
