import Benchmarks.Dss.Pot.ConstructorTraceArgs

/-!
# MakerDAO/Sky DSS Pot constructor vat storage trace

`vat = vat_` packs the address into slot 5.  Same shape as Jug's slot-2 pack, but one stack element
deeper (the stray `1` from the wards store sits at the bottom), so the solc SWAP indices are one
higher (`SWAP4`/`SWAP3` where Jug has `SWAP3`/`SWAP2`) and there is one extra `SWAP2` before the
`SSTORE`.  The store leaves `[⟨1⟩]` on the stack.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

theorem potCtorVatSloadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd75 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
      [solcSlotWord σWards I ⟨5⟩, ⟨5⟩, ⟨1⟩, EVM.word vat.val]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdBeforeSload := pot_ctor_run rd75 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd79⟩ := rdBeforeSload.sload (by pot_ctor_decode) (by evm_ov)
  have hload :
      (σWards.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨5⟩ ⟨0⟩)) =
        solcSlotWord σWards I ⟨5⟩ := by
    rfl
  rw [hload] at rd79
  have hpc79 : (⟨75⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨79⟩ := by
    native_decide
  rw [hpc79] at rd79
  exact ⟨_, _, rd79⟩

theorem potCtorVatMaskLowReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd79 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
        [solcSlotWord σWards I ⟨5⟩, ⟨5⟩, ⟨1⟩, EVM.word vat.val]
        (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
      [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨5⟩, ⟨1⟩, solcSlotWord σWards I ⟨5⟩]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd90 := pot_ctor_run rd79 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap4,
    raw and (by pot_ctor_decode) (by evm_ov)]
  have hpc90 :
      (⟨79⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨90⟩ := by
    native_decide
  rw [hpc90] at rd90
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd90⟩

theorem potCtorVatMaskHighReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd90 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
        [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨5⟩, ⟨1⟩, solcSlotWord σWards I ⟨5⟩]
        (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
      [UInt256.land (solcSlotWord σWards I ⟨5⟩) (UInt256.lnot solcAddrMask), ⟨5⟩, ⟨1⟩,
        UInt256.land (EVM.word vat.val) solcAddrMask]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd102 := pot_ctor_run rd90 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, swap4,
    raw and (by pot_ctor_decode) (by evm_ov)]
  have hpc102 :
      (⟨90⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨102⟩ := by
    native_decide
  rw [hpc102] at rd102
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd102⟩

theorem potCtorVatMaskJoinReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd102 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
        [UInt256.land (solcSlotWord σWards I ⟨5⟩) (UInt256.lnot solcAddrMask), ⟨5⟩, ⟨1⟩,
          UInt256.land (EVM.word vat.val) solcAddrMask]
        (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨5⟩, potCtorVatStored σWards I vat, ⟨1⟩]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd108 := pot_ctor_run rd102 with [
    swap3, swap1, swap3, lor, swap1, swap2]
  have hpc108 :
      (⟨102⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨108⟩ := by
    native_decide
  rw [hpc108] at rd108
  exact ⟨_, _, by
    simpa [potCtorVatStored, setAddressOffset0Word] using rd108⟩

theorem potCtorVatBeforeStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd75 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨108⟩
      [⟨5⟩, potCtorVatStored σWards I vat, ⟨1⟩]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  obtain ⟨_, _, rd79⟩ := potCtorVatSloadReach vat rd75
  obtain ⟨_, _, rd90⟩ := potCtorVatMaskLowReach vat rd79
  obtain ⟨_, _, rd102⟩ := potCtorVatMaskHighReach vat rd90
  exact potCtorVatMaskJoinReach vat rd102

theorem potCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd75 :
      RD (potCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨75⟩
        [⟨1⟩, EVM.word vat.val] (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (potCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨109⟩
      [⟨1⟩] (potCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σWards ⟨5⟩ (potCtorVatStored σWards I vat)) k' C' := by
  obtain ⟨_, _, rd108⟩ := potCtorVatBeforeStoreReach vat rd75
  obtain ⟨k', C', rd109⟩ := rd108.sstore hperm (by pot_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [show (⟨108⟩ : UInt256) + ⟨1⟩ = ⟨109⟩ from by native_decide] using rd109⟩

end Benchmarks.Dss.Pot
