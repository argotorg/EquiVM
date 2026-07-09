import Benchmarks.Dss.Flapper.ConstructorBase

/-!
# MakerDAO/Sky DSS Flapper constructor default-store and nonpayable traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

set_option maxHeartbeats 2000000 in
theorem flapperCtorDefaultsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flapperCtorCode vat gem)
    (hperm : I.perm = true) :
    ∃ k C, RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨66⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, flapperCtorAfterKicksMap σ I) k C := by
  have rd0 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd5 := flapper_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by flapper_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd14 := rd5.pushConst flapperCtorBegWord (width := 8) (op := .PUSH8)
    (by decide) (by flapper_ctor_decode) (by evm_ov)
  have rd16 := flapper_ctor_run rd14 with [push1 ⟨4⟩]
  obtain ⟨k17, C17, rd17raw⟩ := rd16.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  have rd17 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨17⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flapperCtorAfterBegMap σ I) k17 C17 := by
    simpa [flapperCtorAfterBegMap] using rd17raw
  have rd20pre := flapper_ctor_run rd17 with [push1 ⟨5⟩, dup1]
  obtain ⟨k21, C21, rd21raw⟩ := rd20pre.sload (by flapper_ctor_decode) (by evm_ov)
  have rd21 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨21⟩
        [solcSlotWord (flapperCtorAfterBegMap σ I) I ⟨5⟩, ⟨5⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flapperCtorAfterBegMap σ I) k21 C21 := by
    have hload :
        ((flapperCtorAfterBegMap σ I).find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨5⟩ ⟨0⟩)) =
          solcSlotWord (flapperCtorAfterBegMap σ I) I ⟨5⟩ := by
      rfl
    simpa [hload] using rd21raw
  have rd24 := flapper_ctor_run rd21 with [push2 flapperCtorTtlWord]
  have rd31 := rd24.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) (by flapper_ctor_decode) (by evm_ov)
  have rd36 := flapper_ctor_run rd31 with [not, swap1, swap2, and, lor]
  have rd43 := rd36.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) (by flapper_ctor_decode) (by evm_ov)
  have rd48 := flapper_ctor_run rd43 with [push1 ⟨48⟩, shl, not, and]
  have rd58 := rd48.pushConst (UInt256.shiftLeft flapperCtorTauWord ⟨48⟩)
    (width := 9) (op := .PUSH9) (by decide) (by flapper_ctor_decode) (by evm_ov)
  have rd60 := flapper_ctor_run rd58 with [lor, swap1]
  obtain ⟨k61, C61, rd61raw⟩ := rd60.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  have rd61 :
      RD (flapperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨61⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flapperCtorAfterPackedDefaultsMap σ I) k61 C61 := by
    simpa [flapperCtorAfterPackedDefaultsMap, flapperCtorDefaultsSlot5Word,
      flapperCtorTtlWord, flapperCtorTauWord] using rd61raw
  have rd65 := flapper_ctor_run rd61 with [push1 ⟨0⟩, push1 ⟨6⟩]
  obtain ⟨k', C', rd66raw⟩ := rd65.sstore hperm (by flapper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [flapperCtorAfterKicksMap] using rd66raw⟩

theorem flapperCtorGuardSuccessReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flapperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, flapperCtorAfterKicksMap σ I) k C := by
  obtain ⟨_, _, rd66⟩ :=
    flapperCtorDefaultsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm
  have rdBeforeJump := flapper_ctor_run rd66 with [
    callvalue, dup1, iszero, push2 ⟨77⟩]
  have rd77 := rdBeforeJump.jumpiT (by flapper_ctor_decode) (by rw [hwv]; decide)
    (by flapper_ctor_jd) (by evm_ov)
  have rd79 := flapper_ctor_run rd77 with [jumpdest, pop]
  exact ⟨_, _, by
    simpa [show (⟨77⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨79⟩ from by native_decide]
      using rd79⟩

theorem flapperInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flapperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (flapperCtorCode vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd66⟩ :=
    flapperCtorDefaultsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm
  have rd73 := flapper_ctor_run rd66 with [
    callvalue, dup1, iszero, push2 ⟨77⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact flapper_ctor_run rd73 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by flapper_ctor_decode) mem_cost (by evm_ov)]

end Benchmarks.Dss.Flapper
