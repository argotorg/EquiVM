import Benchmarks.Dss.Flopper.ConstructorBase

/-!
# MakerDAO/Sky DSS Flopper constructor default-store and nonpayable traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

set_option maxHeartbeats 2000000 in
theorem flopperCtorDefaultsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flopperCtorCode vat gem)
    (hperm : I.perm = true) :
    ∃ k C, RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨78⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, flopperCtorAfterKicksMap σ I) k C := by
  have rd0 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd5 := flopper_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by flopper_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd14 := rd5.pushConst flopperCtorBegWord (width := 8) (op := .PUSH8)
    (by decide) (by flopper_ctor_decode) (by evm_ov)
  have rd16 := flopper_ctor_run rd14 with [push1 ⟨4⟩]
  obtain ⟨k17, C17, rd17raw⟩ := rd16.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  have rd17 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨17⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flopperCtorAfterBegMap σ I) k17 C17 := by
    simpa [flopperCtorAfterBegMap] using rd17raw
  have rd26 := rd17.pushConst flopperCtorPadWord (width := 8) (op := .PUSH8)
    (by decide) (by flopper_ctor_decode) (by evm_ov)
  have rd28 := flopper_ctor_run rd26 with [push1 ⟨5⟩]
  obtain ⟨k29, C29, rd29raw⟩ := rd28.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  have rd29 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨29⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flopperCtorAfterPadMap σ I) k29 C29 := by
    simpa [flopperCtorAfterPadMap] using rd29raw
  have rd32pre := flopper_ctor_run rd29 with [push1 ⟨6⟩, dup1]
  obtain ⟨k33, C33, rd33raw⟩ := rd32pre.sload (by flopper_ctor_decode) (by evm_ov)
  have rd33 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨33⟩
        [solcSlotWord (flopperCtorAfterPadMap σ I) I ⟨6⟩, ⟨6⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flopperCtorAfterPadMap σ I) k33 C33 := by
    have hload :
        ((flopperCtorAfterPadMap σ I).find? I.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨6⟩ ⟨0⟩)) =
          solcSlotWord (flopperCtorAfterPadMap σ I) I ⟨6⟩ := by
      rfl
    simpa [hload] using rd33raw
  have rd36 := flopper_ctor_run rd33 with [push2 flopperCtorTtlWord]
  have rd43 := rd36.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) (by flopper_ctor_decode) (by evm_ov)
  have rd48 := flopper_ctor_run rd43 with [not, swap1, swap2, and, lor]
  have rd55 := rd48.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) (by flopper_ctor_decode) (by evm_ov)
  have rd60 := flopper_ctor_run rd55 with [push1 ⟨48⟩, shl, not, and]
  have rd70 := rd60.pushConst (UInt256.shiftLeft flopperCtorTauWord ⟨48⟩)
    (width := 9) (op := .PUSH9) (by decide) (by flopper_ctor_decode) (by evm_ov)
  have rd72 := flopper_ctor_run rd70 with [lor, swap1]
  obtain ⟨k73, C73, rd73raw⟩ := rd72.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  have rd73 :
      RD (flopperCtorCode vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨73⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, flopperCtorAfterPackedDefaultsMap σ I) k73 C73 := by
    simpa [flopperCtorAfterPackedDefaultsMap, flopperCtorDefaultsSlot6Word,
      flopperCtorTtlWord, flopperCtorTauWord] using rd73raw
  have rd77 := flopper_ctor_run rd73 with [push1 ⟨0⟩, push1 ⟨7⟩]
  obtain ⟨k', C', rd78raw⟩ := rd77.sstore hperm (by flopper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [flopperCtorAfterKicksMap] using rd78raw⟩

theorem flopperCtorGuardSuccessReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flopperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨91⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, flopperCtorAfterKicksMap σ I) k C := by
  obtain ⟨_, _, rd78⟩ :=
    flopperCtorDefaultsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm
  have rdBeforeJump := flopper_ctor_run rd78 with [
    callvalue, dup1, iszero, push2 ⟨89⟩]
  have rd89 := rdBeforeJump.jumpiT (by flopper_ctor_decode) (by rw [hwv]; decide)
    (by flopper_ctor_jd) (by evm_ov)
  have rd91 := flopper_ctor_run rd89 with [jumpdest, pop]
  exact ⟨_, _, by
    simpa [show (⟨89⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨91⟩ from by native_decide]
      using rd91⟩

theorem flopperInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flopperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (flopperCtorCode vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd78⟩ :=
    flopperCtorDefaultsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm
  have rd85 := flopper_ctor_run rd78 with [
    callvalue, dup1, iszero, push2 ⟨89⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact flopper_ctor_run rd85 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by flopper_ctor_decode) mem_cost (by evm_ov)]

end Benchmarks.Dss.Flopper
