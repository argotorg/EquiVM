import Benchmarks.Dss.Dog.ConstructorBase
import Benchmarks.Dss.Dog.Rely

/-!
# MakerDAO/Sky DSS Dog constructor EVM trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

set_option maxRecDepth 2000000

theorem dogInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = dogCtorCode vat)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (dogCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := dog_ctor_run rd0 with [
    push1 ⟨160⟩, push1 ⟨64⟩,
    raw mstore 9 dogCtorFreePtrMem (UInt256.ofNat 3)
      (by dog_ctor_decode) mem_cost
      (by
        unfold dogCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact dog_ctor_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by dog_ctor_decode) mem_cost (by evm_ov)]

theorem RDret.xiResultAcc {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hOOG | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hOOG
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hOOG))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

set_option maxHeartbeats 1000000 in
theorem dogCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = dogCtorCode vat)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (dogCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
      [EVM.word vat.val] (dogCtorArgFreeMem vat) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd0 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have hcopy : (dogCtorCode vat).write 4927 dogCtorFreePtrMem 160 32 =
      dogCtorArgMem vat := by
    exact dogCtorArg_codecopy_mem vat
  have hfree :
      (((UInt256.ofNat (dogCtorCode vat).size).sub ⟨4927⟩ + (⟨160⟩ : UInt256)).toByteArray).write
          0 (dogCtorArgMem vat) 64 32 =
        dogCtorArgFreeMem vat := by
    rw [dogCtorArgLen_eq]
    rfl
  have rd38 := dog_ctor_run rd0 with [
    push1 ⟨160⟩, push1 ⟨64⟩,
    raw mstore 9 dogCtorFreePtrMem (UInt256.ofNat 3) (by dog_ctor_decode)
      mem_cost
      (by
        unfold dogCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩,
    jumpiT (by rw [hwv]; decide) (by dog_ctor_jd),
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 3) (by dog_ctor_decode)
      mem_cost dogCtorFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨4927⟩, codesize, sub, dup1, push2 ⟨4927⟩, dup4,
    raw codecopy 9 (dogCtorArgMem vat) (UInt256.ofNat 6)
      (by dog_ctor_decode)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [dogCtorCode_size]
        decide)
      (by
        rw [show ((UInt256.ofNat (dogCtorCode vat).size).sub (⟨4927⟩ : UInt256)).toNat = 32 by
          rw [dogCtorCode_size]
          decide]
        exact hcopy)
      (by
        rw [dogCtorCode_size]
        decide)
      (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (dogCtorArgFreeMem vat) (UInt256.ofNat 6)
      (by dog_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  have rdBeforeJump := dog_ctor_run rd38 with [
    push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨51⟩]
  have rd51 := rdBeforeJump.jumpiT (by dog_ctor_decode)
    (by rw [dogCtorArgLen_eq]; decide) (by dog_ctor_jd) (by evm_ov)
  have rd54 := dog_ctor_run rd51 with [
    raw jumpdest (by dog_ctor_decode) (by evm_ov),
    pop,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 6)
      (by dog_ctor_decode) mem_cost (dogCtorArgFreeMem_mload160 vat)
      (by decide) (by evm_ov)]
  exact ⟨_, _, rd54⟩

set_option maxHeartbeats 1000000 in
theorem dogCtorVatDecodeReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd54 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
        [EVM.word vat.val] (dogCtorArgFreeMem vat) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (dogCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨72⟩
      [EVM.word vat.val] (dogCtorVatMem vat) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, σ) k' C' := by
  have rd72 := dog_ctor_run rd54 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨96⟩, shl, sub, not,
    push1 ⟨96⟩, dup3, swap1, shl, and, push1 ⟨128⟩,
    raw mstore 0 (dogCtorVatMem vat) (UInt256.ofNat 6)
      (by dog_ctor_decode) mem_cost
      (by
        rw [dogVatPackedHighMask vat]
        unfold dogCtorVatMem Reasoning.Theory.writeWord
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov)]
  exact ⟨_, _, rd72⟩

theorem dogCtorLiveStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd72 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨72⟩
        [EVM.word vat.val] (dogCtorVatMem vat) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (dogCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
      [⟨1⟩, EVM.word vat.val] (dogCtorVatMem vat) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨3⟩ ⟨1⟩) k' C' := by
  have rdBeforeStore := dog_ctor_run rd72 with [
    push1 ⟨1⟩, push1 ⟨3⟩, dup2, swap1]
  obtain ⟨k', C', rd79⟩ := rdBeforeStore.sstore hperm (by dog_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd79⟩

set_option maxHeartbeats 1000000 in
theorem dogCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σLive σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd79 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
        [⟨1⟩, EVM.word vat.val] (dogCtorVatMem vat) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σLive) k C) :
    ∃ k' C', RD (dogCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨99⟩
      [⟨0⟩, solcSourceWord I, ⟨64⟩, EVM.word vat.val]
      (dogCtorWardsHashMem I vat) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σLive (dogCtorCallerWardsSlot I) ⟨1⟩) k' C' := by
  have rdBeforeHash := dog_ctor_run rd79 with [
    caller, push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (dogCtorVatMem vat))
      (UInt256.ofNat 6) (by dog_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 (dogCtorWardsHashMem I vat)
      (UInt256.ofNat 6) (by dog_ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup3]
  have rdSlot := rdBeforeHash.keccak256 0 (dogCtorCallerWardsSlot I) (UInt256.ofNat 6)
    (by dog_ctor_decode) mem_cost (dogCtorWardsHashSlot I vat) (by decide) (by evm_ov)
  have rdBeforeStore := dog_ctor_run rdSlot with [
    swap4, swap1, swap4]
  obtain ⟨k', C', rd99⟩ := rdBeforeStore.sstore hperm (by dog_ctor_decode) (by evm_ov)
  exact ⟨k', C', rd99⟩

set_option maxHeartbeats 1000000 in
theorem dogCtorRelyLogReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd99 :
      RD (dogCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨99⟩
        [⟨0⟩, solcSourceWord I, ⟨64⟩, EVM.word vat.val]
        (dogCtorWardsHashMem I vat) (UInt256.ofNat 6) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (dogCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨139⟩
      [] (dogCtorWardsHashMem I vat) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rdMload := dog_ctor_run rd99 with [
    swap2,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6)
      (by dog_ctor_decode) mem_cost (dogCtorWardsHashMem_mload64 I vat)
      (by decide) (by evm_ov),
    swap1, swap2]
  have rdTopic := rdMload.pushConst dogRelyLogTopic
    (width := 32) (op := .PUSH32) (by decide) (by dog_ctor_decode) (by evm_ov)
  have rdLogStack := dog_ctor_run rdTopic with [
    swap2]
  have rdLog := RD.log2 0 (UInt256.ofNat 6) rdLogStack
    (by dog_ctor_decode) hperm mem_cost (by decide) (by evm_ov)
  have rdPop := rdLog.pop (by dog_ctor_decode) (by evm_ov)
  exact ⟨_, _, rdPop⟩

set_option maxHeartbeats 1000000 in
theorem dogCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (dogCtorCode vat) I g s0 ⟨139⟩ []
      (dogCtorWardsHashMem I vat) (UInt256.ofNat 6) rdata acc k C) :
    RDret (dogCtorCode vat) g s0 acc (dogCtorPatchedRuntime vat) := by
  have hcopy : (dogCtorCode vat).write 182 (dogCtorWardsHashMem I vat) 0 4745 =
      dogBytecode := by
    exact dogCtorRuntime_codecopy_mem I vat
  have rdVatRaw := dog_ctor_run h with [
    push1 ⟨128⟩,
    raw mload 0 (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) (UInt256.ofNat 6)
      (by dog_ctor_decode) mem_cost
      (by
        apply mloadWordValue_of_readWithPadding
        · rw [dogCtorWardsHashMem_size]
          decide
        · decide
        · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
            dogCtorWardsHashMem_read128 I vat)
      (by decide) (by evm_ov),
    push1 ⟨96⟩, shr]
  have rdVat := by
    simpa [dogVatWord_high_shift_decode vat] using rdVatRaw
  have rdBeforeReturn := dog_ctor_run rdVat with [
    push2 ⟨4745⟩, push2 ⟨182⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat 0 4745)) -
        Cₘ (UInt256.ofNat 6))
      dogBytecode (UInt256.ofNat 149)
      (by dog_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    dup1, push2 ⟨1405⟩,
    raw mstore 0 (writeWord dogBytecode 1405 (EVM.word vat.val)) (UInt256.ofNat 149)
      (by dog_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show (⟨1405⟩ : UInt256).toNat = 1405 from by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨2890⟩,
    raw mstore 0
      (writeWord (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
        (EVM.word vat.val)) (UInt256.ofNat 149)
      (by dog_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show (⟨2890⟩ : UInt256).toNat = 2890 from by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨3170⟩,
    raw mstore 0
      (writeWord
        (writeWord (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
          (EVM.word vat.val)) 3170 (EVM.word vat.val)) (UInt256.ofNat 149)
      (by dog_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show (⟨3170⟩ : UInt256).toNat = 3170 from by decide])
      (by decide) (by evm_ov),
    dup1, push2 ⟨3965⟩,
    raw mstore 0 (dogCtorPatchedRuntime vat) (UInt256.ofNat 149)
      (by dog_ctor_decode) mem_cost
      (by
        simp [dogCtorPatchedRuntime, dogRuntimeWrites, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord,
          show (⟨3965⟩ = (⟨3965⟩ : UInt256) : Prop) from rfl,
          show (⟨3965⟩ : UInt256).toNat = 3965 from by decide])
      (by decide) (by evm_ov),
    pop, push2 ⟨4745⟩, push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 (dogCtorPatchedRuntime vat)
    (by dog_ctor_decode) mem_cost (dogCtorPatchedRuntime_read vat) (by evm_ov)

theorem dogInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = dogCtorCode vat)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (dogCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨3⟩ ⟨1⟩)
          (dogCtorCallerWardsSlot I) ⟨1⟩)
      (dogCtorPatchedRuntime vat) := by
  obtain ⟨_, _, rd54⟩ :=
    dogCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat hcode hwv
  obtain ⟨_, _, rd72⟩ := dogCtorVatDecodeReach vat rd54
  obtain ⟨_, _, rd79⟩ := dogCtorLiveStoreReach vat hperm rd72
  obtain ⟨_, _, rd99⟩ := dogCtorWardsStoreReach vat hperm rd79
  obtain ⟨_, _, rd139⟩ := dogCtorRelyLogReach vat hperm rd99
  exact dogCtorReturnTrace (I := I) vat rd139

end Benchmarks.Dss.Dog
