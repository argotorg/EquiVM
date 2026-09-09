import Benchmarks.Dss.GemJoin.ConstructorBase

/-!
# MakerDAO/Sky DSS GemJoin constructor argument and guard traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

theorem gemJoinInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hcode : I.code = gemJoinCtorCode vat ilk gem)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (gemJoinCtorCode vat ilk gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (gemJoinCtorCode vat ilk gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := gem_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by gem_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact gem_ctor_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by gem_ctor_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem gemJoinCtorArgCopyTrace
    {I : ExecutionEnv} {g0 : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (h : RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨38⟩
      [(UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩, ⟨128⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) rdata acc k' C' := by
  have hcopy :
      (gemJoinCtorCode vat ilk gem).write 2326 solcFreePtrMem 128 96 =
        gemJoinCtorArgMem vat ilk gem := by
    rfl
  have hfree :
      (((UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩ +
            (⟨128⟩ : UInt256)).toByteArray).write
          0 (gemJoinCtorArgMem vat ilk gem) 64 32 =
        gemJoinCtorArgFreeMem vat ilk gem := by
    rw [gemJoinCtorArgLen_eq]
    rfl
  have rd38 := gem_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by gem_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨2326⟩, codesize, sub, dup1, push2 ⟨2326⟩, dup4,
    raw codecopy
      12
      (gemJoinCtorArgMem vat ilk gem) (UInt256.ofNat 7)
      (by gem_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [gemJoinCtorArgLen_eq]
        decide)
      (by
        rw [gemJoinCtorArgLen_eq]
        exact hcopy)
      (by rw [gemJoinCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7)
      (by gem_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  have rd38' : RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨38⟩
      [(UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩, ⟨128⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + (0 + 3) + 3 + 3 + 2 + 3 + 3 + 3 +
        (12 + (GasConstants.Gverylow + GasConstants.Gcopy *
          ((((UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩).toNat + 31) / 32))) +
        3 + 3 + 3 + 3 + (0 + 3)) := by
    simpa [
      show (⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨38⟩
        from by decide +native] using rd38
  exact ⟨_, _, rd38'⟩

set_option maxHeartbeats 1000000 in
theorem gemJoinCtorArgDecodeTrace
    {I : ExecutionEnv} {g0 : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (h : RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨38⟩
      [(UInt256.ofNat (gemJoinCtorCode vat ilk gem).size).sub ⟨2326⟩, ⟨128⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) rdata acc k C) :
    ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨68⟩
      [solcSourceWord I, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) rdata acc k' C' := by
  have rdBeforeJump := gem_ctor_run h with [
    push1 ⟨96⟩, dup2, lt, iszero, push2 ⟨51⟩]
  have rd51 := rdBeforeJump.jumpiT (by gem_ctor_decode)
    (by rw [gemJoinCtorArgLen_eq]; decide) (by gem_ctor_jd) (by evm_ov)
  have h160 :
      (if ((⟨32⟩ : UInt256) + ⟨128⟩).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size ∨
          ((⟨32⟩ : UInt256) + ⟨128⟩) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding
           (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) 32))) = ilk := by
    simpa [show ((⟨32⟩ : UInt256) + ⟨128⟩) = ⟨160⟩ from by decide +native]
      using gemJoinCtorArgFreeMem_mload160 vat ilk gem
  have h192 :
      (if ((⟨64⟩ : UInt256) + ⟨128⟩).toNat ≥ (gemJoinCtorArgFreeMem vat ilk gem).size ∨
          ((⟨64⟩ : UInt256) + ⟨128⟩) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((gemJoinCtorArgFreeMem vat ilk gem).readWithPadding
           (((⟨64⟩ : UInt256) + ⟨128⟩).toNat) 32))) = EVM.word gem.val := by
    simpa [show ((⟨64⟩ : UInt256) + ⟨128⟩) = ⟨192⟩ from by decide +native]
      using gemJoinCtorArgFreeMem_mload192 vat ilk gem
  have rd68 := gem_ctor_run rd51 with [
    raw jumpdest (by gem_ctor_decode) (by evm_ov),
    pop,
    dup1,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 7)
      (by gem_ctor_decode) mem_cost (gemJoinCtorArgFreeMem_mload128 vat ilk gem)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup1, dup4, add,
    raw mload 0 ilk (UInt256.ofNat 7)
      (by gem_ctor_decode) mem_cost h160 (by decide) (by evm_ov),
    push1 ⟨64⟩, swap4, dup5, add,
    raw mload 0 (EVM.word gem.val) (UInt256.ofNat 7)
      (by gem_ctor_decode) mem_cost h192 (by decide) (by evm_ov),
    caller]
  have rd68' : ∃ k' C', RD (gemJoinCtorCode vat ilk gem) I g0 s0 ⟨68⟩
      [solcSourceWord I, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) rdata acc k' C' := by
    refine ⟨
      k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1,
      C + 3 + 3 + 3 + 3 + 3 + 10 + 1 + 2 + 3 + (0 + 3) + 3 + 3 + 3 + 3 +
        (0 + 3) + 3 + 3 + 3 + 3 + (0 + 3) + 2,
      ?_⟩
    simpa [
      solcSourceWord,
      show (⟨51⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ = ⟨68⟩
        from by decide +native] using rd68
  exact rd68'

theorem gemJoinCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g0 : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hcode : I.code = gemJoinCtorCode vat ilk gem)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (gemJoinCtorCode vat ilk gem) I g0
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨68⟩
      [solcSourceWord I, EVM.word gem.val, ilk, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (gemJoinCtorArgFreeMem vat ilk gem) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd8 :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := gemJoinCtorCode vat ilk gem) hcode
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
  obtain ⟨k18, C18, rd18⟩ :=
    solcGuardCallvalueZero (code := gemJoinCtorCode vat ilk gem) (ctgt := ⟨16⟩) (wC := 2)
      (opC := .PUSH2) rd8 hwv (by decide)
      (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode) (by gem_ctor_decode)
      (by gem_ctor_jd)
  have rd18' :
      RD (gemJoinCtorCode vat ilk gem) I g0
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g0 A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by decide +native]
      using rd18
  obtain ⟨_, _, rd38⟩ := gemJoinCtorArgCopyTrace vat ilk gem rd18'
  exact gemJoinCtorArgDecodeTrace vat ilk gem rd38

end Benchmarks.Dss.GemJoin
