import Benchmarks.Dss.DaiJoin.ConstructorTraceBase

/-!
# MakerDAO/Sky DSS DaiJoin constructor argument and guard traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

theorem daiJoinInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress)
    (hcode : I.code = daiJoinCtorCode vat dai)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (daiJoinCtorCode vat dai) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := daiJoin_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by daiJoin_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact daiJoin_ctor_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by daiJoin_ctor_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem daiJoinCtorArgCopyTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat dai : AccountAddress)
    (h : RD (daiJoinCtorCode vat dai) I g s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g s0 ⟨38⟩
      [(UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩, ⟨128⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) rdata acc k' C' := by
  have hcopy : (daiJoinCtorCode vat dai).write 1876 solcFreePtrMem 128 64 =
      daiJoinCtorArgMem vat dai := by
    rfl
  have hfree :
      (((UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩ + (⟨128⟩ : UInt256)).toByteArray).write
          0 (daiJoinCtorArgMem vat dai) 64 32 =
        daiJoinCtorArgFreeMem vat dai := by
    rw [daiJoinCtorArgLen_eq]
    rfl
  have rd38 := daiJoin_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by daiJoin_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨1876⟩, codesize, sub, dup1, push2 ⟨1876⟩, dup4,
    raw codecopy
      9
      (daiJoinCtorArgMem vat dai) (UInt256.ofNat 6)
      (by daiJoin_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [daiJoinCtorArgLen_eq]
        decide)
      (by
        rw [daiJoinCtorArgLen_eq]
        exact hcopy)
      (by rw [daiJoinCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6)
      (by daiJoin_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  have rd38' : RD (daiJoinCtorCode vat dai) I g s0 ⟨38⟩
      [(UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩, ⟨128⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + (0 + 3) + 3 + 2 + 3 + 3 + 3 + 3 +
        (9 + (GasConstants.Gverylow + GasConstants.Gcopy *
          ((((UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩).toNat + 31) / 32))) +
        3 + 3 + 3 + 3 + (0 + 3)) := by
    simpa [
      show (⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨38⟩
        from by decide +native] using rd38
  exact ⟨_, _, rd38'⟩

set_option maxHeartbeats 1000000 in
theorem daiJoinCtorArgSizeGuardTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat dai : AccountAddress)
    (h : RD (daiJoinCtorCode vat dai) I g s0 ⟨38⟩
      [(UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩, ⟨128⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD (daiJoinCtorCode vat dai) I g s0 ⟨61⟩
      [EVM.word dai.val, EVM.word vat.val, ⟨32⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) rdata acc k' C' := by
  have rdBeforeJump := daiJoin_ctor_run h with [
    push1 ⟨64⟩, dup2, lt, iszero, push2 ⟨51⟩]
  have rd51 := rdBeforeJump.jumpiT (by daiJoin_ctor_decode)
    (by rw [daiJoinCtorArgLen_eq]; decide) (by daiJoin_ctor_jd) (by evm_ov)
  have rd61 := daiJoin_ctor_run rd51 with [
    raw jumpdest (by daiJoin_ctor_decode) (by evm_ov),
    pop, dup1,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 6)
      (by daiJoin_ctor_decode) mem_cost (daiJoinCtorArgFreeMem_mload128 vat dai)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, swap2, dup3, add,
    raw mload 0 (EVM.word dai.val) (UInt256.ofNat 6)
      (by daiJoin_ctor_decode) mem_cost (daiJoinCtorArgFreeMem_mload160 vat dai)
      (by decide) (by evm_ov)]
  have rd61' : RD (daiJoinCtorCode vat dai) I g s0 ⟨61⟩
      [EVM.word dai.val, EVM.word vat.val, ⟨32⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + 3 + 3 + 3 + 3 + 10 + 1 + 2 + 3 + (0 + 3) +
        3 + 3 + 3 + 3 + (0 + 3)) := by
    simpa [show (⟨51⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨61⟩ from by decide +native]
      using rd61
  exact ⟨_, _, rd61'⟩

theorem daiJoinCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress)
    (hcode : I.code = daiJoinCtorCode vat dai)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (daiJoinCtorCode vat dai) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨61⟩
      [EVM.word dai.val, EVM.word vat.val, ⟨32⟩]
      (daiJoinCtorArgFreeMem vat dai) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd8 :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := daiJoinCtorCode vat dai) hcode
      (by daiJoin_ctor_decode) (by daiJoin_ctor_decode) (by daiJoin_ctor_decode)
      (by daiJoin_ctor_decode) (by daiJoin_ctor_decode) (by daiJoin_ctor_decode)
  obtain ⟨k18, C18, rd18⟩ :=
    solcGuardCallvalueZero (code := daiJoinCtorCode vat dai) (ctgt := ⟨16⟩) (wC := 2)
      (opC := .PUSH2) rd8 hwv (by decide)
      (by daiJoin_ctor_decode) (by daiJoin_ctor_decode) (by daiJoin_ctor_decode)
      (by daiJoin_ctor_decode) (by daiJoin_ctor_jd)
  have rd18' :
      RD (daiJoinCtorCode vat dai) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by decide +native]
      using rd18
  obtain ⟨_, _, rd38⟩ := daiJoinCtorArgCopyTrace vat dai rd18'
  exact daiJoinCtorArgSizeGuardTrace vat dai rd38

end Benchmarks.Dss.DaiJoin
