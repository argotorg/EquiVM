import Benchmarks.Dss.Spot.ConstructorBase

/-!
# MakerDAO/Sky DSS Spotter constructor argument and guard traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = spotCtorCode vat)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (spotCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := spot_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by spot_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact spot_ctor_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by spot_ctor_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem spotCtorArgCopyTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (spotCtorCode vat) I g s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (spotCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (spotCtorCode vat).size).sub ⟨2320⟩, ⟨128⟩]
      (spotCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k' C' := by
  have hcopy : (spotCtorCode vat).write 2320 solcFreePtrMem 128 32 = spotCtorArgMem vat := by
    rfl
  have hfree :
      (((UInt256.ofNat (spotCtorCode vat).size).sub ⟨2320⟩ + (⟨128⟩ : UInt256)).toByteArray).write
          0 (spotCtorArgMem vat) 64 32 =
        spotCtorArgFreeMem vat := by
    rw [spotCtorArgLen_eq]
    rfl
  have rd38 := spot_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by spot_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨2320⟩, codesize, sub, dup1, push2 ⟨2320⟩, dup4,
    raw codecopy
      6
      (spotCtorArgMem vat) (UInt256.ofNat 5)
      (by spot_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [spotCtorArgLen_eq]
        decide)
      (by
        rw [spotCtorArgLen_eq]
        exact hcopy)
      (by rw [spotCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (spotCtorArgFreeMem vat) (UInt256.ofNat 5)
      (by spot_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  have rd38' : RD (spotCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (spotCtorCode vat).size).sub ⟨2320⟩, ⟨128⟩]
      (spotCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + (0 + 3) + 3 + 2 + 3 + 3 + 3 + 3 +
        (6 + (GasConstants.Gverylow + GasConstants.Gcopy *
          ((((UInt256.ofNat (spotCtorCode vat).size).sub ⟨2320⟩).toNat + 31) / 32))) +
        3 + 3 + 3 + 3 + (0 + 3)) := by
    simpa [
      show (⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨38⟩
        from by native_decide] using rd38
  exact ⟨_, _, rd38'⟩

set_option maxHeartbeats 1000000 in
theorem spotCtorArgSizeGuardTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (spotCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (spotCtorCode vat).size).sub ⟨2320⟩, ⟨128⟩]
      (spotCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (spotCtorCode vat) I g s0 ⟨54⟩
      [EVM.word vat.val] (spotCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k' C' := by
  have rdBeforeJump := spot_ctor_run h with [
    push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨51⟩]
  have rd51 := rdBeforeJump.jumpiT (by spot_ctor_decode)
    (by rw [spotCtorArgLen_eq]; decide) (by spot_ctor_jd) (by evm_ov)
  have rd54 := spot_ctor_run rd51 with [
    raw jumpdest (by spot_ctor_decode) (by evm_ov),
    pop,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 5)
      (by spot_ctor_decode) mem_cost (spotCtorArgFreeMem_mload128 vat)
      (by decide) (by evm_ov)]
  have rd54' : RD (spotCtorCode vat) I g s0 ⟨54⟩
      [EVM.word vat.val] (spotCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + 3 + 3 + 3 + 3 + 10 + 1 + 2 + (0 + 3)) := by
    simpa [show (⟨51⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨54⟩
      from by native_decide] using rd54
  exact ⟨_, _, rd54'⟩

theorem spotCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = spotCtorCode vat)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
      [EVM.word vat.val] (spotCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd8 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := spotCtorCode vat) hcode
      (by spot_ctor_decode) (by spot_ctor_decode) (by spot_ctor_decode)
      (by spot_ctor_decode) (by spot_ctor_decode) (by spot_ctor_decode)
  obtain ⟨k18, C18, rd18⟩ :=
    solcGuardCallvalueZero (code := spotCtorCode vat) (ctgt := ⟨16⟩) (wC := 2)
      (opC := .PUSH2) rd8 hwv (by decide)
      (by spot_ctor_decode) (by spot_ctor_decode) (by spot_ctor_decode) (by spot_ctor_decode)
      (by spot_ctor_jd)
  have rd18' :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by native_decide]
      using rd18
  obtain ⟨_, _, rd38⟩ := spotCtorArgCopyTrace vat rd18'
  exact spotCtorArgSizeGuardTrace vat rd38

end Benchmarks.Dss.Spot
