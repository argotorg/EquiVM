import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestRoutines

/-! Complete interest-accrual simulation, including calls, stores, minting, and failures. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem sourceStateStoreSelf {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (slot value : UInt256) :
    let changed := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value
    SourceState s0 I changed.accountMap changed := by
  refine ⟨?_, (storageStore_executionEnv _ _ _ _).trans hs.env, rfl⟩
  have hw := (hs.storageWrite slot value).world
  simpa only [← hs.env] using hw

theorem accrueInterestStoredSourceState {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (lost total : UInt256) :
    SourceState s0 I (accrueInterestStoredState evm lost total).accountMap
      (accrueInterestStoredState evm lost total) :=
  sourceStateStoreSelf (sourceStateStoreSelf hs ⟨22⟩ total) ⟨23⟩ lost

theorem mintBalanceSourceState {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (recipient : AccountAddress) (value : UInt256) :
    SourceState s0 I (mintBalanceState evm recipient value).accountMap
      (mintBalanceState evm recipient value) :=
  sourceStateStoreSelf (sourceStateStoreSelf hs ⟨2⟩ (mintOldSupply evm + value))
    (balanceSlot recipient) (balanceWord (mintSupplyState evm value) recipient + value)

theorem accrueInterestSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 40 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14262⟩ (ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (accrueInterestFrame (immStore v) ptr) evm
      allocatedAccrueInterestFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecFuncBody config (accrueInterestFrame (immStore v) ptr) evm
      allocatedAccrueInterestFunction.body .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (ptr' : UInt256) (mem' out : ByteArray),
      I.perm = true ∧ SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (accrueInterestFrame (immStore v) ptr) evm
        allocatedAccrueInterestFunction.body (.returned frame' evm' [uint256Value ptr']) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := accrueInterestReachCalculation v (by omega) rd
  rcases accruedAssetsSimulation v
      (by simp only [accrueInterestCalcTail, List.length_cons]; omega)
      hcalldata hfree hlo hmem hs
      (by rw [metaMorphoV1_1PatchedValidJumps]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨evm', frame', lost, total, shares, ptr', mem', out,
      hs', _, _, _, _, hbody, aw2, k2, C2, h2⟩
  · exact .inl ⟨accrueInterestCalculationReverts v hbad, hrev⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := accrueInterestReachLastStore v (by omega) h2
    rw [← hs'.env] at h3
    by_cases hperm : I.perm = true
    · have hp : evm'.executionEnv.perm = true := by rw [hs'.env]; exact hperm
      obtain ⟨aw4, k4, C4, h4⟩ := accrueInterestStoreReturn v (by omega) hp h3
      let changed := accrueInterestStoredState evm' lost total
      have hs4 : SourceState s0 I changed.accountMap changed :=
        accrueInterestStoredSourceState hs' lost total
      have hl := accrueInterestStoredLocals (immStore v) ptr lost total shares ptr'
      rw [hs'.env] at h4
      by_cases hzero : shares = ⟨0⟩
      · rw [accrueInterestBranchPC, if_pos hzero] at h4
        obtain ⟨mem5, aw5, k5, C5, h5⟩ := accrueInterestFinish v (by omega) hperm hret h4
        exact .inr (.inr ⟨changed, _, ptr', mem5, out, hperm, hs4,
          ExecFuncBody.execBlockRet (accrueInterestValuesPrefix v hbody
            (accrueInterestStoresPrefix _ _ _ _ _ _ _ (accrueInterestZeroSource hl hzero))),
          aw5, k5, C5, h5⟩)
      · rw [accrueInterestBranchPC, if_neg hzero, ← hs4.env] at h4
        obtain ⟨aw5, k5, C5, h5⟩ := accrueInterestReachMint v (by omega) h4
        by_cases hgood : mintAllowed changed (accrueFeeRecipient changed) shares
        · have hp4 : changed.executionEnv.perm = true := by rw [hs4.env]; exact hperm
          obtain ⟨aw6, k6, C6, h6⟩ := mintReturn v
            (by simp only [accrueInterestEventStack, List.length_cons]; omega) hgood hp4
            (by rw [metaMorphoV1_1PatchedValidJumps]; jump_dest) h5
          rw [hs4.env] at h6
          obtain ⟨mem7, aw7, k7, C7, h7⟩ := accrueInterestMintFinish v
            (by omega) hperm hret h6
          exact .inr (.inr ⟨_, _, ptr', mem7, out, hperm,
            mintBalanceSourceState hs4 (accrueFeeRecipient changed) shares,
            ExecFuncBody.execBlockRet (accrueInterestValuesPrefix v hbody
              (accrueInterestStoresPrefix _ _ _ _ _ _ _
                (accrueInterestMintSource hl hzero hgood))), aw7, k7, C7, h7⟩)
        · exact .inl ⟨ExecFuncBody.execBlockRevert (accrueInterestValuesPrefix v hbody
            (accrueInterestStoresPrefix _ _ _ _ _ _ _
              (accrueInterestMintReverts hl hzero hgood))),
            mintRevert v (by simp only [accrueInterestEventStack, List.length_cons]; omega)
              hgood h5⟩
    · have hp : evm'.executionEnv.perm = false := by
        rw [hs'.env]; exact Bool.eq_false_of_not_eq_true hperm
      exact .inr (.inl ⟨ExecFuncBody.execBlockStatic (accrueInterestValuesPrefix v hbody
        (accrueInterestStoresStatic _ _ _ _ _ _ _ hp)),
        updateLastAssetsStatic v
          (by simp only [accrueInterestStoreTail, List.length_cons]; omega) hp h3⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
