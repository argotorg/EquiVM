import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-!
# ERC6909 benchmark — top-level dispatcher/revert assembly

This file starts with the shared dispatcher failure paths.  The final theorem is assembled after the
per-function `…BodyCore` files land.
-/

/-! ## Shared dispatch and revert traces -/

theorem erc6909Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition, supportsInterfaceTransition, transferTransition,
      transferFromTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, erc6909AllowanceSelectorBytes]; rfl
    · rw [selectorOf, erc6909ApproveSelectorBytes]; rfl
    · rw [selectorOf, erc6909BalanceOfSelectorBytes]; rfl
    · rw [selectorOf, erc6909IsOperatorSelectorBytes]; rfl
    · rw [selectorOf, erc6909SetOperatorSelectorBytes]; rfl
    · rw [selectorOf, erc6909SupportsInterfaceSelectorBytes]; rfl
    · rw [selectorOf, erc6909TransferSelectorBytes]; rfl
    · rw [selectorOf, erc6909TransferFromSelectorBytes]; rfl) h

theorem erc6909Dispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 8 → (erc6909SelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes]
    simpa [erc6909SelBytes] using hnm 5 (by omega)
  · rw [selectorOf, erc6909ApproveSelectorBytes]
    simpa [erc6909SelBytes] using hnm 3 (by omega)
  · rw [selectorOf, erc6909BalanceOfSelectorBytes]
    simpa [erc6909SelBytes] using hnm 0 (by omega)
  · rw [selectorOf, erc6909IsOperatorSelectorBytes]
    simpa [erc6909SelBytes] using hnm 6 (by omega)
  · rw [selectorOf, erc6909SetOperatorSelectorBytes]
    simpa [erc6909SelBytes] using hnm 4 (by omega)
  · rw [selectorOf, erc6909SupportsInterfaceSelectorBytes]
    simpa [erc6909SelBytes] using hnm 1 (by omega)
  · rw [selectorOf, erc6909TransferSelectorBytes]
    simpa [erc6909SelBytes] using hnm 2 (by omega)
  · rw [selectorOf, erc6909TransferFromSelectorBytes]
    simpa [erc6909SelBytes] using hnm 7 (by omega)

theorem erc6909BodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem erc6909X_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt erc6909BenchBytecode)
    (opC := solcGuardTgtOp erc6909BenchBytecode)
    (wC := solcGuardTgtWidth erc6909BenchBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem erc6909X_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt erc6909BenchBytecode)
    (opC := solcGuardTgtOp erc6909BenchBytecode)
    (wC := solcGuardTgtWidth erc6909BenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc erc6909BenchBytecode)
    (rtgt := solcCalldataRevertTgt erc6909BenchBytecode)
    (opR := solcCalldataRevertTgtOp erc6909BenchBytecode)
    (wR := solcCalldataRevertTgtWidth erc6909BenchBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem erc6909X_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 8 → (erc6909SelBytes i == I.calldata.extract 0 4) = false) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqBalance0 :
      UInt256.eq (armSelNatW erc6909BenchBytecode erc6909LowFirstArmPc) (erc6909SelWord I) =
        ⟨0⟩ := by
    rw [erc6909BalanceArmEq I hsz, hnm 0 (by omega)]
    rfl
  have heqLowRest0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩ := by
    intro j hj
    rw [erc6909LowRestArmEq I hsz j hj, hnm (j + 1) (by omega)]
    rfl
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩ := by
    intro j hj
    rw [erc6909HighArmEq I hsz j hj, hnm (j + 4) (by omega)]
    rfl
  obtain ⟨kS, CS, hsplit⟩ := erc6909ReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot :
      UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc) (erc6909SelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit erc6909SplitWellFormed hpivot (by simp)
    have h52 := RD.selectorArmNotTakenAuto h41 (erc6909HighArmsWellFormed 0 (by omega))
      (heqHigh0 0 (by omega)) (by simp)
    have h63 := RD.selectorArmNotTakenAuto h52 (erc6909HighArmsWellFormed 1 (by omega))
      (heqHigh0 1 (by omega)) (by simp)
    have h74 := RD.selectorArmNotTakenAuto h63 (erc6909HighArmsWellFormed 2 (by omega))
      (heqHigh0 2 (by omega)) (by simp)
    have h85 := RD.selectorArmNotTakenAuto h74 (erc6909HighArmsWellFormed 3 (by omega))
      (heqHigh0 3 (by omega)) (by simp)
    have h85' : ∃ k C, RD erc6909BenchBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨85⟩ [erc6909SelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [erc6909HighFirstArmPc, erc6909SplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h85
    obtain ⟨_, _, h85rd⟩ := h85'
    exact h85rd.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h88 := RD.selectorSplitTakenAuto hsplit erc6909SplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h89 := h88.jumpdest (by decide) (by simp)
    have h99 := RD.selectorArmWidthNotTakenAuto 3 h89 erc6909BalanceArmWellFormed
      heqBalance0 (by simp)
    have h110 := RD.selectorArmNotTakenAuto h99 (erc6909LowRestArmsWellFormed 0 (by omega))
      (heqLowRest0 0 (by omega)) (by simp)
    have h121 := RD.selectorArmNotTakenAuto h110 (erc6909LowRestArmsWellFormed 1 (by omega))
      (heqLowRest0 1 (by omega)) (by simp)
    have h132 := RD.selectorArmNotTakenAuto h121 (erc6909LowRestArmsWellFormed 2 (by omega))
      (heqLowRest0 2 (by omega)) (by simp)
    have h132' : ∃ k C, RD erc6909BenchBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨132⟩ [erc6909SelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22 + 22, ?_⟩
      simpa [erc6909LowRestFirstArmPc, erc6909LowFirstArmPc, erc6909LowJumpdestPc,
        erc6909SplitPc, nthArmPc, selArmNextPc, armTgtWidth, armTgt, pushAt,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc, selArmPushSelPcW,
        selArmEqPcW, selArmPushTgtPcW, selArmJumpiPcW, selArmNextPcW, armTgtW,
        armTgtWidthW] using h132
    obtain ⟨_, _, h132rd⟩ := h132'
    have h133 := h132rd.jumpdest (by decide) (by simp)
    exact h133.revertStub (by decide) (by decide) (by decide) (by simp)

theorem erc6909NonPayable {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  exact (erc6909X_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (erc6909BodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem erc6909ShortRevert {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  exact (erc6909X_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (erc6909Dispatch_none_short hsz)

theorem erc6909NoDispatch {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 8 → (erc6909SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (erc6909X_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (erc6909Dispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (erc6909X_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (erc6909Dispatch_none_short hshort)

end OpenZeppelinBench.ERC6909
