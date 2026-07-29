import Benchmarks.Dss.LinearDecrease.Trusted

/-!
# MakerDAO/Sky DSS LinearDecrease dispatcher facts

Solm dispatch routing facts and shared dispatcher-level proof obligations.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.LinearDecrease

attribute [local simp]
  denySelectorBytes
  fileSelectorBytes
  priceSelectorBytes
  relySelectorBytes
  tauSelectorBytes
  wardsSelectorBytes

theorem stairstepDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 0)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatchFile {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 1)) :
    dispatchMsg contract I.calldata = some fileTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatchPrice {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 2)) :
    dispatchMsg contract I.calldata = some priceTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some priceTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 3)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatchTau {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 4)) :
    dispatchMsg contract I.calldata = some tauTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tauTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (stairstepSelBytes 5)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = stairstepSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem stairstepDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [denyTransition, fileTransition, priceTransition, relyTransition, tauTransition,
      wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, denySelectorBytes, fileSelectorBytes, priceSelectorBytes,
        relySelectorBytes, tauSelectorBytes, wardsSelectorBytes]
      native_decide) h

theorem stairstepDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 6 → (stairstepSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, denySelectorBytes]
    simpa [stairstepSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, fileSelectorBytes]
    simpa [stairstepSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, priceSelectorBytes]
    simpa [stairstepSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [stairstepSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, tauSelectorBytes]
    simpa [stairstepSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [stairstepSelBytes] using hnm 5 (by omega)

theorem stairstepNoSelectorMatches {I : ExecutionEnv}
    (hdeny : ¬ selIs I (stairstepSelBytes 0))
    (hfile : ¬ selIs I (stairstepSelBytes 1))
    (hprice : ¬ selIs I (stairstepSelBytes 2))
    (hrely : ¬ selIs I (stairstepSelBytes 3))
    (htau : ¬ selIs I (stairstepSelBytes 4))
    (hwards : ¬ selIs I (stairstepSelBytes 5)) :
    ∀ i, i < 6 → (stairstepSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, stairstepSelBytes] using hdeny
  · simpa [selIs, stairstepSelBytes] using hfile
  · simpa [selIs, stairstepSelBytes] using hprice
  · simpa [selIs, stairstepSelBytes] using hrely
  · simpa [selIs, stairstepSelBytes] using htau
  · simpa [selIs, stairstepSelBytes] using hwards

/-! ## Runtime dispatcher PCs and selector arms

These constants are read from `runtime.hex`; keep them synchronized with
`linearDecreaseBytecode`.
-/

abbrev stairstepFirstArmPc : UInt256 := ⟨32⟩
abbrev stairstepDispatchBodyPc : UInt256 := ⟨18⟩
abbrev stairstepSelectorLoadPc : UInt256 := ⟨26⟩
abbrev stairstepDispatchRevertPc : UInt256 := ⟨98⟩

def stairstepArmSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 1 => ⟨#[0x48, 0x7a, 0x23, 0x95]⟩ -- price(uint256,uint256)
  | 2 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 3 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 4 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()

abbrev stairstepFileEntryPc : UInt256 := ⟨103⟩
abbrev stairstepPriceEntryPc : UInt256 := ⟨140⟩
abbrev stairstepRelyEntryPc : UInt256 := ⟨193⟩
abbrev stairstepDenyEntryPc : UInt256 := ⟨231⟩
abbrev stairstepWardsEntryPc : UInt256 := ⟨269⟩
abbrev stairstepTauEntryPc : UInt256 := ⟨307⟩

theorem stairstepBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem stairstepSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    stairstepSelWord I = sel := by
  simpa [stairstepSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

set_option maxHeartbeats 1000000 in
theorem stairstepArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed linearDecreaseBytecode
      (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem stairstepArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) =
      if (stairstepArmSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem stairstepReachFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD linearDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        stairstepFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [stairstepFirstArmPc, stairstepSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := linearDecreaseBytecode)
      (bodyPc := stairstepDispatchBodyPc) (loadPc := stairstepSelectorLoadPc)
      (firstPc := stairstepFirstArmPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := stairstepDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem stairstepReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc i))
        (stairstepSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J linearDecreaseBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt linearDecreaseBytecode
        (nthArmPc linearDecreaseBytecode stairstepFirstArmPc i) = bodyPC) :
    ∃ k C, RD linearDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    stairstepReachFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => stairstepArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem stairstepNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD linearDecreaseBytecode I g (initState cA gh bl σ σ₀ g A I)
      stairstepFirstArmPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h98 := h
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (stairstepArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h98 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem stairstepX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem stairstepX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt linearDecreaseBytecode)
    (opC := solcGuardTgtOp linearDecreaseBytecode)
    (wC := solcGuardTgtWidth linearDecreaseBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h98 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 stairstepDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h98 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem stairstepX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 6 → (stairstepSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [stairstepArmEq I hsz 0 (by omega)]
      have hfalse : (stairstepArmSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepArmEq I hsz 1 (by omega)]
      have hfalse : (stairstepArmSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepArmEq I hsz 2 (by omega)]
      have hfalse : (stairstepArmSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepArmEq I hsz 3 (by omega)]
      have hfalse : (stairstepArmSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepArmEq I hsz 4 (by omega)]
      have hfalse : (stairstepArmSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [stairstepArmEq I hsz 5 (by omega)]
      have hfalse : (stairstepArmSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [stairstepArmSelBytes, stairstepSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
  obtain ⟨_, _, hfirst⟩ :=
    stairstepReachFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  exact stairstepNoMatchRevert hfirst heq

theorem stairstepNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (stairstepX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (stairstepBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem stairstepNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = linearDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 6 → (stairstepSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (stairstepX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (stairstepDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (stairstepX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (stairstepDispatch_none_short hshort)

end Benchmarks.Dss.LinearDecrease
