import Examples.ERC20.Bytecode
import Examples.ERC20.Spec
import Examples.ERC20.TotalSupply
import Examples.ERC20.BalanceOf
import Examples.ERC20.Allowance
import Examples.ERC20.Approve
import Examples.ERC20.Transfer
import Examples.ERC20.TransferFrom
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# ERC20 — top-level correctness scaffold (driven by the generic dispatcher)

`erc20Correct` runs the **generic solc-dispatcher machinery** end-to-end: prologue → callvalue/​size
guards → selector load → `RD.dispatchTo` over the six arms, reaching the matched function's body
entry, then hands off to that function's correctness obligation.  `erc20ReachBody` is the *proven*
machinery driver (one `RD.dispatchTo`); the per-function body proofs and the selector-identification
/ revert facts are named obligations discharged in ERC20-local helper files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace ERC20

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev erc20SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- ERC20's six selector arms begin at pc 30 (`approve`). -/
abbrev erc20FirstArmPc : UInt256 := ⟨30⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- All six ERC20 selector arms decode as `DUP1; PUSH4; EQ; PUSH2; JUMPI` — proven once. -/
theorem erc20ArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ERC20's six function selectors, indexed in dispatch (arm) order. -/
def erc20SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
  | 3 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
  | 4 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- `ByteArray` `==` reflects equality (no `LawfulBEq ByteArray` instance is in scope). -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

/-- **EVM selector coupling.**  Arm `j`'s `EQ` (its bytecode `PUSH4` value vs the calldata selector
    word) is `1`/`0` exactly as the `j`-th selector's bytes match `calldata[0:4]` — a per-arm
    instance of `evmSelectorDecode`. -/
theorem erc20ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 6) :
    UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc j)) (erc20SelWord I)
      = if (erc20SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- **Selector identification (proven).**  When `calldata[0:4]` is the `i`-th selector, the earlier
    arms' `EQ`s are `0` (the selectors are distinct) and arm `i`'s is non-zero. -/
theorem erc20Matches {I : ExecutionEnv} (i : ℕ) (hi : i < 6) (hsz : 4 ≤ I.calldata.size)
    (hsel : (erc20SelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i → UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc j))
        (erc20SelWord I) = ⟨0⟩)
    ∧ UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc i))
        (erc20SelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = erc20SelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [erc20ArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [erc20ArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- **Machinery driver (proven).**  `cv = 0`, `size ≥ 4`, calldata selects arm `i` (body entry
    `bodyPC`): run prologue → guards → selector load, then `RD.dispatchTo` to reach `bodyPC` with the
    selector word on the stack.  This is where the generic dispatcher actually executes. -/
theorem erc20ReachBody {cA gh bl σ σ₀ A I} {g : Sat256} (i : ℕ) (hi5 : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc j))
        (erc20SelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc i))
        (erc20SelWord I) ≠ ⟨0⟩)
    (hjd : (D_J erc20Bytecode 0).contains bodyPC = true)
    (hbody : armTgt erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc i) = bodyPC) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [erc20SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := erc20FirstArmPc) (bodyPC := bodyPC) (i := i)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => erc20ArmsWellFormed j (le_trans hj hi5)) heq0 htake
    hjd hbody

/-! ## ERC20 dispatch and shared revert traces -/

theorem erc20Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg erc20Contract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [approveTransition, totalSupplyTransition, transferFromTransition, balanceOfTransition,
      transferTransition, allowanceTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, erc20ApproveSelectorBytes]; rfl
    · rw [selectorOf, erc20TotalSupplySelectorBytes]; rfl
    · rw [selectorOf, erc20TransferFromSelectorBytes]; rfl
    · rw [selectorOf, erc20BalanceOfSelectorBytes]; rfl
    · rw [selectorOf, erc20TransferSelectorBytes]; rfl
    · rw [selectorOf, erc20AllowanceSelectorBytes]; rfl) h

theorem erc20Dispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == cd.extract 0 4) = false) :
    dispatchMsg erc20Contract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [erc20Contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc20ApproveSelectorBytes]; simpa [erc20SelBytes] using hnm 0 (by omega)
  · rw [selectorOf, erc20TotalSupplySelectorBytes]; simpa [erc20SelBytes] using hnm 1 (by omega)
  · rw [selectorOf, erc20TransferFromSelectorBytes]; simpa [erc20SelBytes] using hnm 2 (by omega)
  · rw [selectorOf, erc20BalanceOfSelectorBytes]; simpa [erc20SelBytes] using hnm 3 (by omega)
  · rw [selectorOf, erc20TransferSelectorBytes]; simpa [erc20SelBytes] using hnm 4 (by omega)
  · rw [selectorOf, erc20AllowanceSelectorBytes]; simpa [erc20SelBytes] using hnm 5 (by omega)

theorem erc20BodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ erc20Contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody erc20Config erc20Contract evm locals t.body .reverted := by
  simp [erc20Contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem erc20X_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt erc20Bytecode) (opC := solcGuardTgtOp erc20Bytecode)
    (wC := solcGuardTgtWidth erc20Bytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem erc20X_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt erc20Bytecode) (opC := solcGuardTgtOp erc20Bytecode)
    (wC := solcGuardTgtWidth erc20Bytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc erc20Bytecode)
    (rtgt := solcCalldataRevertTgt erc20Bytecode)
    (opR := solcCalldataRevertTgtOp erc20Bytecode)
    (wR := solcCalldataRevertTgtWidth erc20Bytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem erc20X_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat erc20Bytecode (nthArmPc erc20Bytecode erc20FirstArmPc j))
        (erc20SelWord I) = ⟨0⟩ := by
    intro j hj
    rw [erc20ArmEq I hsz j hj]
    rw [hnm j hj]
    rfl
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k1, C1, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt erc20Bytecode) (opC := solcGuardTgtOp erc20Bytecode)
    (wC := solcGuardTgtWidth erc20Bytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  obtain ⟨k2, C2, h2⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc erc20Bytecode)
    (selLoadTgt := solcCalldataRevertTgt erc20Bytecode)
    (opR := solcCalldataRevertTgtOp erc20Bytecode)
    (wR := solcCalldataRevertTgtWidth erc20Bytecode)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  have h4 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) erc20FirstArmPc
      [erc20SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3 C3 := by
    simpa [erc20FirstArmPc, erc20SelWord, solcFirstArmPcFromPrefix, solcSelectorLoadPc,
      solcCalldataJumpiPc, solcCalldataRevertPushPc, solcDispatchBodyPc] using h3
  have h5 := h4
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 4 (by omega)) (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (erc20ArmsWellFormed 5 (by omega)) (heq0 5 (by omega)) (by simp)
  have h96 : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨96⟩
      [erc20SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨k3 + 5 + 5 + 5 + 5 + 5 + 5, C3 + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
    simpa [erc20FirstArmPc, nthArmPc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h5
  obtain ⟨_, _, h96rd⟩ := h96
  exact evm_run h96rd with [
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## Per-function body obligations (take the dispatcher-reached cursor) -/

/-- From `approve`'s body entry (pc 100), the body refines its Solm transition. -/
theorem erc20ApproveBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨100⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20ApproveBodyCore hcode hsize hperm hwv hsel hreach

/-- `totalSupply` body (pc 148) refines its transition. -/
theorem erc20TotalSupplyBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨148⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20TotalSupplyBodyCore hcode hwv hsel hreach

/-- `transferFrom` body (pc 178) refines its transition. -/
theorem erc20TransferFromBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨178⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20TransferFromBodyCore hcode hsize hperm hwv hsel hreach

/-- `balanceOf` body (pc 226) refines its transition. -/
theorem erc20BalanceOfBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨226⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20BalanceOfBodyCore hcode hsize hwv hsel hreach

/-- `transfer` body (pc 274) refines its transition. -/
theorem erc20TransferBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨274⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20TransferBodyCore hcode hsize hperm hwv hsel hreach

/-- `allowance` body (pc 322) refines its transition. -/
theorem erc20AllowanceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨322⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact erc20AllowanceBodyCore hcode hsize hwv hsel hreach

/-! ## Revert obligations -/

/-- Every selector misses (so `dispatchMsg = none`) ⇒ the EVM falls through to the no-match
    target and reverts.  `hnm` is the explicit no-match evidence: for each of the six arms, the
    bytecode selector does not equal `calldata[0:4]`. -/
theorem erc20NoDispatch {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (erc20X_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (erc20Dispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (erc20X_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (erc20Dispatch_none_short hshort)

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch.
    The other no-dispatch path; here no selector can match because `calldata[0:4]` has fewer than
    four bytes. -/
theorem erc20ShortRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact (erc20X_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (erc20Dispatch_none_short hsz)

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable). -/
theorem erc20NonPayable {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  exact (erc20X_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg erc20Contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ erc20Contract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (erc20BodyReverts_nonPayable t htmem (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-! ## Top-level theorem — drive the dispatcher, route each body to its correctness -/

/-- The deployed ERC20 runtime bytecode refines the Solm specification, for every initial state.
    `callvalue ≠ 0` / short calldata / no-match revert; otherwise the dispatcher machinery
    (`erc20ReachBody`) drives the EVM to the matched function's body entry, handed to that function's
    body obligation. -/
theorem erc20Correct : runtimeEquivalence!?! erc20Config erc20Bytecode erc20Contract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · -- callvalue = 0, size ≥ 4: dispatch on the selector, driving the machinery to each body
      by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · exact erc20ApproveBody hcode hsize hperm hwv h0
          (erc20ReachBody 0 (by omega) ⟨100⟩ hcode hwv hsz hsize (erc20Matches 0 (by omega) hsz h0).1
            (erc20Matches 0 (by omega) hsz h0).2 (by jump_dest) (by decide))
      · by_cases h1 : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
        · exact erc20TotalSupplyBody hcode hsize hperm hwv h1
            (erc20ReachBody 1 (by omega) ⟨148⟩ hcode hwv hsz hsize (erc20Matches 1 (by omega) hsz h1).1
              (erc20Matches 1 (by omega) hsz h1).2 (by jump_dest) (by decide))
        · by_cases h2 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
          · exact erc20TransferFromBody hcode hsize hperm hwv h2
              (erc20ReachBody 2 (by omega) ⟨178⟩ hcode hwv hsz hsize (erc20Matches 2 (by omega) hsz h2).1
                (erc20Matches 2 (by omega) hsz h2).2 (by jump_dest) (by decide))
          · by_cases h3 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
            · exact erc20BalanceOfBody hcode hsize hperm hwv h3
                (erc20ReachBody 3 (by omega) ⟨226⟩ hcode hwv hsz hsize (erc20Matches 3 (by omega) hsz h3).1
                  (erc20Matches 3 (by omega) hsz h3).2 (by jump_dest) (by decide))
            · by_cases h4 : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
              · exact erc20TransferBody hcode hsize hperm hwv h4
                  (erc20ReachBody 4 (by omega) ⟨274⟩ hcode hwv hsz hsize (erc20Matches 4 (by omega) hsz h4).1
                    (erc20Matches 4 (by omega) hsz h4).2 (by jump_dest) (by decide))
              · by_cases h5 : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                · exact erc20AllowanceBody hcode hsize hperm hwv h5
                    (erc20ReachBody 5 (by omega) ⟨322⟩ hcode hwv hsz hsize (erc20Matches 5 (by omega) hsz h5).1
                      (erc20Matches 5 (by omega) hsz h5).2 (by jump_dest) (by decide))
                · -- size ≥ 4 but no selector matches: explicit no-match evidence from h0..h5
                  refine erc20NoDispatch hcode hsize hperm hwv ?_
                  intro i hi
                  interval_cases i
                  · simpa [selIs, erc20SelBytes] using h0
                  · simpa [selIs, erc20SelBytes] using h1
                  · simpa [selIs, erc20SelBytes] using h2
                  · simpa [selIs, erc20SelBytes] using h3
                  · simpa [selIs, erc20SelBytes] using h4
                  · simpa [selIs, erc20SelBytes] using h5
    · -- callvalue = 0, size < 4: size guard reverts before dispatch
      exact erc20ShortRevert hcode hsize hperm hwv (by omega)
  · -- callvalue ≠ 0: non-payable revert
    exact erc20NonPayable hcode hwv

end ERC20
