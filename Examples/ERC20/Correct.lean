import Examples.ERC20.Bytecode
import Examples.ERC20.Spec
import Examples.ERC20.TotalSupply
import Examples.ERC20.BalanceOf
import Examples.ERC20.Allowance
import Examples.ERC20.Approve
import Examples.ERC20.Transfer
import Examples.ERC20.TransferFrom
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Initcode
import Reasoning.Memory
import Mathlib.Tactic.IntervalCases

/-!
# ERC20 — top-level correctness scaffold (driven by the generic dispatcher)

`erc20Correct` runs the **generic solc-dispatcher machinery** end-to-end: prologue → callvalue/​size
guards → selector load → `RD.dispatchTo` over the six arms, reaching the matched function's body
entry, then hands off to that function's correctness obligation.  `erc20ReachBody` is the *proven*
machinery driver (one `RD.dispatchTo`); the per-function body proofs and the selector-identification
/ revert facts are named obligations discharged in ERC20-local helper files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

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
  rw [dispatchMsg_eq_dispatchList erc20Contract cd (by rfl)]
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
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
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
theorem erc20ApproveBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨100⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20ApproveBodyCore hcode hsize hperm hwv hsel hreach hAccounts

/-- `totalSupply` body (pc 148) refines its transition. -/
theorem erc20TotalSupplyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨148⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20TotalSupplyBodyCore hcode hwv hsel hreach hAccounts

/-- `transferFrom` body (pc 178) refines its transition. -/
theorem erc20TransferFromBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨178⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20TransferFromBodyCore hcode hsize hperm hwv hsel hreach hAccounts

/-- `balanceOf` body (pc 226) refines its transition. -/
theorem erc20BalanceOfBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨226⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20BalanceOfBodyCore hcode hsize hwv hsel hreach hAccounts

/-- `transfer` body (pc 274) refines its transition. -/
theorem erc20TransferBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨274⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20TransferBodyCore hcode hsize hperm hwv hsel hreach hAccounts

/-- `allowance` body (pc 322) refines its transition. -/
theorem erc20AllowanceBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨322⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20AllowanceBodyCore hcode hsize hwv hsel hreach hAccounts

/-! ## Revert obligations -/

/-- Every selector misses (so `dispatchMsg = none`) ⇒ the EVM falls through to the no-match
    target and reverts.  `hnm` is the explicit no-match evidence: for each of the six arms, the
    bytecode selector does not equal `calldata[0:4]`. -/
theorem erc20NoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (erc20X_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (erc20Dispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (erc20X_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (erc20Dispatch_none_short hshort)

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch.
    The other no-dispatch path; here no selector can match because `calldata[0:4]` has fewer than
    four bytes. -/
theorem erc20ShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (erc20X_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (erc20Dispatch_none_short hsz)

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable). -/
theorem erc20NonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (erc20X_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg erc20Contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ erc20Contract.transitions := by
          rw [dispatchMsg_eq_dispatchList erc20Contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (erc20BodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-! ## Top-level theorem — drive the dispatcher, route each body to its correctness -/

/-- The deployed ERC20 runtime bytecode refines the Solm specification, for every initial state.
    `callvalue ≠ 0` / short calldata / no-match revert; otherwise the dispatcher machinery
    (`erc20ReachBody`) drives the EVM to the matched function's body entry, handed to that function's
    body obligation. -/
theorem erc20Correct : runtimeEquivalence erc20Config erc20Bytecode erc20Contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · -- callvalue = 0, size ≥ 4: dispatch on the selector, driving the machinery to each body
      by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · exact erc20ApproveBody hcode hsize hperm hwv h0
          (erc20ReachBody 0 (by omega) ⟨100⟩ hcode hwv hsz hsize (erc20Matches 0 (by omega) hsz h0).1
            (erc20Matches 0 (by omega) hsz h0).2 (by jump_dest) (by decide)) hAccounts
      · by_cases h1 : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
        · exact erc20TotalSupplyBody hcode hsize hperm hwv h1
            (erc20ReachBody 1 (by omega) ⟨148⟩ hcode hwv hsz hsize (erc20Matches 1 (by omega) hsz h1).1
              (erc20Matches 1 (by omega) hsz h1).2 (by jump_dest) (by decide)) hAccounts
        · by_cases h2 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
          · exact erc20TransferFromBody hcode hsize hperm hwv h2
              (erc20ReachBody 2 (by omega) ⟨178⟩ hcode hwv hsz hsize (erc20Matches 2 (by omega) hsz h2).1
                (erc20Matches 2 (by omega) hsz h2).2 (by jump_dest) (by decide)) hAccounts
          · by_cases h3 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
            · exact erc20BalanceOfBody hcode hsize hperm hwv h3
                (erc20ReachBody 3 (by omega) ⟨226⟩ hcode hwv hsz hsize (erc20Matches 3 (by omega) hsz h3).1
                  (erc20Matches 3 (by omega) hsz h3).2 (by jump_dest) (by decide)) hAccounts
            · by_cases h4 : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
              · exact erc20TransferBody hcode hsize hperm hwv h4
                  (erc20ReachBody 4 (by omega) ⟨274⟩ hcode hwv hsz hsize (erc20Matches 4 (by omega) hsz h4).1
                    (erc20Matches 4 (by omega) hsz h4).2 (by jump_dest) (by decide)) hAccounts
              · by_cases h5 : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                · exact erc20AllowanceBody hcode hsize hperm hwv h5
                    (erc20ReachBody 5 (by omega) ⟨322⟩ hcode hwv hsz hsize (erc20Matches 5 (by omega) hsz h5).1
                      (erc20Matches 5 (by omega) hsz h5).2 (by jump_dest) (by decide)) hAccounts
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

/-! ## Constructor side -/

theorem erc20CtorPrefix_size : erc20CtorPrefix.size = 55 := by
  native_decide

theorem erc20Bytecode_size : erc20Bytecode.size = 2708 := by
  native_decide

theorem erc20Initcode_size : erc20Initcode.size = 2763 := by
  rw [erc20Initcode, ByteArray.size_append, erc20CtorPrefix_size, erc20Bytecode_size]

theorem erc20Initcode_runtime_window :
    erc20Initcode.extract 55 (55 + 2708) = erc20Bytecode := by
  unfold erc20Initcode
  exact extract_append_right' erc20CtorPrefix erc20Bytecode 55 (55 + 2708)
    erc20CtorPrefix_size.symm
    (by rw [erc20CtorPrefix_size, erc20Bytecode_size])

noncomputable def erc20CtorCode (initialSupply : UInt256) : ByteArray :=
  erc20Initcode ++ (EVM.Word.toBytesBE initialSupply).toByteArray

theorem erc20Initcode_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 55) :
    decode (erc20Initcode ++ tail) pc = decode erc20Initcode pc :=
  Reasoning.Theory.decode_append_left_window erc20Initcode tail pc
    (by rw [erc20Initcode_size]; omega) (by rw [erc20Initcode_size]; norm_num)

macro "erc20_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [erc20Initcode_decode_append _ _ (by decide)]
      | (unfold erc20CtorCode; rw [erc20Initcode_decode_append _ _ (by decide)]);
     native_decide))

macro "erc20_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold erc20CtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "erc20_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by erc20_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by erc20_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by erc20_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by erc20_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem erc20Deployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    erc20Config.selfDeployment erc20Initcode args = some deployedInitcode →
    ∃ i : Int,
      args = [.int i]
        ∧ 0 ≤ i
        ∧ i < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode = erc20Initcode ++ (EVM.Word.toBytesBE (EVM.word i.toNat)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [erc20Config, genSolidityConstructorDeployment, erc20Contract, constructorDecl,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
              constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              uint256, uint256Int, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
              encodeABIWord?] at h
      | nil =>
          cases arg with
          | int i =>
              by_cases hbounds : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
              · simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  uint256, uint256Int, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (erc20Initcode ++ args.toByteArray)) = some deployedInitcode at h
                split at h
                · simp at h
                  refine ⟨i, rfl, hbounds.1, hbounds.2, ?_⟩
                  exact h.symm
                · rename_i hnot
                  exact False.elim (hnot hbounds)
              · simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  uint256, uint256Int, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (erc20Initcode ++ args.toByteArray)) = some deployedInitcode at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | bool b =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | address a =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [erc20Config, genSolidityConstructorDeployment, erc20Contract,
                constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

noncomputable def erc20CtorArgMem (initialSupply : UInt256) : ByteArray :=
  (UInt256.toByteArray initialSupply).write 0 solcFreePtrMem 64 32

noncomputable def erc20CtorHashMem (caller : AccountAddress) (initialSupply : UInt256) : ByteArray :=
  twoWordHashMem (UInt256.ofNat caller.val) ⟨0⟩ (erc20CtorArgMem initialSupply)

noncomputable def erc20CtorReturnMem (caller : AccountAddress) (initialSupply : UInt256) : ByteArray :=
  (erc20CtorCode initialSupply).write 55 (erc20CtorHashMem caller initialSupply) 0 2708

theorem erc20CtorArg_extract (initialSupply : UInt256) :
    (erc20CtorCode initialSupply).extract 2763 (2763 + 32) =
      (EVM.Word.toBytesBE initialSupply).toByteArray := by
  unfold erc20CtorCode
  exact extract_append_right' erc20Initcode (EVM.Word.toBytesBE initialSupply).toByteArray
    2763 (2763 + 32)
    erc20Initcode_size.symm
    (by rw [erc20Initcode_size, word_toBytesBE_toByteArray_size])

theorem erc20CtorArg_codecopy_mem (initialSupply : UInt256) :
    (erc20CtorCode initialSupply).write 2763 solcFreePtrMem 64 32 =
      erc20CtorArgMem initialSupply := by
  unfold erc20CtorArgMem
  rw [write_eq_gen_from (erc20CtorCode initialSupply) solcFreePtrMem 2763 64 32
    (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, erc20Initcode_size,
      word_toBytesBE_toByteArray_size])
    (by rw [solcFreePtrMem_size])]
  rw [write32_eq (UInt256.toByteArray initialSupply) solcFreePtrMem 64
    (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; norm_num)]
  rw [erc20CtorArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [show (UInt256.toByteArray initialSupply).extract 0 32 =
      UInt256.toByteArray initialSupply from by
    rw [show 32 = (UInt256.toByteArray initialSupply).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem erc20CtorArgMem_size (initialSupply : UInt256) :
    (erc20CtorArgMem initialSupply).size = 96 := by
  unfold erc20CtorArgMem
  exact writeWord_size_of_96 solcFreePtrMem initialSupply 64 solcFreePtrMem_size (by omega)

theorem erc20CtorArgMem_read64 (initialSupply : UInt256) :
    (erc20CtorArgMem initialSupply).readWithPadding 64 32 = UInt256.toByteArray initialSupply := by
  unfold erc20CtorArgMem
  exact toByteArray_write_read_back_of_gap initialSupply solcFreePtrMem 64
    (by simp [solcFreePtrMem_size])

theorem erc20CtorArgMem_mload64 (initialSupply : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (erc20CtorArgMem initialSupply).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 3) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((erc20CtorArgMem initialSupply).readWithPadding 64 32)))
      = initialSupply := by
  exact mloadWordValue_of_readWithPadding
    (mem := erc20CtorArgMem initialSupply) (aw := UInt256.ofNat 3) (off := ⟨64⟩)
    (v := initialSupply)
    (by rw [erc20CtorArgMem_size]; decide)
    (by decide)
    (erc20CtorArgMem_read64 initialSupply)

theorem erc20CtorHashMem_size (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorHashMem caller initialSupply).size = 96 := by
  unfold erc20CtorHashMem
  exact twoWordHashMem_size_96 (UInt256.ofNat caller.val) ⟨0⟩ (erc20CtorArgMem_size initialSupply)

theorem erc20CtorKeccakSlot (caller : AccountAddress) (initialSupply : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((erc20CtorHashMem caller initialSupply).readWithPadding 0 64)))
      = erc20BalanceOfSlot (.address caller) := by
  unfold erc20CtorHashMem erc20BalanceOfSlot erc20MappingSlot
  rw [twoWordHashMem_read0_64 (UInt256.ofNat caller.val) ⟨0⟩
    (erc20CtorArgMem_size initialSupply)]
  rw [approveSource_keyValueToWord caller]
  exact mappingSlot_single (UInt256.ofNat caller.val) ⟨0⟩

theorem erc20CtorRuntime_codecopy_mem (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorCode initialSupply).write 55 (erc20CtorHashMem caller initialSupply) 0 2708 =
      erc20CtorReturnMem caller initialSupply := rfl

theorem erc20CtorReturnMem_read (caller : AccountAddress) (initialSupply : UInt256) :
    (erc20CtorReturnMem caller initialSupply).readWithPadding 0 2708 = erc20Bytecode := by
  unfold erc20CtorReturnMem
  rw [write0_read_back_from_gen (erc20CtorCode initialSupply) (erc20CtorHashMem caller initialSupply)
    55 2708 (by decide)
    (by rw [erc20CtorCode, ByteArray.size_append, erc20Initcode_size,
      word_toBytesBE_toByteArray_size]; omega)
    (by decide)]
  have hleft :
      (erc20CtorCode initialSupply).extract 55 (55 + 2708) =
        erc20Initcode.extract 55 (55 + 2708) := by
    have h := extract_append_left erc20Initcode (EVM.Word.toBytesBE initialSupply).toByteArray
      55 (55 + 2708) (by rw [erc20Initcode_size])
    simpa [erc20CtorCode] using h
  rw [hleft, erc20Initcode_runtime_window]

theorem erc20InitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = erc20Initcode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (erc20Initcode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (erc20Initcode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd6 := erc20_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd6.revertStub (by erc20_ctor_decode) (by erc20_ctor_decode) (by erc20_ctor_decode)
    (by simp)

theorem erc20InitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (initialSupply : UInt256)
    (hcode : I.code = erc20CtorCode initialSupply)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (erc20CtorCode initialSupply) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (erc20BalanceOfSlot (.address I.source)) initialSupply)
          ⟨2⟩ initialSupply)
      erc20Bytecode := by
  have rd0 :
      RD (erc20CtorCode initialSupply) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rdBeforeBalanceStore := erc20_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩,
    jumpiT (by rw [hwv]; decide) (by erc20_ctor_jd),
    jumpdest, pop,
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push2 ⟨2763⟩, push1 ⟨64⟩,
    raw codecopy 0 (erc20CtorArgMem initialSupply) (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      (erc20CtorArg_codecopy_mem initialSupply)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 initialSupply (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      (erc20CtorArgMem_mload64 initialSupply)
      (by decide) (by evm_ov),
    dup1, caller, push0,
    raw mstore 0 (wordAt0Mem (UInt256.ofNat I.source.val) (erc20CtorArgMem initialSupply))
      (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0, push1 ⟨32⟩,
    raw mstore 0 (erc20CtorHashMem I.source initialSupply) (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (erc20BalanceOfSlot (.address I.source)) (UInt256.ofNat 3)
      (by erc20_ctor_decode)
      mem_cost
      (erc20CtorKeccakSlot I.source initialSupply)
      (by decide) (by evm_ov)]
  obtain ⟨k', C', rdAfterBalanceStore⟩ :=
    rdBeforeBalanceStore.sstore hperm (by erc20_ctor_decode) (by evm_ov)
  have rdBeforeTotalSupplyStore := erc20_ctor_run rdAfterBalanceStore with [
    push1 ⟨2⟩]
  obtain ⟨k'', C'', rdAfterTotalSupplyStore⟩ :=
    rdBeforeTotalSupplyStore.sstore hperm (by erc20_ctor_decode) (by evm_ov)
  have rdBeforeReturn := erc20_ctor_run rdAfterTotalSupplyStore with [
    push2 ⟨2708⟩, push1 ⟨55⟩, push0,
    raw codecopy 260 (erc20CtorReturnMem I.source initialSupply) (UInt256.ofNat 85)
      (by erc20_ctor_decode)
      mem_cost
      (erc20CtorRuntime_codecopy_mem I.source initialSupply)
      (by decide) (by evm_ov),
    push2 ⟨2708⟩, push0]
  exact rdBeforeReturn.ret 0 erc20Bytecode
    (by erc20_ctor_decode)
    mem_cost
    (erc20CtorReturnMem_read I.source initialSupply)
    (by evm_ov)

def erc20CtorLocals (initialSupply : Int) : Store :=
  Std.HashMap.ofList
    (List.zip (erc20Contract.ctor.params.map Param.name) [.int initialSupply])

theorem erc20CtorLocals_get_initialSupply (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "initialSupply" = some (.int initialSupply) := by
  unfold erc20CtorLocals
  simp [erc20Contract, constructorDecl]

theorem erc20CtorLocals_get_balanceOf (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "balanceOf" = none := by
  unfold erc20CtorLocals
  simp [erc20Contract, constructorDecl]

theorem erc20CtorLocals_get_totalSupply (initialSupply : Int) :
    (erc20CtorLocals initialSupply).get? "totalSupply" = none := by
  unfold erc20CtorLocals
  simp [erc20Contract, constructorDecl]

def erc20CtorBalancePostState (evm : EVM.State) (initialSupply : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (erc20BalanceOfSlot (.address evm.executionEnv.source)) initialSupply

def erc20CtorPostState (evm : EVM.State) (initialSupply : UInt256) : EVM.State :=
  Solm.EVM.storageStore (erc20CtorBalancePostState evm initialSupply)
    (erc20CtorBalancePostState evm initialSupply).executionEnv.codeOwner ⟨2⟩ initialSupply

theorem erc20CtorAssignBalance (evm : EVM.State) (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
      evm .storage (balanceOfRef sender) (.int initialSupply) =
        .ok ({ contract := erc20Contract, locals := erc20CtorLocals initialSupply },
          erc20CtorBalancePostState evm (EVM.word initialSupply.toNat)) := by
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := erc20CtorLocals_get_balanceOf initialSupply)
      (her := by
        simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, balanceOfRef, sender,
          envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
          pure, evalExpr?])
      (hty := by simp [storageTypeAt?, erc20Contract, erc20StorageDecls, uint256Storage,
        storageTypeStep?])
      (hloc := erc20Config_storage_balanceOf (.address evm.executionEnv.source))
  have hword :
      (EVM.word initialSupply.toNat).toNat = initialSupply.toNat :=
    constructorUInt256Word_toNat initialSupply h0 hlt
  have hint : Int.ofNat (EVM.word initialSupply.toNat).toNat = initialSupply := by
    calc
      Int.ofNat (EVM.word initialSupply.toNat).toNat = Int.ofNat initialSupply.toNat := by
        rw [hword]
      _ = initialSupply := by
        exact Int.toNat_of_nonneg h0
  conv_lhs => rw [← hint]
  rw [erc20StorageLocStore_uint256]
  rfl

theorem erc20CtorAssignTotalSupply (evm : EVM.State) (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
      evm .storage totalSupplyRef (.int initialSupply) =
        .ok ({ contract := erc20Contract, locals := erc20CtorLocals initialSupply },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
            (EVM.word initialSupply.toNat)) := by
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := erc20CtorLocals_get_totalSupply initialSupply)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, erc20Contract, erc20StorageDecls, uint256Storage])
      (hloc := erc20Config_storage_totalSupply)
  have hword :
      (EVM.word initialSupply.toNat).toNat = initialSupply.toNat :=
    constructorUInt256Word_toNat initialSupply h0 hlt
  have hint : Int.ofNat (EVM.word initialSupply.toNat).toNat = initialSupply := by
    calc
      Int.ofNat (EVM.word initialSupply.toNat).toNat = Int.ofNat initialSupply.toNat := by
        rw [hword]
      _ = initialSupply := by
        exact Int.toNat_of_nonneg h0
  conv_lhs => rw [← hint]
  rw [erc20StorageLocStore_uint256]

theorem erc20SolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (initialSupply : Int)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec erc20Config erc20Contract [.int initialSupply]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := erc20CtorLocals initialSupply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [erc20CtorLocals, erc20Contract, constructorDecl]
  · exact bodyReverts_nonPayable (cfg := erc20Config) (contract := erc20Contract)
      (locals := erc20CtorLocals initialSupply) hwv

theorem erc20SolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (initialSupply : Int)
    (h0 : 0 ≤ initialSupply)
    (hlt : initialSupply < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec erc20Config erc20Contract [.int initialSupply]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
        (erc20CtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.word initialSupply.toNat))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := erc20CtorLocals initialSupply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [erc20CtorLocals, erc20Contract, constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    let frame : Frame := { contract := erc20Contract, locals := erc20CtorLocals initialSupply }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := erc20CtorBalancePostState evm0 (EVM.word initialSupply.toNat)
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := erc20Config)
        (solm := frame) (evm := evm0) (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .int initialSupply)
        (by
          show evalExpr? erc20Config frame evm0 (.var "initialSupply") = .ok (.int initialSupply)
          unfold frame
          simp only [evalExpr?, erc20CtorLocals_get_initialSupply, EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact erc20CtorAssignBalance
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            initialSupply h0 hlt)
    · refine ExecBlock.consNormal ?_ ExecBlock.nil
      exact ExecStmt.assign (value := .int initialSupply)
        (by
          show evalExpr? erc20Config frame evm1 (.var "initialSupply") = .ok (.int initialSupply)
          unfold frame
          simp only [evalExpr?, erc20CtorLocals_get_initialSupply, EvalResult.ofOption])
        (by
          unfold evm1 frame
          simpa [erc20CtorPostState, storageStore_executionEnv] using
            erc20CtorAssignTotalSupply
              (erc20CtorBalancePostState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.word initialSupply.toNat))
              initialSupply h0 hlt)

theorem erc20ConstructorCorrect :
    constructorEquivalence erc20Config erc20Initcode erc20Contract erc20Bytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ
  rcases erc20Deployment_shape hdeploy with ⟨initialSupply, hargs, h0, hlt, hdeployed⟩
  subst args
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hcodeCtor : I.code = erc20CtorCode (EVM.word initialSupply.toNat) := by
      rw [hcode, hdeployed]
      unfold erc20CtorCode
      rfl
    have hrd := erc20InitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (EVM.word initialSupply.toNat) hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ_evm (erc20BalanceOfSlot (.address I.source))
              (EVM.word initialSupply.toNat))
            ⟨2⟩ (EVM.word initialSupply.toNat) :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (erc20SolmCtorExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          initialSupply h0 hlt hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_createdAccounts,
          initState]
      · simp only [erc20CtorPostState, erc20CtorBalancePostState, storageStore_accountMap,
          storageStore_executionEnv, initState]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ (EVM.word initialSupply.toNat)
          (accountMapEquiv_sstoreAccountMap I.codeOwner
            (erc20BalanceOfSlot (.address I.source)) (EVM.word initialSupply.toNat) hσ)
  · let tail := (EVM.Word.toBytesBE (EVM.word initialSupply.toNat)).toByteArray
    have hcodeTail : I.code = erc20Initcode ++ tail := by
      rw [hcode, hdeployed]
    have hrd := erc20InitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (erc20SolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          initialSupply hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

/-- The full contract equivalence combines constructor/initcode and runtime equivalence. -/
theorem erc20ContractCorrect :
    contractEquivalence erc20Config erc20Initcode erc20Bytecode erc20Contract :=
  contractEquivalence.intro erc20ConstructorCorrect erc20Correct

end ERC20
