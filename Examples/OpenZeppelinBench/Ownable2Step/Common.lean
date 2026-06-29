import Examples.OpenZeppelinBench.Ownable2Step.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## Ownable2StepBench-wide dispatch, ABI, and return helpers -/

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev ownable2StepSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- Ownable2StepBench's five selector arms begin at pc 30 (`renounceOwnership`). -/
abbrev ownable2StepFirstArmPc : UInt256 := ⟨30⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- Ownable2StepBench function selectors, indexed in bytecode dispatch-arm order. -/
def ownable2StepSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x71, 0x50, 0x18, 0xa6]⟩  -- renounceOwnership()
  | 1 => ⟨#[0x79, 0xba, 0x50, 0x97]⟩  -- acceptOwnership()
  | 2 => ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩  -- owner()
  | 3 => ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩  -- pendingOwner()
  | _ => ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩  -- transferOwnership(address)

/-- All five selector arms decode as `DUP1; PUSH4; EQ; PUSH2; JUMPI`. -/
theorem ownable2StepArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed ownable2StepBenchBytecode
      (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Arm `j`'s selector equality agrees with the calldata byte comparison. -/
theorem ownable2StepArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc j))
        (ownable2StepSelWord I)
      = if (ownable2StepSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- Selector identification for the linear dispatcher. -/
theorem ownable2StepMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ownable2StepSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc j))
        (ownable2StepSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc i))
        (ownable2StepSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = ownable2StepSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [ownable2StepArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [ownable2StepArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- Standard solc prologue/guards/selector-load, then linear dispatch to a body entry. -/
theorem ownable2StepReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi4 : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = ownable2StepBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc j))
        (ownable2StepSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc i))
        (ownable2StepSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J ownable2StepBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt ownable2StepBenchBytecode
        (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc i) = bodyPC) :
    ∃ k C, RD ownable2StepBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := ownable2StepFirstArmPc) (bodyPC := bodyPC) (i := i)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => ownable2StepArmsWellFormed j (le_trans hj hi4)) heq0 htake
    hjd hbody

/-! ## Shared dispatch and revert traces -/

theorem ownable2StepDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [acceptOwnershipTransition, ownerTransition, pendingOwnerTransition, renounceOwnershipTransition,
      transferOwnershipTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, acceptOwnershipSelectorBytes]; rfl
    · rw [selectorOf, ownerSelectorBytes]; rfl
    · rw [selectorOf, pendingOwnerSelectorBytes]; rfl
    · rw [selectorOf, renounceOwnershipSelectorBytes]; rfl
    · rw [selectorOf, transferOwnershipSelectorBytes]; rfl) h

theorem ownable2StepDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 5 → (ownable2StepSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, acceptOwnershipSelectorBytes]; simpa [ownable2StepSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, ownerSelectorBytes]; simpa [ownable2StepSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, pendingOwnerSelectorBytes]; simpa [ownable2StepSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, renounceOwnershipSelectorBytes]; simpa [ownable2StepSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, transferOwnershipSelectorBytes]; simpa [ownable2StepSelBytes] using hnm 4 (by omega)

theorem ownable2StepBodyReverts_nonPayable
    (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem ownable2StepX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ownable2StepBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt ownable2StepBenchBytecode)
    (opC := solcGuardTgtOp ownable2StepBenchBytecode)
    (wC := solcGuardTgtWidth ownable2StepBenchBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ownable2StepX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ownable2StepBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt ownable2StepBenchBytecode)
    (opC := solcGuardTgtOp ownable2StepBenchBytecode)
    (wC := solcGuardTgtWidth ownable2StepBenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc ownable2StepBenchBytecode)
    (rtgt := solcCalldataRevertTgt ownable2StepBenchBytecode)
    (opR := solcCalldataRevertTgtOp ownable2StepBenchBytecode)
    (wR := solcCalldataRevertTgtWidth ownable2StepBenchBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem ownable2StepX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ownable2StepBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 5 → (ownable2StepSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat ownable2StepBenchBytecode
          (nthArmPc ownable2StepBenchBytecode ownable2StepFirstArmPc j))
        (ownable2StepSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [ownable2StepArmEq I hsz j hj]
    rw [hnm j hj]
    rfl
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt ownable2StepBenchBytecode)
    (opC := solcGuardTgtOp ownable2StepBenchBytecode)
    (wC := solcGuardTgtWidth ownable2StepBenchBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc ownable2StepBenchBytecode)
    (selLoadTgt := solcCalldataRevertTgt ownable2StepBenchBytecode)
    (opR := solcCalldataRevertTgtOp ownable2StepBenchBytecode)
    (wR := solcCalldataRevertTgtWidth ownable2StepBenchBytecode)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ :=
    solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  have h4 : RD ownable2StepBenchBytecode I g (initState cA gh bl σ σ₀ g A I)
      ownable2StepFirstArmPc [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k3 C3 := by
    simpa [ownable2StepFirstArmPc, ownable2StepSelWord, solcFirstArmPcFromPrefix,
      solcSelectorWord, solcSelectorLoadPc, solcCalldataJumpiPc, solcCalldataRevertPushPc,
      solcDispatchBodyPc] using h3
  have h5 := h4
    |>.selectorArmNotTakenAuto (ownable2StepArmsWellFormed 0 (by omega)) (heq0 0 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (ownable2StepArmsWellFormed 1 (by omega)) (heq0 1 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (ownable2StepArmsWellFormed 2 (by omega)) (heq0 2 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (ownable2StepArmsWellFormed 3 (by omega)) (heq0 3 (by omega))
        (by simp)
    |>.selectorArmNotTakenAuto (ownable2StepArmsWellFormed 4 (by omega)) (heq0 4 (by omega))
        (by simp)
  have h85 : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨85⟩ [ownable2StepSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨k3 + 5 + 5 + 5 + 5 + 5, C3 + 22 + 22 + 22 + 22 + 22, ?_⟩
    simpa [ownable2StepFirstArmPc, nthArmPc, selArmNextPc, armTgtWidth, armTgt,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h5
  obtain ⟨_, _, h85rd⟩ := h85
  exact evm_run h85rd with [
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem ownable2StepNonPayable {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ownable2StepX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (ownable2StepBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem ownable2StepShortRevert {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ownable2StepX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (ownable2StepDispatch_none_short hsz)

theorem ownable2StepNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 5 → (ownable2StepSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (ownable2StepX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (ownable2StepDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (ownable2StepX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (ownable2StepDispatch_none_short hshort)

/-! ## Address return helpers -/

def ownable2StepSetAddressWord (old addr : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask)) (UInt256.land addr solcAddrMask)

def ownable2StepSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem ownable2StepSourceWord_toNat (I : ExecutionEnv) :
    (ownable2StepSourceWord I).toNat = I.source.val := by
  unfold ownable2StepSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem ownable2StepSourceWord_canonical (I : ExecutionEnv) :
    (ownable2StepSourceWord I).toNat < EVM.addressModulus := by
  rw [ownable2StepSourceWord_toNat]
  exact I.source.isLt

theorem ownable2StepSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (ownable2StepSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [ownable2StepSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem ownable2StepMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = ownable2StepSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, ownable2StepSource_ofNat]

theorem ownable2StepWord_eq_of_maskedAddress_eq_source {w : UInt256} {I : ExecutionEnv}
    (h : AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source) :
    UInt256.land w solcAddrMask = ownable2StepSourceWord I := by
  apply u256_inj
  have hcanon := solcAddrMask_result_canonical w
  have hval := congrArg Fin.val h
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [ownable2StepSourceWord_toNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  exact hval

abbrev ownable2StepRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem ownable2StepSubRet32_toNat :
    (UInt256.sub ownable2StepRetEnd ⟨128⟩).toNat = 32 := by
  decide

/-! ## Shared Ownable unauthorized custom error -/

def ownable2StepUnauthorizedSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x118cdaa7⟩ : UInt256) ⟨224⟩

noncomputable def ownable2StepUnauthorizedMem (caller : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask caller)).write 0
    (solcReturnMem ownable2StepUnauthorizedSelector) 132 32

theorem ownable2StepUnauthorizedMem_size (caller : UInt256) :
    (ownable2StepUnauthorizedMem caller).size = 164 := by
  unfold ownable2StepUnauthorizedMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  rw [show ((solcReturnMem ownable2StepUnauthorizedSelector).extract (132 + 32) 160).size =
      0 by
    rw [ByteArray.size_extract, solcReturnMem_size]
    norm_num]
  omega

theorem ownable2StepUnauthorizedMem_read64 (caller : UInt256) :
    (ownable2StepUnauthorizedMem caller).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ownable2StepUnauthorizedMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
  exact solcReturnMem_read64 ownable2StepUnauthorizedSelector

theorem ownable2StepUnauthorizedMem_mload64 (caller : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (ownable2StepUnauthorizedMem caller).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((ownable2StepUnauthorizedMem caller).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [ownable2StepUnauthorizedMem_size]; decide) (by decide)
    (ownable2StepUnauthorizedMem_read64 caller)

end OpenZeppelinBench.Ownable2Step

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM

end Reasoning.Theory

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

def ownable2StepOnlyOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

/-- Ownable2StepBench's direct one-word address return tail at pc 119. -/
theorem RD.ownable2StepReturnAddress119 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ⟨119⟩
        (val :: R) solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    RDret _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val solcAddrMask)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSubRet32_toNat]
        simpa using solcReturnMem_read128 (UInt256.land val solcAddrMask))
      (by evm_ov) ]

set_option maxHeartbeats 1000000 in
theorem RD.ownable2StepOnlyOwnerPass {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ⟨387⟩
        (ret :: R) mem aw rdata (cA, σ) k C)
    (howner :
      UInt256.land (ownable2StepOnlyOwnerWord σ ee) solcAddrMask =
        _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee)
    (hret :
      (D_J _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode 0).contains ret =
        true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ret R
      mem aw rdata (cA, σ) k' C' := by
  have rd389 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd390₀⟩ := rd389.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd390⟩ : ∃ k' C',
      RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ⟨390⟩
        (ownable2StepOnlyOwnerWord σ ee :: ret :: R) mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [ownable2StepOnlyOwnerWord] using rd390₀⟩
  have rd401₀ := evm_run rd390 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (ownable2StepOnlyOwnerWord σ ee) =
        _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee := by
    rw [Reasoning.Theory.u256_land_comm, howner]
  have heq :
      UInt256.eq (UInt256.ofNat ee.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (ownable2StepOnlyOwnerWord σ ee)) = ⟨1⟩ := by
    change UInt256.eq (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee)
      (UInt256.land solcAddrMask (ownable2StepOnlyOwnerWord σ ee)) = ⟨1⟩
    rw [hmask, u256_eq_refl]
  have rd401 := rd401₀
  rw [heq] at rd401
  have rd200 := evm_run rd401 with [push2 ⟨200⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd200 with [jumpdest, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.ownable2StepOnlyOwnerRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ⟨387⟩
        (ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (howner :
      UInt256.land (ownable2StepOnlyOwnerWord σ ee) solcAddrMask ≠
        _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee)
    (hov : R.length + 8 ≤ 1024) :
    RDrev _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode g s0 := by
  have rd389 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd390₀⟩ := rd389.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd390⟩ : ∃ k' C',
      RD _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode ee g s0 ⟨390⟩
        (ownable2StepOnlyOwnerWord σ ee :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [ownable2StepOnlyOwnerWord] using rd390₀⟩
  have rd401₀ := evm_run rd390 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (ownable2StepOnlyOwnerWord σ ee) ≠
        _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee := by
    intro hmask
    exact howner (by
      rw [Reasoning.Theory.u256_land_comm] at hmask
      exact hmask)
  have hneq :
      UInt256.ofNat ee.source.val ≠
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (ownable2StepOnlyOwnerWord σ ee) := by
    change _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee ≠
      UInt256.land solcAddrMask (ownable2StepOnlyOwnerWord σ ee)
    exact fun h => hmask h.symm
  have heq :
      UInt256.eq (UInt256.ofNat ee.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (ownable2StepOnlyOwnerWord σ ee)) = ⟨0⟩ := by
    exact u256_eq_of_ne hneq
  have rd401 := rd401₀
  rw [heq] at rd401
  have rd405 := evm_run rd401 with [push2 ⟨200⟩, jumpiNT (by decide)]
  have rd418 := evm_run rd405 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x118cdaa7⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6
      (solcReturnMem _root_.OpenZeppelinBench.Ownable2Step.ownable2StepUnauthorizedSelector)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd423 := evm_run rd418 with [caller, push1 ⟨4⟩, dup3, add]
  have rd426 := evm_run rd423 with [
    raw mstore 3
      (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepUnauthorizedMem
        (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide]
        rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold _root_.OpenZeppelinBench.Ownable2Step.ownable2StepUnauthorizedMem
          _root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord
        rw [show UInt256.land solcAddrMask (UInt256.ofNat ee.source.val) =
            UInt256.ofNat ee.source.val by
          rw [Reasoning.Theory.u256_land_comm]
          exact solcAddrMask_clean
            (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord_canonical ee)])
      (by decide) (by evm_ov),
    push1 ⟨36⟩, add]
  have rd254 := evm_run rd426 with [push2 ⟨254⟩, jump (by jump_dest)]
  have rd262 := evm_run rd254 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepUnauthorizedMem_mload64
        (_root_.OpenZeppelinBench.Ownable2Step.ownable2StepSourceWord ee))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd262.rev 0 (by decide) mem_cost (by evm_ov)

end Reasoning.Reach
