import Examples.SimpleAuction.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction shared proof foundation

Phase 0 common facts for the one-level binary-search dispatcher.  Unlike Ballot, SimpleAuction has
a payable `bid()` entry, so the dispatcher prefix has no global callvalue guard.  The per-function
wrappers for the six non-payable entries perform their own callvalue checks.
-/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev simpleAuctionSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `simpleAuctionContract.transitions` order. -/
def simpleAuctionSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x19, 0x98, 0xae, 0xef]⟩  -- bid
  | 1 => ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩  -- withdraw
  | 2 => ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩  -- auctionEnd
  | 3 => ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩  -- beneficiary
  | 4 => ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩  -- auctionEndTime
  | 5 => ⟨#[0x91, 0xf9, 0x01, 0x57]⟩  -- highestBidder
  | _ => ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩  -- highestBid

/-- Low selector half in bytecode arm order. -/
def simpleAuctionLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x19, 0x98, 0xae, 0xef]⟩  -- bid
  | 1 => ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩  -- auctionEnd
  | _ => ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩  -- beneficiary

/-- High selector half in bytecode arm order. -/
def simpleAuctionHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩  -- withdraw
  | 1 => ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩  -- auctionEndTime
  | 2 => ⟨#[0x91, 0xf9, 0x01, 0x57]⟩  -- highestBidder
  | _ => ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩  -- highestBid

/-! ## Binary-search dispatcher constants -/

abbrev simpleAuctionSplitPc : UInt256 := ⟨18⟩
abbrev simpleAuctionHighFirstArmPc : UInt256 := ⟨29⟩
abbrev simpleAuctionLowJumpdestPc : UInt256 := ⟨76⟩
abbrev simpleAuctionLowFirstArmPc : UInt256 := ⟨77⟩

theorem simpleAuctionSplitWellFormed :
    selectorSplitWellFormed simpleAuctionBytecode simpleAuctionSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem simpleAuctionHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed simpleAuctionBytecode
      (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem simpleAuctionLowArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed simpleAuctionBytecode
      (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Shared scalar storage and return helpers -/

theorem simpleAuctionStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (simpleAuctionAddrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [simpleAuctionAddrLoc, addressOffset0Loc] using
    storageLocLoad_address_offset0 evm slot

theorem simpleAuctionStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (simpleAuctionUint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [simpleAuctionUint256Loc, uint256Loc] using storageLocLoad_uint256 evm slot

abbrev simpleAuctionRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem simpleAuctionSubRet32_toNat :
    (UInt256.sub simpleAuctionRetEnd ⟨128⟩).toNat = 32 := by
  decide

theorem simpleAuctionSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    simpleAuctionSelWord I = sel := by
  apply u256_inj
  dsimp [simpleAuctionSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem simpleAuctionLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc j))
        (simpleAuctionSelWord I) =
      if (simpleAuctionLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem simpleAuctionHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc j))
        (simpleAuctionSelWord I) =
      if (simpleAuctionHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem simpleAuctionLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (simpleAuctionLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc i))
        (simpleAuctionSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = simpleAuctionLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [simpleAuctionLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [simpleAuctionLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem simpleAuctionHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (simpleAuctionHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc i))
        (simpleAuctionSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = simpleAuctionHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [simpleAuctionHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [simpleAuctionHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem simpleAuctionPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (simpleAuctionLowSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat simpleAuctionBytecode simpleAuctionSplitPc)
      (simpleAuctionSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode simpleAuctionLowFirstArmPc :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x19 0x98 0xae 0xef _ (by decide)
        (by simpa [simpleAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc 1) :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x2a 0x24 0xf4 0x6c _ (by decide)
        (by simpa [simpleAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc 2) :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x38 0xaf 0x3e 0xed _ (by decide)
        (by simpa [simpleAuctionLowSelBytes] using hsel)
    rw [hword]; decide

theorem simpleAuctionPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (simpleAuctionHighSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat simpleAuctionBytecode simpleAuctionSplitPc)
      (simpleAuctionSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : simpleAuctionSelWord I = armSelNat simpleAuctionBytecode simpleAuctionSplitPc :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x3c 0xcf 0xd6 0x0b _ (by decide)
        (by simpa [simpleAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc 1) :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x4b 0x44 0x9c 0xba _ (by decide)
        (by simpa [simpleAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc 2) :=
      simpleAuctionSelWord_eq_of_beq I hsz 0x91 0xf9 0x01 0x57 _ (by decide)
        (by simpa [simpleAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : simpleAuctionSelWord I =
        armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc 3) :=
      simpleAuctionSelWord_eq_of_beq I hsz 0xd5 0x7b 0xde 0x79 _ (by decide)
        (by simpa [simpleAuctionHighSelBytes] using hsel)
    rw [hword]; decide

/-! ## Payable dispatcher prefix and routing -/

theorem simpleAuctionPayablePrologueRD {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = simpleAuctionBytecode) :
    RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 3 18 := by
  exact evm_run (RD.initState hcode) with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by decide) ]

theorem simpleAuctionReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = simpleAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) simpleAuctionSplitPc
        [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (bodyPc := (⟨5⟩ : UInt256)) (selLoadTgt := (⟨110⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    (simpleAuctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide)
    (by simp)
  refine ⟨k3, C3, ?_⟩
  simpa [simpleAuctionSelWord] using h3

theorem simpleAuctionReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = simpleAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat simpleAuctionBytecode simpleAuctionSplitPc)
      (simpleAuctionSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc i))
        (simpleAuctionSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J simpleAuctionBytecode 0).contains bodyPC = true)
    (hbody : armTgt simpleAuctionBytecode
        (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hsplit⟩ := simpleAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hfirst := by
    simpa [simpleAuctionHighFirstArmPc, simpleAuctionSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto hsplit simpleAuctionSplitWellFormed hpivot (by simp)
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => by
      simpa [simpleAuctionHighFirstArmPc, simpleAuctionSplitPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
        simpleAuctionHighArmsWellFormed j (le_trans hj hi))
    (fun j hj => by
      simpa [simpleAuctionHighFirstArmPc, simpleAuctionSplitPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using heq0 j hj)
    (by
      simpa [simpleAuctionHighFirstArmPc, simpleAuctionSplitPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using htake)
    (by
      change (D_J simpleAuctionBytecode 0).contains
        (armTgt simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc i)) = true
      rw [hbody]
      exact hjd)
    (by
      change armTgt simpleAuctionBytecode
        (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc i) = bodyPC
      exact hbody)
    (by simp)

theorem simpleAuctionReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = simpleAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat simpleAuctionBytecode simpleAuctionSplitPc)
      (simpleAuctionSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc i))
        (simpleAuctionSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J simpleAuctionBytecode 0).contains bodyPC = true)
    (hbody : armTgt simpleAuctionBytecode
        (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hsplit⟩ := simpleAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hlowJd := by
    simpa [simpleAuctionLowJumpdestPc, simpleAuctionSplitPc, armTgt, pushAt,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitTakenAuto hsplit simpleAuctionSplitWellFormed hpivot (by jump_dest) (by simp)
  have hfirst := by
    simpa [simpleAuctionLowFirstArmPc, simpleAuctionLowJumpdestPc] using
      hlowJd.jumpdest (by decide) (by simp)
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => by
      simpa [simpleAuctionLowFirstArmPc, simpleAuctionLowJumpdestPc, simpleAuctionSplitPc,
        armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
        simpleAuctionLowArmsWellFormed j (le_trans hj hi))
    (fun j hj => by
      simpa [simpleAuctionLowFirstArmPc, simpleAuctionLowJumpdestPc, simpleAuctionSplitPc,
        armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using heq0 j hj)
    (by
      simpa [simpleAuctionLowFirstArmPc, simpleAuctionLowJumpdestPc, simpleAuctionSplitPc,
        armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using htake)
    (by
      change (D_J simpleAuctionBytecode 0).contains
        (armTgt simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc i)) = true
      rw [hbody]
      exact hjd)
    (by
      change armTgt simpleAuctionBytecode
        (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc i) = bodyPC
      exact hbody)
    (by simp)

/-! ## Shared dispatcher revert paths -/

theorem simpleAuctionDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg simpleAuctionContract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [bidTransition, withdrawTransition, auctionEndTransition, beneficiaryGetter,
      auctionEndTimeGetter, highestBidderGetter, highestBidGetter] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, simpleAuctionBidSelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionWithdrawSelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionBeneficiarySelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionAuctionEndTimeSelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionHighestBidderSelectorBytes]; rfl
    · rw [selectorOf, simpleAuctionHighestBidSelectorBytes]; rfl) h

theorem simpleAuctionDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 7 → (simpleAuctionSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg simpleAuctionContract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [simpleAuctionContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, simpleAuctionBeneficiarySelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, simpleAuctionAuctionEndTimeSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, simpleAuctionHighestBidderSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, simpleAuctionHighestBidSelectorBytes]
    simpa [simpleAuctionSelBytes] using hnm 6 (by omega)

theorem simpleAuctionX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = simpleAuctionBytecode) (hsz : I.calldata.size < 4) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcCalldataShortRevert
    (bodyPc := (⟨5⟩ : UInt256)) (rtgt := (⟨110⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    (simpleAuctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem simpleAuctionX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = simpleAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 7 → (simpleAuctionSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionLowFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have h := hnm 0 (by omega)
      have hf : (simpleAuctionLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionLowSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionLowArmEq I hsz 0 (by omega), hf]
      rfl
    · have h := hnm 2 (by omega)
      have hf : (simpleAuctionLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionLowSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionLowArmEq I hsz 1 (by omega), hf]
      rfl
    · have h := hnm 3 (by omega)
      have hf : (simpleAuctionLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionLowSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionLowArmEq I hsz 2 (by omega), hf]
      rfl
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat simpleAuctionBytecode
          (nthArmPc simpleAuctionBytecode simpleAuctionHighFirstArmPc j))
        (simpleAuctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have h := hnm 1 (by omega)
      have hf : (simpleAuctionHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionHighSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionHighArmEq I hsz 0 (by omega), hf]
      rfl
    · have h := hnm 4 (by omega)
      have hf : (simpleAuctionHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionHighSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionHighArmEq I hsz 1 (by omega), hf]
      rfl
    · have h := hnm 5 (by omega)
      have hf : (simpleAuctionHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionHighSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionHighArmEq I hsz 2 (by omega), hf]
      rfl
    · have h := hnm 6 (by omega)
      have hf : (simpleAuctionHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [simpleAuctionHighSelBytes, simpleAuctionSelBytes] using h
      rw [simpleAuctionHighArmEq I hsz 3 (by omega), hf]
      rfl
  obtain ⟨kS, CS, hsplit⟩ := simpleAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat simpleAuctionBytecode simpleAuctionSplitPc)
      (simpleAuctionSelWord I) = ⟨0⟩
  · have h29 := RD.selectorSplitNotTakenAuto hsplit simpleAuctionSplitWellFormed hpivot (by simp)
    have h73 := h29
      |>.selectorArmNotTakenAuto (simpleAuctionHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (simpleAuctionHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (simpleAuctionHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (simpleAuctionHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
    have h73' : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨73⟩
        [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [simpleAuctionHighFirstArmPc, simpleAuctionSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h73
    obtain ⟨_, _, h73rd⟩ := h73'
    exact h73rd.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h76 := RD.selectorSplitTakenAuto hsplit simpleAuctionSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h77 := h76.jumpdest (by decide) (by simp)
    have h110 := h77
      |>.selectorArmNotTakenAuto (simpleAuctionLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (simpleAuctionLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (simpleAuctionLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
    have h110' : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨110⟩
        [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22, ?_⟩
      simpa [simpleAuctionLowFirstArmPc, simpleAuctionLowJumpdestPc, simpleAuctionSplitPc,
        nthArmPc, selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc,
        selArmEqPc, selArmPush4Pc] using h110
    obtain ⟨_, _, h110rd⟩ := h110'
    have h111 := h110rd.jumpdest (by decide) (by simp)
    exact h111.revertStub (by decide) (by decide) (by decide) (by simp)

end SimpleAuction

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

theorem RD.simpleAuctionRoutineEncodeAddress {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD _root_.simpleAuctionBytecode ee g s0 ⟨174⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD _root_.simpleAuctionBytecode ee g s0 ⟨194⟩
      (SimpleAuction.simpleAuctionRetEnd :: ret :: R)
      (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact ⟨_, _, by simpa using rd⟩

theorem RD.simpleAuctionReturnOneWord194 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD _root_.simpleAuctionBytecode ee g s0 ⟨194⟩
        (SimpleAuction.simpleAuctionRetEnd :: R) (solcReturnMem val) (UInt256.ofNat 5)
        rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret _root_.simpleAuctionBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          SimpleAuction.simpleAuctionSubRet32_toNat]
        simpa using solcReturnMem_read128 val)
      (by evm_ov)]

end Reasoning.Reach
