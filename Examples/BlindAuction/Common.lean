import Examples.BlindAuction.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BlindAuction

/-!
# BlindAuction shared proof foundation

Phase 0 common facts for the optimizer-on one-level binary-search dispatcher.  The dispatcher itself
is payable: only the calldata-size guard runs before selector dispatch.  Non-payable checks live in
the individual body wrappers emitted by solc.
-/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev blindAuctionSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `blindAuctionContract.transitions` order. -/
def blindAuctionSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩  -- bid
  | 1 => ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩  -- reveal
  | 2 => ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩  -- withdraw
  | 3 => ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩  -- auctionEnd
  | 4 => ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩  -- beneficiary
  | 5 => ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩  -- biddingEnd
  | 6 => ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩  -- revealEnd
  | 7 => ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩  -- ended
  | 8 => ⟨#[0x91, 0xf9, 0x01, 0x57]⟩  -- highestBidder
  | 9 => ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩  -- highestBid
  | _ => ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩  -- bids

/-- Low selector half in bytecode arm order. -/
def blindAuctionLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩  -- bids
  | 1 => ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩  -- ended
  | 2 => ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩  -- auctionEnd
  | 3 => ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩  -- beneficiary
  | _ => ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩  -- withdraw

/-- High selector half in bytecode arm order. -/
def blindAuctionHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩  -- biddingEnd
  | 1 => ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩  -- reveal
  | 2 => ⟨#[0x91, 0xf9, 0x01, 0x57]⟩  -- highestBidder
  | 3 => ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩  -- bid
  | 4 => ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩  -- revealEnd
  | _ => ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩  -- highestBid

/-! ## Binary-search dispatcher constants -/

abbrev blindAuctionSplitPc : UInt256 := ⟨18⟩
abbrev blindAuctionHighFirstArmPc : UInt256 := ⟨29⟩
abbrev blindAuctionLowJumpdestPc : UInt256 := ⟨98⟩
abbrev blindAuctionLowFirstArmPc : UInt256 := ⟨99⟩

theorem blindAuctionSplitWellFormed :
    selectorSplitWellFormed blindAuctionBytecode blindAuctionSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem blindAuctionHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed blindAuctionBytecode
      (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem blindAuctionLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed blindAuctionBytecode
      (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem blindAuctionSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    blindAuctionSelWord I = sel := by
  apply u256_inj
  dsimp [blindAuctionSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem blindAuctionLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc j))
        (blindAuctionSelWord I) =
      if (blindAuctionLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem blindAuctionHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc j))
        (blindAuctionSelWord I) =
      if (blindAuctionHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem blindAuctionLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (blindAuctionLowSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc i))
        (blindAuctionSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = blindAuctionLowSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [blindAuctionLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [blindAuctionLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem blindAuctionHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 6)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (blindAuctionHighSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc i))
        (blindAuctionSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = blindAuctionHighSelBytes i :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [blindAuctionHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [blindAuctionHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem blindAuctionPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (blindAuctionLowSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat blindAuctionBytecode blindAuctionSplitPc)
      (blindAuctionSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode blindAuctionLowFirstArmPc :=
      blindAuctionSelWord_eq_of_beq I hsz 0x01 0x49 0x5c 0x1c _ (by decide)
        (by simpa [blindAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc 1) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x12 0xfa 0x6f 0xeb _ (by decide)
        (by simpa [blindAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc 2) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x2a 0x24 0xf4 0x6c _ (by decide)
        (by simpa [blindAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc 3) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x38 0xaf 0x3e 0xed _ (by decide)
        (by simpa [blindAuctionLowSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc 4) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x3c 0xcf 0xd6 0x0b _ (by decide)
        (by simpa [blindAuctionLowSelBytes] using hsel)
    rw [hword]; decide

theorem blindAuctionPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 6)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (blindAuctionHighSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat blindAuctionBytecode blindAuctionSplitPc)
      (blindAuctionSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : blindAuctionSelWord I = armSelNat blindAuctionBytecode blindAuctionSplitPc :=
      blindAuctionSelWord_eq_of_beq I hsz 0x42 0x3b 0x21 0x7f _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc 1) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x90 0x0f 0x08 0x0a _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc 2) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x91 0xf9 0x01 0x57 _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc 3) :=
      blindAuctionSelWord_eq_of_beq I hsz 0x95 0x7b 0xb1 0xe0 _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc 4) :=
      blindAuctionSelWord_eq_of_beq I hsz 0xa6 0xe6 0x64 0x77 _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide
  · have hword : blindAuctionSelWord I =
        armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc 5) :=
      blindAuctionSelWord_eq_of_beq I hsz 0xd5 0x7b 0xde 0x79 _ (by decide)
        (by simpa [blindAuctionHighSelBytes] using hsel)
    rw [hword]; decide

/-! ## Payable dispatcher prefix and routing -/

theorem blindAuctionPayablePrologueRD {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = blindAuctionBytecode) :
    RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 3 18 := by
  exact evm_run (RD.initState hcode) with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by decide) ]

theorem blindAuctionReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = blindAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) blindAuctionSplitPc
        [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (bodyPc := (⟨5⟩ : UInt256)) (selLoadTgt := (⟨154⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    (blindAuctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide)
    (by simp)
  refine ⟨k3, C3, ?_⟩
  simpa [blindAuctionSelWord] using h3

theorem blindAuctionReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = blindAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat blindAuctionBytecode blindAuctionSplitPc)
      (blindAuctionSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc i))
        (blindAuctionSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J blindAuctionBytecode 0).contains bodyPC = true)
    (hbody : armTgt blindAuctionBytecode
        (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := blindAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hfirstEx : ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I)
      blindAuctionHighFirstArmPc [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    simpa [blindAuctionHighFirstArmPc, blindAuctionSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto hsplit blindAuctionSplitWellFormed hpivot (by simp)
  obtain ⟨_, _, hfirst⟩ := hfirstEx
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => blindAuctionHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

theorem blindAuctionReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = blindAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat blindAuctionBytecode blindAuctionSplitPc)
      (blindAuctionSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc i))
        (blindAuctionSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J blindAuctionBytecode 0).contains bodyPC = true)
    (hbody : armTgt blindAuctionBytecode
        (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨kS, CS, hsplit⟩ := blindAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hlowJdEx : ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I)
      blindAuctionLowJumpdestPc [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kS + 5, CS + 22, ?_⟩
    simpa [blindAuctionLowJumpdestPc, blindAuctionSplitPc, armTgt, pushAt,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitTakenAuto hsplit blindAuctionSplitWellFormed hpivot (by jump_dest) (by simp)
  obtain ⟨kJd, CJd, hlowJd⟩ := hlowJdEx
  have hfirstEx : ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I)
      blindAuctionLowFirstArmPc [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨kJd + 1, CJd + 1, ?_⟩
    simpa [blindAuctionLowFirstArmPc, blindAuctionLowJumpdestPc] using
      hlowJd.jumpdest (by decide) (by simp)
  obtain ⟨_, _, hfirst⟩ := hfirstEx
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => blindAuctionLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ## Shared dispatcher revert paths -/

theorem blindAuctionDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg blindAuctionContract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter,
      highestBidderGetter, highestBidGetter, bidsGetter] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, blindAuctionBidSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionRevealSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionWithdrawSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionAuctionEndSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionBeneficiarySelectorBytes]; rfl
    · rw [selectorOf, blindAuctionBiddingEndSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionRevealEndSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionEndedSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionHighestBidderSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionHighestBidSelectorBytes]; rfl
    · rw [selectorOf, blindAuctionBidsSelectorBytes]; rfl) h

theorem blindAuctionDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 11 → (blindAuctionSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg blindAuctionContract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [blindAuctionContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, blindAuctionRevealSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, blindAuctionEndedSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, blindAuctionHighestBidderSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, blindAuctionHighestBidSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, blindAuctionBidsSelectorBytes]
    simpa [blindAuctionSelBytes] using hnm 10 (by omega)

theorem blindAuctionX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = blindAuctionBytecode) (hsz : I.calldata.size < 4) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcCalldataShortRevert
    (bodyPc := (⟨5⟩ : UInt256)) (rtgt := (⟨154⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    (blindAuctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem blindAuctionX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = blindAuctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 11 → (blindAuctionSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionLowFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (blindAuctionLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionLowSelBytes, blindAuctionSelBytes] using hnm 10 (by omega)
      rw [blindAuctionLowArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (blindAuctionLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionLowSelBytes, blindAuctionSelBytes] using hnm 7 (by omega)
      rw [blindAuctionLowArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (blindAuctionLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionLowSelBytes, blindAuctionSelBytes] using hnm 3 (by omega)
      rw [blindAuctionLowArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (blindAuctionLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionLowSelBytes, blindAuctionSelBytes] using hnm 4 (by omega)
      rw [blindAuctionLowArmEq I hsz 3 (by omega), hm]
      rfl
    · have hm : (blindAuctionLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionLowSelBytes, blindAuctionSelBytes] using hnm 2 (by omega)
      rw [blindAuctionLowArmEq I hsz 4 (by omega), hm]
      rfl
  have heqHigh0 : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat blindAuctionBytecode
          (nthArmPc blindAuctionBytecode blindAuctionHighFirstArmPc j))
        (blindAuctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (blindAuctionHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 5 (by omega)
      rw [blindAuctionHighArmEq I hsz 0 (by omega), hm]
      rfl
    · have hm : (blindAuctionHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 1 (by omega)
      rw [blindAuctionHighArmEq I hsz 1 (by omega), hm]
      rfl
    · have hm : (blindAuctionHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 8 (by omega)
      rw [blindAuctionHighArmEq I hsz 2 (by omega), hm]
      rfl
    · have hm : (blindAuctionHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 0 (by omega)
      rw [blindAuctionHighArmEq I hsz 3 (by omega), hm]
      rfl
    · have hm : (blindAuctionHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 6 (by omega)
      rw [blindAuctionHighArmEq I hsz 4 (by omega), hm]
      rfl
    · have hm : (blindAuctionHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [blindAuctionHighSelBytes, blindAuctionSelBytes] using hnm 9 (by omega)
      rw [blindAuctionHighArmEq I hsz 5 (by omega), hm]
      rfl
  obtain ⟨kS, CS, hsplit⟩ := blindAuctionReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat blindAuctionBytecode blindAuctionSplitPc)
      (blindAuctionSelWord I) = ⟨0⟩
  · have h29 := RD.selectorSplitNotTakenAuto hsplit blindAuctionSplitWellFormed hpivot (by simp)
    have h95 := h29
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 4 (by omega))
          (heqHigh0 4 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionHighArmsWellFormed 5 (by omega))
          (heqHigh0 5 (by omega)) (by simp)
    have h95' : ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨95⟩
        [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [blindAuctionHighFirstArmPc, blindAuctionSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h95
    obtain ⟨_, _, h95rd⟩ := h95'
    exact h95rd.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h98 := RD.selectorSplitTakenAuto hsplit blindAuctionSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h99 := h98.jumpdest (by decide) (by simp)
    have h154 := h99
      |>.selectorArmNotTakenAuto (blindAuctionLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionLowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (blindAuctionLowArmsWellFormed 4 (by omega))
          (heqLow0 4 (by omega)) (by simp)
    have h154' : ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨154⟩
        [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5 + 5,
        CS + 22 + 1 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [blindAuctionLowFirstArmPc, blindAuctionLowJumpdestPc, blindAuctionSplitPc,
        nthArmPc, selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc,
        selArmEqPc, selArmPush4Pc] using h154
    obtain ⟨_, _, h154rd⟩ := h154'
    have h155 := h154rd.jumpdest (by decide) (by simp)
    exact h155.revertStub (by decide) (by decide) (by decide) (by simp)

theorem blindAuctionShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (blindAuctionX_short (g := Sat256.ofUInt256 g) hcode hsz).reEquivNoDispatch hcode
    (blindAuctionDispatch_none_short hsz)

theorem blindAuctionNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hnm : ∀ i, i < 11 → (blindAuctionSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (blindAuctionX_noMatch (g := Sat256.ofUInt256 g) hcode hsz hsize hnm)
      |>.reEquivNoDispatch hcode (blindAuctionDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (blindAuctionX_short (g := Sat256.ofUInt256 g) hcode hshort).reEquivNoDispatch hcode
      (blindAuctionDispatch_none_short hshort)

end BlindAuction
