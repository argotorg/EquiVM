import Benchmarks.Auction.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.ExternalCall
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Solm.Equiv
import Mathlib.Tactic.IntervalCases

/-!
# Auction common proof helpers

Contract-local ABI selector and runtime-case helpers shared by the Auction proof files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

-- LIBRARY CANDIDATE: generalizes Reasoning.Memory.mstoreCost_of_stack to MLOAD.
theorem auctionMloadCost_of_stack {s : State} {aw off : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MLOAD = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

-- LIBRARY CANDIDATE: generalizes log memory-cost helpers for LOGn opcodes.
theorem auctionLog2Cost_of_stack {s : State} {aw off sz topic1 topic2 : UInt256}
    {t : List UInt256} {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: sz :: topic1 :: topic2 :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat sz.toNat)) - Cₘ aw =
      mcost) :
    memoryExpansionCost s .LOG2 = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  have hsz : s.machineState.stack[1]! = sz := by
    rw [hstk]
    rfl
  rw [htop, hsz, haw]
  exact hcost

-- LIBRARY CANDIDATE: missing Reasoning.Reach.RD.log2, parallel to RD.log1/log3/log4.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat <
          memoryExpansionCost s .LOG2 +
            (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]
        exact hcode
      · simp only [stLog2]
        rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]
        exact hmem
      · simp only [stLog2]
        rw [haw, hawout]
      · simp only [stLog2]
        exact hrdata
      · simp only [stLog2]
        exact hacc
      · simp only [stLog2]
        exact hee
      · simp only [stLog2]
        exact hworld

abbrev RuntimeCase
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader}
    {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    (g : UInt256) : Prop :=
  runtimeEquivalenceFor auctionConfig Auction.auctionContract cA gh bl
    σ_evm σ_solm σ₀ g A I

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- The selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev auctionSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

def auctionSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

def auctionPausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionSlotWord ⟨51⟩ σ I) ⟨255⟩

def auctionPausedSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def auctionPausedSetFalseWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def auctionPausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨51⟩ (auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I))

def auctionUnpausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨51⟩ (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I))

def auctionPausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (auctionPausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))

def auctionUnpausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
    (auctionPausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))

def auctionOnlyOwnerStringWord : UInt256 :=
  ⟨0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572⟩

def auctionSetOwnerWord (old newOwner : UInt256) : UInt256 :=
  setAddressOffset0Word old newOwner

def auctionSetOwnerPostMap (σ : AccountMap) (I : ExecutionEnv) (newOwner : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨151⟩
    (auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ I) newOwner)

def auctionSetOwnerPostState (evm : EVM.State) (newOwner : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
    (auctionSetOwnerWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) newOwner)

def auctionOwnershipTransferredTopic : UInt256 :=
  ⟨0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0⟩

theorem auctionSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (b0 b1 b2 b3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [b0, b1, b2, b3] : ℕ) = sel.toNat)
    (hbeq : ((⟨#[b0, b1, b2, b3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    auctionSelWord I = sel := by
  apply u256_inj
  dsimp [auctionSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata b0 b1 b2 b3 hsz).mp hbeq, hsel]

/-- NounsAuctionHouse selectors in the runtime dispatch-arm order. -/
def auctionSelBytes : Nat → ByteArray
  | 0 => ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩  -- duration()
  | 1 => ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩  -- nouns()
  | 2 => ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩  -- setMinBidIncrementPercentage(uint8)
  | 3 => ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩  -- unpause()
  | 4 => ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩  -- weth()
  | 5 => ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩  -- paused()
  | 6 => ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩  -- createBid(uint256)
  | 7 => ⟨#[0x71, 0x20, 0x33, 0x4b]⟩  -- setTimeBuffer(uint256)
  | 8 => ⟨#[0x71, 0x50, 0x18, 0xa6]⟩  -- renounceOwnership()
  | 9 => ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩  -- auction()
  | 10 => ⟨#[0x84, 0x56, 0xcb, 0x59]⟩ -- pause()
  | 11 => ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩ -- initialize(address,address,uint256,uint256,uint8,uint256)
  | 12 => ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ -- owner()
  | 13 => ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩ -- settleAuction()
  | 14 => ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩ -- minBidIncrementPercentage()
  | 15 => ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩ -- setReservePrice(uint256)
  | 16 => ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩ -- reservePrice()
  | 17 => ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩ -- timeBuffer()
  | 18 => ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩ -- settleCurrentAndCreateNewAuction()
  | _ => ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩  -- transferOwnership(address)

/-! ## Dispatcher constants and selector groups -/

abbrev auctionSplitPc : UInt256 := ⟨18⟩
abbrev auctionUpperSplitPc : UInt256 := ⟨29⟩
abbrev auctionUpperMidFirstArmPc : UInt256 := ⟨40⟩
abbrev auctionUpperLowFirstArmPc : UInt256 := ⟨99⟩
abbrev auctionLowerSplitPc : UInt256 := ⟨158⟩
abbrev auctionLowerMidFirstArmPc : UInt256 := ⟨169⟩
abbrev auctionLowerLowFirstArmPc : UInt256 := ⟨228⟩

def auctionUpperMidSelBytes : Nat → ByteArray
  | 0 => ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩ -- setReservePrice(uint256)
  | 1 => ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩ -- reservePrice()
  | 2 => ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩ -- timeBuffer()
  | 3 => ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩ -- settleCurrentAndCreateNewAuction()
  | _ => ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩  -- transferOwnership(address)

def auctionUpperLowSelBytes : Nat → ByteArray
  | 0 => ⟨#[0x84, 0x56, 0xcb, 0x59]⟩ -- pause()
  | 1 => ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩ -- setReservePrice(uint256)
  | 2 => ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ -- owner()
  | 3 => ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩ -- settleCurrentAndCreateNewAuction()
  | _ => ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩  -- minBidIncrementPercentage()

def auctionLowerMidSelBytes : Nat → ByteArray
  | 0 => ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ -- paused()
  | 1 => ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩ -- createBid(uint256)
  | 2 => ⟨#[0x71, 0x20, 0x33, 0x4b]⟩ -- setTimeBuffer(uint256)
  | 3 => ⟨#[0x71, 0x50, 0x18, 0xa6]⟩ -- renounceOwnership()
  | _ => ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩  -- auction()

def auctionLowerLowSelBytes : Nat → ByteArray
  | 0 => ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩ -- duration()
  | 1 => ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩ -- nouns()
  | 2 => ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩ -- setMinBidIncrementPercentage(uint8)
  | 3 => ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ -- unpause()
  | _ => ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩  -- weth()

theorem auctionSplitWellFormed :
    selectorSplitWellFormed auctionBytecode auctionSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionUpperSplitWellFormed :
    selectorSplitWellFormed auctionBytecode auctionUpperSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionLowerSplitWellFormed :
    selectorSplitWellFormed auctionBytecode auctionLowerSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionUpperMidArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed auctionBytecode
      (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionUpperLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed auctionBytecode
      (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionLowerMidArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed auctionBytecode
      (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionLowerLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed auctionBytecode
      (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem auctionUpperMidArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j))
        (auctionSelWord I) =
      if (auctionUpperMidSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem auctionUpperLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j))
        (auctionSelWord I) =
      if (auctionUpperLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem auctionLowerMidArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j))
        (auctionSelWord I) =
      if (auctionLowerMidSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem auctionLowerLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 5) :
    UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j))
        (auctionSelWord I) =
      if (auctionLowerLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem auctionDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg Auction.auctionContract cd = none := by
  rw [dispatchMsg_eq_dispatchList Auction.auctionContract cd (by rfl)]
  change dispatchList
    [ initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter ] cd =
    none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | rw [selectorOf, initializeSelectorBytes]; rfl
      | rw [selectorOf, createBidSelectorBytes]; rfl
      | rw [selectorOf, settleAndCreateSelectorBytes]; rfl
      | rw [selectorOf, settleAuctionSelectorBytes]; rfl
      | rw [selectorOf, pauseSelectorBytes]; rfl
      | rw [selectorOf, unpauseSelectorBytes]; rfl
      | rw [selectorOf, setTimeBufferSelectorBytes]; rfl
      | rw [selectorOf, setReservePriceSelectorBytes]; rfl
      | rw [selectorOf, setMinBidIncSelectorBytes]; rfl
      | rw [selectorOf, transferOwnershipSelectorBytes]; rfl
      | rw [selectorOf, renounceOwnershipSelectorBytes]; rfl
      | rw [selectorOf, ownerSelectorBytes]; rfl
      | rw [selectorOf, pausedSelectorBytes]; rfl
      | rw [selectorOf, nounsSelectorBytes]; rfl
      | rw [selectorOf, wethSelectorBytes]; rfl
      | rw [selectorOf, timeBufferSelectorBytes]; rfl
      | rw [selectorOf, reservePriceSelectorBytes]; rfl
      | rw [selectorOf, minBidIncSelectorBytes]; rfl
      | rw [selectorOf, durationSelectorBytes]; rfl
      | rw [selectorOf, auctionGetterSelectorBytes]; rfl) h

theorem auctionDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 20 → (auctionSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg Auction.auctionContract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [Auction.auctionContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, initializeSelectorBytes]
    simpa [auctionSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, createBidSelectorBytes]
    simpa [auctionSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, settleAndCreateSelectorBytes]
    simpa [auctionSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, settleAuctionSelectorBytes]
    simpa [auctionSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, pauseSelectorBytes]
    simpa [auctionSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, unpauseSelectorBytes]
    simpa [auctionSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, setTimeBufferSelectorBytes]
    simpa [auctionSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, setReservePriceSelectorBytes]
    simpa [auctionSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, setMinBidIncSelectorBytes]
    simpa [auctionSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, transferOwnershipSelectorBytes]
    simpa [auctionSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, renounceOwnershipSelectorBytes]
    simpa [auctionSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, ownerSelectorBytes]
    simpa [auctionSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, pausedSelectorBytes]
    simpa [auctionSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, nounsSelectorBytes]
    simpa [auctionSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, wethSelectorBytes]
    simpa [auctionSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, timeBufferSelectorBytes]
    simpa [auctionSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, reservePriceSelectorBytes]
    simpa [auctionSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, minBidIncSelectorBytes]
    simpa [auctionSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, durationSelectorBytes]
    simpa [auctionSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, auctionGetterSelectorBytes]
    simpa [auctionSelBytes] using hnm 9 (by omega)

/-! ## ABI decode helpers -/

-- GENERALIZES Reasoning.ABI.decodeScalarWord_uint256_ok by parameterizing uint width.
theorem auctionDecodeScalarWord_uint8_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWord? uint8 bytes start =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  simp only [uint8, uint8Int, decodeScalarWord?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_neg (show ¬ ((8 : ℕ) = 0) from by decide)]
  rw [if_pos (by simpa [EVM.twoPow] using hcanon)]
  rfl

-- GENERALIZES Reasoning.ABI.decodeScalarWord_uint256_none_short by parameterizing uint width.
theorem auctionDecodeScalarWord_uint8_none_noncanon {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWord? uint8 bytes start = none := by
  simp only [uint8, uint8Int, decodeScalarWord?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp only
  rw [if_neg (show ¬ ((8 : ℕ) = 0) from by decide)]
  rw [if_neg (by simpa [EVM.twoPow] using hnc)]

-- GENERALIZES Reasoning.ABI.decodeScalarWord_uint256_none_short by parameterizing uint width.
theorem auctionDecodeScalarWord_uint8_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? uint8 bytes start = none := by
  simp only [uint8, uint8Int, decodeScalarWord?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_neg hshort]

-- GENERALIZES Reasoning.ABI.decodeScalarWords_uint256_ok by parameterizing uint width.
theorem auctionDecodeScalarWords_uint8_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [uint8] bytes 0 =
      some [.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  simp only [decodeScalarWords?]
  rw [auctionDecodeScalarWord_uint8_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  rfl

-- GENERALIZES Reasoning.ABI.decodeScalarWords_uint256_none_short by parameterizing uint width.
theorem auctionDecodeScalarWords_uint8_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [uint8] bytes 0 = none := by
  simp only [decodeScalarWords?]
  rw [auctionDecodeScalarWord_uint8_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

-- GENERALIZES Reasoning.ABI.decodeScalarWords_uint256_none_short by parameterizing uint width.
theorem auctionDecodeScalarWords_uint8_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [uint8] bytes 0 = none := by
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  rw [auctionDecodeScalarWord_uint8_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

-- GENERALIZES Reasoning.ABI.decodeCalldata_uint256_ok by parameterizing uint width.
theorem auctionDecodeCalldata_uint8_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.twoPow 8) :
    decodeCalldata [x] [uint8] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [uint8]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_uint8_ok (bytes := cd.toList.drop 4) htake4 (by
    simpa [hword4] using hcanon)]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

-- GENERALIZES Reasoning.ABI.decodeCalldata_address_none_noncanon for uintN canonicality.
theorem auctionDecodeCalldata_uint8_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.twoPow 8) :
    decodeCalldata [x] [uint8] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [uint8]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_uint8_none_noncanon (bytes := cd.toList.drop 4) htake4 (by
    simpa [hword4] using hnc)]

-- GENERALIZES Reasoning.ABI.decodeCalldata_uint256_none_short by parameterizing uint width.
theorem auctionDecodeCalldata_uint8_none_short {cd : ByteArray} {x : Solm.Ident}
    (hshort : cd.size < 36) :
    decodeCalldata [x] [uint8] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [uint8]) (cd := cd)
    (by decide)]
  by_cases hsz4 : cd.size < 4
  · rw [if_pos (by rw [htlen]; omega : cd.toList.length < 4)]
  · rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    rw [auctionDecodeScalarWords_uint8_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

-- GENERALIZES Reasoning.ABI.decodeCalldata_uint256_none_huge by parameterizing uint width.
theorem auctionDecodeCalldata_uint8_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [uint8] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [uint8]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

/-! ## Getter source helpers -/

theorem auctionStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionUint256Loc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [auctionUint256Loc, uint256Loc, uint256Int] using storageLocLoad_uint256 evm slot

theorem auctionStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (auctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [auctionUint256Loc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm slot val

def auctionUint8Loc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .int uint8Int }

def auctionSetUint8Offset0Word (old val : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) val

-- GENERALIZES Reasoning.Storage.packedSetTrueNat_lt_size by parameterizing the low byte.
theorem auctionPackedSetByteNat_lt_size (old val : UInt256) (hval : val.toNat < 256) :
    val.toNat + 256 * (old.toNat / 256) < UInt256.size := by
  have hq : old.toNat / 256 < 2 ^ 248 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 256 * 2 ^ 248 = (2 : Nat) ^ 256 by norm_num [Nat.pow_add]]
    exact old.val.isLt
  have hvle : val.toNat ≤ 255 := by omega
  have hqle : old.toNat / 256 ≤ 2 ^ 248 - 1 := Nat.le_pred_of_lt hq
  have hmul : 256 * (old.toNat / 256) ≤ 256 * (2 ^ 248 - 1) :=
    Nat.mul_le_mul_left 256 hqle
  norm_num [UInt256.size] at hmul ⊢
  omega

-- GENERALIZES Reasoning.Storage.packedSetTrueWord_toNat by parameterizing the low byte.
theorem auctionPackedSetByteWord_toNat (old val : UInt256) (hval : val.toNat < 256) :
    (auctionSetUint8Offset0Word old val).toNat = val.toNat + 256 * (old.toNat / 256) := by
  unfold auctionSetUint8Offset0Word
  rw [u256_lor_toNat, u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hland_lt : Nat.land old.toNat (2 ^ 256 - 2 ^ 8) < UInt256.size := by
    rw [natLandClearLow8 old.toNat (by exact old.val.isLt)]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLandClearLow8 old.toNat (by exact old.val.isLt)]
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (old.toNat / 256) 256]
  rw [nat_lor_comm]
  rw [show 256 * (old.toNat / 256) = (old.toNat / 256) * 2 ^ 8 by ring]
  rw [nat_lor_shift_add val.toNat (old.toNat / 256) 8 (by simpa using hval)]
  rw [show (old.toNat / 256) * 2 ^ 8 = 256 * (old.toNat / 256) by ring]
  rw [Nat.mod_eq_of_lt (auctionPackedSetByteNat_lt_size old val hval)]

theorem auctionLand255_eq_self_of_uint8 (w : UInt256) (h : w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ = w := by
  apply u256_inj
  rw [u256_land_toNat]
  have h255 : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by decide
  rw [h255, nat_land_mask_eq_mod]
  rw [show w.toNat % 2 ^ 8 = w.toNat by exact Nat.mod_eq_of_lt h]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem auctionLand255_ne_self_of_not_uint8 (w : UInt256)
    (h : ¬ w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ ≠ w := by
  intro heq
  apply h
  have hto := congrArg UInt256.toNat heq
  rw [u256_land_toNat] at hto
  have h255 : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by decide
  rw [h255, nat_land_mask_eq_mod] at hto
  have hmodLt : w.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  have hsize : 2 ^ 8 < UInt256.size := by native_decide
  have hmodSize : w.toNat % 2 ^ 8 < UInt256.size := lt_trans hmodLt hsize
  rw [Nat.mod_eq_of_lt hmodSize] at hto
  have hle : 2 ^ 8 ≤ w.toNat := by
    have hle' : EVM.twoPow 8 ≤ w.toNat := Nat.le_of_not_gt h
    rwa [show EVM.twoPow 8 = 2 ^ 8 from by decide] at hle'
  have hlt : w.toNat % 2 ^ 8 < w.toNat := lt_of_lt_of_le hmodLt hle
  omega

theorem auctionStorageLocLoad_uint8 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionUint8Loc slot) =
      .int (Int.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).toNat) := by
  simpa [auctionUint8Loc, uint8Int] using
    storageLocLoad_uint_offset0 (evm := evm) (slot := slot) (size := ⟨1, by decide⟩)
      (width := ⟨8, by decide⟩) (hbound := by decide) (by decide)

-- LIBRARY CANDIDATE: packed unsigned integer store at byte offset 0.
theorem auctionStorageLocStore_uint8_offset0 (evm : EVM.State) (slot val : UInt256)
    (hval : val.toNat < 256) :
    storageLocStore evm (auctionUint8Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (auctionSetUint8Offset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord auctionUint8Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (auctionSetUint8Offset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen : ((EVM.Word.toBytesLEWithSizeProof val).1.take 1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
    norm_num
  rw [hlen]
  rw [show 256 ^ 1 = 256 by norm_num]
  rw [show val.toNat % 256 = val.toNat by exact Nat.mod_eq_of_lt hval]
  exact (auctionPackedSetByteWord_toNat
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val hval).symm

theorem auctionStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addressOffset0Loc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa using storageLocLoad_address_offset0 evm slot

theorem auctionStorageLocStore_address_offset0 (evm : EVM.State) (slot val : UInt256)
    (hcanon : val.toNat < EVM.addressModulus) :
    storageLocStore evm (auctionAddrLoc slot) (.address (AccountAddress.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  simpa [auctionAddrLoc] using storageLocStore_address_offset0 evm slot val hcanon

theorem auctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolOffset0Loc slot) =
      wordToElem .bool
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa using storageLocLoad_bool_offset0 evm slot

theorem auctionStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool false := by
  simpa using storageLocLoad_bool_offset0_false evm slot hzero

theorem auctionStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolOffset0Loc slot) = .bool true := by
  simpa using storageLocLoad_bool_offset0_true evm slot hnz

-- GENERALIZES Reasoning.Storage.storageLocLoad_bool_offset0 by parameterizing the byte offset.
theorem auctionStorageLocLoad_bool_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) :
    storageLocLoad evm (auctionBoolLocAt slot offset) =
      wordToElem .bool
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.ofNat (256 ^ offset.val))) ⟨255⟩) := by
  simp [storageLocLoad, auctionBoolLocAt]
  congr
  simpa [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val 1
      (by omega) (by decide)

-- GENERALIZES Reasoning.Storage.storageLocLoad_bool_offset0_false by parameterizing the byte offset.
theorem auctionStorageLocLoad_bool_offset_false (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32)
    (hzero : UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val))) ⟨255⟩ = ⟨0⟩) :
    storageLocLoad evm (auctionBoolLocAt slot offset) = .bool false := by
  rw [auctionStorageLocLoad_bool_offset]
  rw [hzero]
  simp [wordToElem]

-- GENERALIZES Reasoning.Storage.storageLocLoad_bool_offset0_true by parameterizing the byte offset.
theorem auctionStorageLocLoad_bool_offset_true (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32)
    (hnz : UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val))) ⟨255⟩ ≠ ⟨0⟩) :
    storageLocLoad evm (auctionBoolLocAt slot offset) = .bool true := by
  rw [auctionStorageLocLoad_bool_offset]
  simp [wordToElem]
  intro h
  apply hnz
  apply u256_inj
  exact congrArg Fin.val h

def auctionSetBoolOffset1TrueWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 256 + 256 + 65536 * (old.toNat / 65536))

def auctionSetBoolOffset1FalseWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 256 + 65536 * (old.toNat / 65536))

-- LIBRARY CANDIDATE: packed bool true store at byte offset 1.
theorem auctionSetBoolOffset1TrueNat_lt_size (old : UInt256) :
    old.toNat % 256 + 256 + 65536 * (old.toNat / 65536) < UInt256.size := by
  have hq : old.toNat / 65536 < 2 ^ 240 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 65536 * 2 ^ 240 = (2 : Nat) ^ 256 by norm_num [Nat.pow_add]]
    exact old.val.isLt
  have hqle : old.toNat / 65536 ≤ 2 ^ 240 - 1 := Nat.le_pred_of_lt hq
  have hmul : 65536 * (old.toNat / 65536) ≤ 65536 * (2 ^ 240 - 1) :=
    Nat.mul_le_mul_left 65536 hqle
  have hlow : old.toNat % 256 ≤ 255 := Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  norm_num [UInt256.size] at hmul ⊢
  omega

-- LIBRARY CANDIDATE: packed bool false store at byte offset 1.
theorem auctionSetBoolOffset1FalseNat_lt_size (old : UInt256) :
    old.toNat % 256 + 65536 * (old.toNat / 65536) < UInt256.size := by
  have hlt := auctionSetBoolOffset1TrueNat_lt_size old
  omega

-- LIBRARY CANDIDATE: `Nat.land` distributes over `Nat.lor`.
theorem natLand_lor (n a b : Nat) :
    Nat.land n (Nat.lor a b) = Nat.lor (Nat.land n a) (Nat.land n b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (a ||| b)).testBit i = ((n &&& a) ||| (n &&& b)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and]
  cases n.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

-- LIBRARY CANDIDATE: packed bool false store at byte offset 1 as a bitmask operation.
theorem auctionClearBoolOffset1Word_eq (old : UInt256) :
    UInt256.land old (UInt256.lnot ⟨65280⟩) = auctionSetBoolOffset1FalseWord old := by
  apply u256_inj
  unfold auctionSetBoolOffset1FalseWord
  rw [u256_land_toNat]
  have hlnot : (UInt256.lnot (⟨65280⟩ : UInt256)).toNat =
      Nat.lor (2 ^ 8 - 1) (2 ^ 256 - 2 ^ 16) := by
    native_decide
  rw [hlnot]
  have hmasklt : Nat.lor (2 ^ 8 - 1) (2 ^ 256 - 2 ^ 16) < UInt256.size := by
    native_decide
  have hland_lt :
      Nat.land old.toNat (Nat.lor (2 ^ 8 - 1) (2 ^ 256 - 2 ^ 16)) <
        UInt256.size :=
    lt_of_le_of_lt (nat_land_le_right _ _) hmasklt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLand_lor]
  rw [nat_land_mask_eq_mod old.toNat 8]
  rw [natLandClearLow old.toNat 16 (by norm_num) old.val.isLt]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 8) (old.toNat / 2 ^ 16) 16 (by
    have h : old.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt old.toNat (by norm_num)
    omega)]
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [show 2 ^ 16 = 65536 by norm_num]
  rw [show (old.toNat / 65536) * 65536 = 65536 * (old.toNat / 65536) by ring]
  rw [ulit_toNat' _ (auctionSetBoolOffset1FalseNat_lt_size old)]

-- LIBRARY CANDIDATE: the combined initializer flag write as a solc bitmask operation.
theorem auctionSetBoolOffset1TrueThenOffset0True_eq_mask (old : UInt256) :
    setBoolOffset0Word (auctionSetBoolOffset1TrueWord old) ⟨1⟩ =
      UInt256.lor (UInt256.land old (UInt256.lnot ⟨65535⟩)) ⟨257⟩ := by
  apply u256_inj
  unfold setBoolOffset0Word auctionSetBoolOffset1TrueWord
  rw [u256_lor_toNat, u256_land_toNat]
  have hiszero : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  rw [hiszero]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  rw [ulit_toNat' _ (auctionSetBoolOffset1TrueNat_lt_size old)]
  have hlnot255 : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot255]
  have hval_lt : old.toNat % 256 + 256 + 65536 * (old.toNat / 65536) < UInt256.size :=
    auctionSetBoolOffset1TrueNat_lt_size old
  have hland_lt :
      Nat.land (old.toNat % 256 + 256 + 65536 * (old.toNat / 65536))
          (2 ^ 256 - 2 ^ 8) <
        UInt256.size := by
    have hcomm := nat_land_comm
      (old.toNat % 256 + 256 + 65536 * (old.toNat / 65536)) (2 ^ 256 - 2 ^ 8)
    rw [hcomm]
    exact lt_of_le_of_lt (nat_land_le_right _ _) hval_lt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLandClearLow8 _ hval_lt]
  rw [show 2 ^ 8 = 256 by norm_num]
  have hdiv :
      (old.toNat % 256 + 256 + 65536 * (old.toNat / 65536)) / 256 =
        1 + 256 * (old.toNat / 65536) := by
    have hlow : old.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega
  rw [hdiv]
  rw [nat_lor_comm]
  rw [show (1 + 256 * (old.toNat / 65536)) * 256 =
      (1 + 256 * (old.toNat / 65536)) * 2 ^ 8 by norm_num]
  rw [nat_lor_shift_add 1 (1 + 256 * (old.toNat / 65536)) 8 (by norm_num)]
  rw [show 1 + (1 + 256 * (old.toNat / 65536)) * 2 ^ 8 =
      257 + 65536 * (old.toNat / 65536) by ring]
  rw [u256_lor_toNat, u256_land_toNat]
  have hlnot65535 : (UInt256.lnot (⟨65535⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 16 := by
    native_decide
  rw [hlnot65535]
  have hland2_lt : Nat.land old.toNat (2 ^ 256 - 2 ^ 16) < UInt256.size := by
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by native_decide)
  rw [Nat.mod_eq_of_lt hland2_lt]
  rw [natLandClearLow old.toNat 16 (by norm_num) old.val.isLt]
  rw [show 2 ^ 16 = 65536 by norm_num]
  rw [show (⟨257⟩ : UInt256).toNat = 257 by decide]
  rw [nat_lor_comm]
  rw [show old.toNat / 65536 * 65536 = (old.toNat / 65536) * 2 ^ 16 by norm_num]
  rw [nat_lor_shift_add 257 (old.toNat / 65536) 16 (by norm_num)]
  rw [show (old.toNat / 65536) * 2 ^ 16 = 65536 * (old.toNat / 65536) by ring]

-- LIBRARY CANDIDATE: packed bool true store at byte offset 1.
theorem auctionStorageLocStore_bool_true_offset1 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 1) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (auctionSetBoolOffset1TrueWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt auctionSetBoolOffset1TrueWord
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (1 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((1 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 256 +
          256 + 65536 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat /
            65536))).toNat
  rw [show (1 : Fin 32).val = 1 from rfl, show (1 : Fin 33).val = 1 from rfl]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1 = [1] by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  rw [hlen1]
  simp [fromBytes']
  rw [ulit_toNat' _ (auctionSetBoolOffset1TrueNat_lt_size
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))]

-- LIBRARY CANDIDATE: packed bool false store at byte offset 1.
theorem auctionStorageLocStore_bool_false_offset1 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 1) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (auctionSetBoolOffset1FalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt auctionSetBoolOffset1FalseWord
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (1 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((1 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 256 +
          65536 * ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat /
            65536))).toNat
  rw [show (1 : Fin 32).val = 1 from rfl, show (1 : Fin 33).val = 1 from rfl]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 = [0] by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  rw [hlen1]
  simp [fromBytes']
  rw [ulit_toNat' _ (auctionSetBoolOffset1FalseNat_lt_size
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))]

-- LIBRARY CANDIDATE: ABI scalar bool value encoding for packed storage words.
theorem abiBoolWordEncoding (w : UInt256) :
    encodeABIValue? (.elem .bool) (wordToElem .bool (UInt256.land w ⟨255⟩)) =
      some (EVM.Word.toBytesBE
        (UInt256.isZero (UInt256.isZero (UInt256.land w ⟨255⟩)))) := by
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simp [wordToElem, hz, hnorm, encodeABIValue?, encodeABIWord?, Bool.toUInt256_false]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]
  · have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land w ⟨255⟩) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simp [wordToElem, hval, hiz, hnorm, encodeABIValue?, encodeABIWord?, Bool.toUInt256_true]
    rw [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl]

theorem auctionStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩)) := by
  simpa using storageLocStore_bool_true_offset0 evm slot

theorem auctionStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolOffset0Loc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩))) := by
  simpa using storageLocStore_bool_false_offset0 evm slot

theorem auctionUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm ref =
      .ok er)
    (hty : storageTypeAt? auctionContract.storage er = some (.elem (.int uint256Int)))
    (hloc : auctionConfig.storage.layout er = fun _ => some (auctionUint256Loc slot)) :
    ExecTransitionBody auctionConfig auctionContract evm locals [nonpayable, .return [(.storage ref)]]
      (.returned { contract := auctionContract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := auctionConfig) (contract := auctionContract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (auctionStorageLocLoad_uint256 evm slot))

theorem auctionUint8GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm ref =
      .ok er)
    (hty : storageTypeAt? auctionContract.storage er = some (.elem (.int uint8Int)))
    (hloc : auctionConfig.storage.layout er = fun _ => some (auctionUint8Loc slot)) :
    ExecTransitionBody auctionConfig auctionContract evm locals [nonpayable, .return [(.storage ref)]]
      (.returned { contract := auctionContract, locals := locals } evm
        (some [(.int (Int.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := auctionConfig) (contract := auctionContract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (auctionStorageLocLoad_uint8 evm slot))

theorem auctionAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm ref =
      .ok er)
    (hty : storageTypeAt? auctionContract.storage er = some (.elem .address))
    (hloc : auctionConfig.storage.layout er = fun _ => some (addressOffset0Loc slot)) :
    ExecTransitionBody auctionConfig auctionContract evm locals [nonpayable, .return [(.storage ref)]]
      (.returned { contract := auctionContract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := auctionConfig) (contract := auctionContract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (auctionStorageLocLoad_address_offset0 evm slot))

theorem auctionBoolGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm ref =
      .ok er)
    (hty : storageTypeAt? auctionContract.storage er = some (.elem .bool))
    (hloc : auctionConfig.storage.layout er = fun _ => some (boolOffset0Loc slot)) :
    ExecTransitionBody auctionConfig auctionContract evm locals [nonpayable, .return [(.storage ref)]]
      (.returned { contract := auctionContract, locals := locals } evm
        (some [wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩)])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := auctionConfig) (contract := auctionContract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (auctionStorageLocLoad_bool_offset0 evm slot))

/-! ## Owner/source-address helpers -/

def auctionSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem auctionSourceWord_toNat (I : ExecutionEnv) :
    (auctionSourceWord I).toNat = I.source.val := by
  unfold auctionSourceWord
  exact UInt256.toNat_ofNat_of_lt (by
    exact lt_of_lt_of_le I.source.isLt (by decide))

theorem auctionSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (auctionSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [auctionSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem auctionSourceWord_canonical (I : ExecutionEnv) :
    (auctionSourceWord I).toNat < EVM.addressModulus := by
  rw [auctionSourceWord_toNat]
  exact I.source.isLt

theorem auctionMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = auctionSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, auctionSource_ofNat]

theorem auctionWord_eq_of_maskedAddress_eq_source {w : UInt256} {I : ExecutionEnv}
    (h : AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source) :
    UInt256.land w solcAddrMask = auctionSourceWord I := by
  apply u256_inj
  have hcanon := solcAddrMask_result_canonical w
  have hval := congrArg Fin.val h
  unfold AccountAddress.ofNat at hval
  rw [Fin.val_ofNat] at hval
  rw [auctionSourceWord_toNat]
  rw [Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)] at hval
  exact hval

noncomputable def auctionEventMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0 solcFreePtrMem 128 32

theorem auctionEventMem_size (I : ExecutionEnv) : (auctionEventMem I).size = 160 := by
  simpa [auctionEventMem, solcReturnMem] using solcReturnMem_size (auctionSourceWord I)

theorem auctionEventMem_read64 (I : ExecutionEnv) :
    (auctionEventMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [auctionEventMem, solcReturnMem] using solcReturnMem_read64 (auctionSourceWord I)

theorem auctionEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEventMem I).size ∨
        (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionEventMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) =
      (⟨128⟩ : UInt256) := by
  exact mloadFreePtrValue (by rw [auctionEventMem_size]; decide) (by decide)
    (auctionEventMem_read64 I)

/-! ## Dispatcher reachability -/

theorem auctionPayablePrologueRD {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) :
    RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 3 18 := by
  exact evm_run (RD.initState hcode) with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by decide) ]

theorem auctionReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) auctionSplitPc
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (bodyPc := (⟨5⟩ : UInt256)) (selLoadTgt := (⟨283⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    (auctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide)
    (by simp)
  exact ⟨k3, C3, by simpa [auctionSelWord] using h3⟩

theorem auctionX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) (hsz : I.calldata.size < 4) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run
    (auctionPayablePrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode) with [
    push1 ⟨4⟩,
    calldatasize,
    lt,
    push2 ⟨283⟩,
    jumpiT (lt_four_ne_zero_of_lt hsz) (by jump_dest),
    jumpdest,
    push0,
    dup1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 20 → (auctionSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqUpperMid0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j))
        (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (auctionUpperMidSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperMidSelBytes, auctionSelBytes] using hnm 15 (by omega)
      rw [auctionUpperMidArmEq I hsz 0 (by omega), hm]; rfl
    · have hm : (auctionUpperMidSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperMidSelBytes, auctionSelBytes] using hnm 16 (by omega)
      rw [auctionUpperMidArmEq I hsz 1 (by omega), hm]; rfl
    · have hm : (auctionUpperMidSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperMidSelBytes, auctionSelBytes] using hnm 17 (by omega)
      rw [auctionUpperMidArmEq I hsz 2 (by omega), hm]; rfl
    · have hm : (auctionUpperMidSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperMidSelBytes, auctionSelBytes] using hnm 18 (by omega)
      rw [auctionUpperMidArmEq I hsz 3 (by omega), hm]; rfl
    · have hm : (auctionUpperMidSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperMidSelBytes, auctionSelBytes] using hnm 19 (by omega)
      rw [auctionUpperMidArmEq I hsz 4 (by omega), hm]; rfl
  have heqUpperLow0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j))
        (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (auctionUpperLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperLowSelBytes, auctionSelBytes] using hnm 10 (by omega)
      rw [auctionUpperLowArmEq I hsz 0 (by omega), hm]; rfl
    · have hm : (auctionUpperLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperLowSelBytes, auctionSelBytes] using hnm 11 (by omega)
      rw [auctionUpperLowArmEq I hsz 1 (by omega), hm]; rfl
    · have hm : (auctionUpperLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperLowSelBytes, auctionSelBytes] using hnm 12 (by omega)
      rw [auctionUpperLowArmEq I hsz 2 (by omega), hm]; rfl
    · have hm : (auctionUpperLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperLowSelBytes, auctionSelBytes] using hnm 13 (by omega)
      rw [auctionUpperLowArmEq I hsz 3 (by omega), hm]; rfl
    · have hm : (auctionUpperLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [auctionUpperLowSelBytes, auctionSelBytes] using hnm 14 (by omega)
      rw [auctionUpperLowArmEq I hsz 4 (by omega), hm]; rfl
  have heqLowerMid0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j))
        (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (auctionLowerMidSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerMidSelBytes, auctionSelBytes] using hnm 5 (by omega)
      rw [auctionLowerMidArmEq I hsz 0 (by omega), hm]; rfl
    · have hm : (auctionLowerMidSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerMidSelBytes, auctionSelBytes] using hnm 6 (by omega)
      rw [auctionLowerMidArmEq I hsz 1 (by omega), hm]; rfl
    · have hm : (auctionLowerMidSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerMidSelBytes, auctionSelBytes] using hnm 7 (by omega)
      rw [auctionLowerMidArmEq I hsz 2 (by omega), hm]; rfl
    · have hm : (auctionLowerMidSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerMidSelBytes, auctionSelBytes] using hnm 8 (by omega)
      rw [auctionLowerMidArmEq I hsz 3 (by omega), hm]; rfl
    · have hm : (auctionLowerMidSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerMidSelBytes, auctionSelBytes] using hnm 9 (by omega)
      rw [auctionLowerMidArmEq I hsz 4 (by omega), hm]; rfl
  have heqLowerLow0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat auctionBytecode
          (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j))
        (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · have hm : (auctionLowerLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerLowSelBytes, auctionSelBytes] using hnm 0 (by omega)
      rw [auctionLowerLowArmEq I hsz 0 (by omega), hm]; rfl
    · have hm : (auctionLowerLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerLowSelBytes, auctionSelBytes] using hnm 1 (by omega)
      rw [auctionLowerLowArmEq I hsz 1 (by omega), hm]; rfl
    · have hm : (auctionLowerLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerLowSelBytes, auctionSelBytes] using hnm 2 (by omega)
      rw [auctionLowerLowArmEq I hsz 2 (by omega), hm]; rfl
    · have hm : (auctionLowerLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerLowSelBytes, auctionSelBytes] using hnm 3 (by omega)
      rw [auctionLowerLowArmEq I hsz 3 (by omega), hm]; rfl
    · have hm : (auctionLowerLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [auctionLowerLowSelBytes, auctionSelBytes] using hnm 4 (by omega)
      rw [auctionLowerLowArmEq I hsz 4 (by omega), hm]; rfl
  obtain ⟨kS, CS, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  by_cases hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc)
      (auctionSelWord I) = ⟨0⟩
  · have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
    by_cases hupper : UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc)
        (auctionSelWord I) = ⟨0⟩
    · have h40 := RD.selectorSplitNotTakenAuto h29 auctionUpperSplitWellFormed hupper (by simp)
      have h95 := h40
        |>.selectorArmNotTakenAuto (auctionUpperMidArmsWellFormed 0 (by omega))
            (heqUpperMid0 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperMidArmsWellFormed 1 (by omega))
            (heqUpperMid0 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperMidArmsWellFormed 2 (by omega))
            (heqUpperMid0 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperMidArmsWellFormed 3 (by omega))
            (heqUpperMid0 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperMidArmsWellFormed 4 (by omega))
            (heqUpperMid0 4 (by omega)) (by simp)
      have h95' : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨95⟩
          [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine Exists.intro (kS + 5 + 5 + 5 + 5 + 5 + 5 + 5) ?_
        refine Exists.intro (CS + 22 + 22 + 22 + 22 + 22 + 22 + 22) ?_
        simpa [auctionUpperMidFirstArmPc, auctionUpperSplitPc, auctionSplitPc, nthArmPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using h95
      obtain ⟨_, _, h95rd⟩ := h95'
      exact evm_run h95rd with [push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]
    · have h98 := RD.selectorSplitTakenAuto h29 auctionUpperSplitWellFormed hupper
        (by jump_dest) (by simp)
      have h99 := h98.jumpdest (by decide) (by simp)
      have h154 := h99
        |>.selectorArmNotTakenAuto (auctionUpperLowArmsWellFormed 0 (by omega))
            (heqUpperLow0 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperLowArmsWellFormed 1 (by omega))
            (heqUpperLow0 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperLowArmsWellFormed 2 (by omega))
            (heqUpperLow0 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperLowArmsWellFormed 3 (by omega))
            (heqUpperLow0 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionUpperLowArmsWellFormed 4 (by omega))
            (heqUpperLow0 4 (by omega)) (by simp)
      have h154' : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨154⟩
          [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine Exists.intro (kS + 5 + 5 + 1 + 5 + 5 + 5 + 5 + 5) ?_
        refine Exists.intro (CS + 22 + 22 + 1 + 22 + 22 + 22 + 22 + 22) ?_
        simpa [auctionUpperLowFirstArmPc, auctionUpperSplitPc, auctionSplitPc, nthArmPc,
          selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using h154
      obtain ⟨_, _, h154rd⟩ := h154'
      exact evm_run h154rd with [push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]
  · have h157 := RD.selectorSplitTakenAuto hsplit auctionSplitWellFormed hroot
      (by jump_dest) (by simp)
    have h158 := h157.jumpdest (by decide) (by simp)
    by_cases hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc)
        (auctionSelWord I) = ⟨0⟩
    · have h169 := RD.selectorSplitNotTakenAuto h158 auctionLowerSplitWellFormed hlower (by simp)
      have h224 := h169
        |>.selectorArmNotTakenAuto (auctionLowerMidArmsWellFormed 0 (by omega))
            (heqLowerMid0 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerMidArmsWellFormed 1 (by omega))
            (heqLowerMid0 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerMidArmsWellFormed 2 (by omega))
            (heqLowerMid0 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerMidArmsWellFormed 3 (by omega))
            (heqLowerMid0 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerMidArmsWellFormed 4 (by omega))
            (heqLowerMid0 4 (by omega)) (by simp)
      have h224' : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨224⟩
          [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine Exists.intro (kS + 5 + 1 + 5 + 5 + 5 + 5 + 5 + 5) ?_
        refine Exists.intro (CS + 22 + 1 + 22 + 22 + 22 + 22 + 22 + 22) ?_
        simpa [auctionLowerMidFirstArmPc, auctionLowerSplitPc, auctionSplitPc, nthArmPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using h224
      obtain ⟨_, _, h224rd⟩ := h224'
      exact evm_run h224rd with [push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]
    · have h227 := RD.selectorSplitTakenAuto h158 auctionLowerSplitWellFormed hlower
        (by jump_dest) (by simp)
      have h228 := h227.jumpdest (by decide) (by simp)
      have h283 := h228
        |>.selectorArmNotTakenAuto (auctionLowerLowArmsWellFormed 0 (by omega))
            (heqLowerLow0 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerLowArmsWellFormed 1 (by omega))
            (heqLowerLow0 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerLowArmsWellFormed 2 (by omega))
            (heqLowerLow0 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerLowArmsWellFormed 3 (by omega))
            (heqLowerLow0 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (auctionLowerLowArmsWellFormed 4 (by omega))
            (heqLowerLow0 4 (by omega)) (by simp)
      have h283' : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨283⟩
          [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
        refine Exists.intro (kS + 5 + 1 + 5 + 1 + 5 + 5 + 5 + 5 + 5) ?_
        refine Exists.intro (CS + 22 + 1 + 22 + 1 + 22 + 22 + 22 + 22 + 22) ?_
        simpa [auctionLowerLowFirstArmPc, auctionLowerSplitPc, auctionSplitPc, nthArmPc,
          selArmNextPc, armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using h283
      obtain ⟨_, _, h283rd⟩ := h283'
      exact evm_run h283rd with [
        jumpdest, push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

-- LIBRARY CANDIDATE: general UInt256 subtraction nonzero from word inequality.
theorem u256_sub_ne_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.sub a b ≠ ⟨0⟩ := by
  intro hsub
  apply h
  apply u256_inj
  have hv := congrArg UInt256.toNat hsub
  simp at hv
  by_cases hle : b.toNat ≤ a.toNat
  · have hs : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
    rw [hs] at hv
    omega
  · have hlt : a.toNat < b.toNat := by omega
    have hs : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
      usub_toNat_underflow hlt
    rw [hs] at hv
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega

-- LIBRARY CANDIDATE: relate EVM MLOAD-style padded reads at zero to ByteArray.readBytes.
theorem readWithPadding_zero_32_eq_readBytes (cd : ByteArray) :
    cd.readWithPadding 0 32 = ByteArray.readBytes cd 0 32 := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [readBytes32_toList]
  by_cases hzero : cd.size = 0
  · have hdata : cd.data.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Array.length_toList]
      exact hzero
    simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, hzero, hdata,
      byteArray_zeroes_toList]
    native_decide
  · by_cases hlt : cd.size < 32
    · rw [← byteArray_toList_eq (cd.readWithPadding 0 32)]
      rw [readWithPadding_zero_toList_of_size_lt32 cd hzero hlt]
      rw [byteArray_toList_eq]
      rw [List.take_of_length_le]
      · simp only [min_eq_right (Nat.le_of_lt hlt)]
      · rw [Array.length_toList]
        exact Nat.le_of_lt hlt
    · have hge : 32 ≤ cd.size := by omega
      have hnotempty : cd ≠ ByteArray.empty := by
        intro hempty
        apply hzero
        rw [hempty]
        rfl
      unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
      simp [hge, hnotempty, ByteArray.size_extract, byteArray_zeroes_toList]

-- LIBRARY CANDIDATE: value-parametric variant of
-- Reasoning.Theory.typedCallViaEVM_callMade_accountMapEquiv.
theorem typedCallViaEVM_value_callMade_accountMapEquiv {cfg : Config}
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {targetWord valueWord : UInt256} {name : Ident} {args : List Value}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool} {value : ℤ}
    (hvalue : valueWord = EVM.wordOfInt value)
    (hbalance : valueWord ≤ (evm_evm.accountMap.find? evm_evm.executionEnv.codeOwner
      |>.elim ⟨0⟩ (·.balance)))
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hSubstate : evm_solm.substate = evm_evm.substate)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z,
          { evm_solm with
              accountMap := σ'_solm,
              substate := A'_solm,
              createdAccounts := cA' },
          out) callPerm ∧
      accountMapEquiv σ' σ'_solm := by
  have hcallE : typedCallViaEVM cfg evm_evm tgt name value args
      (z, { evm_evm with accountMap := σ', substate := A', createdAccounts := cA' }, out)
      callPerm := by
    refine ⟨mem.readWithPadding inOff.toNat inSize.toNat, hcd, ?_⟩
    have hΘ' := hΘ
    rw [accountAddress_roundtrip, ← htgt] at hΘ'
    exact callViaEVM.callMade (perm := callPerm) hvalue ⟨callGas, A_in, hΘ'⟩ rfl
      hbalance hdepth
  simpa using
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evm_solm) hcallE hAccounts hOriginalAccounts hCreated hGenesis hBlocks
      hSubstate hEnv

theorem auctionNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hnm : ∀ i, i < 20 → ¬ selIs I (auctionSelBytes i))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  by_cases hsz : 4 ≤ I.calldata.size
  · have hnmBool : ∀ i, i < 20 → (auctionSelBytes i == I.calldata.extract 0 4) = false := by
      intro i hi
      cases hbeq : (auctionSelBytes i == I.calldata.extract 0 4) with
      | false => rfl
      | true => exact False.elim ((_hnm i hi) hbeq)
    exact (auctionX_noMatch (g := Sat256.ofUInt256 g) _hcode hsz _hsize hnmBool)
      |>.reEquivNoDispatch _hcode (auctionDispatch_none_nomatch hnmBool)
  · have hshort : I.calldata.size < 4 := by omega
    exact (auctionX_short (g := Sat256.ofUInt256 g) _hcode hshort)
      |>.reEquivNoDispatch _hcode (auctionDispatch_none_short hshort)

end Auction
