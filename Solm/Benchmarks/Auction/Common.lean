import Solm.Benchmarks.Auction.Trusted
import Solm.Reasoning.Dispatch
import EVMReasoning.Solc
import Solm.Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

abbrev Entry := Fin 20

abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

def entryBytes (i : Entry) : ByteArray :=
  match i.val with
  | 0 => ⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩
  | 1 => ⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩
  | 2 => ⟨#[0x36, 0xeb, 0xdb, 0x38]⟩
  | 3 => ⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩
  | 4 => ⟨#[0x3f, 0xc8, 0xce, 0xf3]⟩
  | 5 => ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩
  | 6 => ⟨#[0x65, 0x9d, 0xd2, 0xb4]⟩
  | 7 => ⟨#[0x71, 0x20, 0x33, 0x4b]⟩
  | 8 => ⟨#[0x71, 0x50, 0x18, 0xa6]⟩
  | 9 => ⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩
  | 10 => ⟨#[0x84, 0x56, 0xcb, 0x59]⟩
  | 11 => ⟨#[0x87, 0xf4, 0x9f, 0x54]⟩
  | 12 => ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
  | 13 => ⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩
  | 14 => ⟨#[0xb2, 0x96, 0x02, 0x4d]⟩
  | 15 => ⟨#[0xce, 0x9c, 0x7c, 0x0d]⟩
  | 16 => ⟨#[0xdb, 0x2e, 0x1e, 0xed]⟩
  | 17 => ⟨#[0xec, 0x91, 0xf2, 0xa4]⟩
  | 18 => ⟨#[0xf2, 0x5e, 0xff, 0xfc]⟩
  | _ => ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩

def entryWord (i : Entry) : UInt256 :=
  match i.val with
  | 0 => ⟨0x0fb5a6b4⟩
  | 1 => ⟨0x2de45f18⟩
  | 2 => ⟨0x36ebdb38⟩
  | 3 => ⟨0x3f4ba83a⟩
  | 4 => ⟨0x3fc8cef3⟩
  | 5 => ⟨0x5c975abb⟩
  | 6 => ⟨0x659dd2b4⟩
  | 7 => ⟨0x7120334b⟩
  | 8 => ⟨0x715018a6⟩
  | 9 => ⟨0x7d9f6db5⟩
  | 10 => ⟨0x8456cb59⟩
  | 11 => ⟨0x87f49f54⟩
  | 12 => ⟨0x8da5cb5b⟩
  | 13 => ⟨0xa4d0a17e⟩
  | 14 => ⟨0xb296024d⟩
  | 15 => ⟨0xce9c7c0d⟩
  | 16 => ⟨0xdb2e1eed⟩
  | 17 => ⟨0xec91f2a4⟩
  | 18 => ⟨0xf25efffc⟩
  | _ => ⟨0xf2fde38b⟩

def entryPc (i : Entry) : UInt256 :=
  match i.val with
  | 0 => ⟨287⟩
  | 1 => ⟨327⟩
  | 2 => ⟨382⟩
  | 3 => ⟨415⟩
  | 4 => ⟨435⟩
  | 5 => ⟨466⟩
  | 6 => ⟨500⟩
  | 7 => ⟨519⟩
  | 8 => ⟨550⟩
  | 9 => ⟨570⟩
  | 10 => ⟨685⟩
  | 11 => ⟨705⟩
  | 12 => ⟨736⟩
  | 13 => ⟨765⟩
  | 14 => ⟨785⟩
  | 15 => ⟨828⟩
  | 16 => ⟨859⟩
  | 17 => ⟨880⟩
  | 18 => ⟨901⟩
  | _ => ⟨921⟩

def entryTransition (i : Entry) : TransitionDecl :=
  match i.val with
  | 0 => durationGetter
  | 1 => nounsGetter
  | 2 => setMinBidIncTransition
  | 3 => unpauseTransition
  | 4 => wethGetter
  | 5 => pausedGetter
  | 6 => createBidTransition
  | 7 => setTimeBufferTransition
  | 8 => renounceOwnershipTransition
  | 9 => auctionGetter
  | 10 => pauseTransition
  | 11 => initializeTransition
  | 12 => ownerGetter
  | 13 => settleAuctionTransition
  | 14 => minBidIncGetter
  | 15 => setReservePriceTransition
  | 16 => reservePriceGetter
  | 17 => timeBufferGetter
  | 18 => settleAndCreateTransition
  | _ => transferOwnershipTransition

theorem entryBytes_size : ∀ i : Entry, (entryBytes i).size = 4 := by
  native_decide

theorem entryWord_eq {I : ExecutionEnv} (i : Entry) (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (entryBytes i)) : solcSelectorWord I = entryWord i := by
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    exact solcSelectorWord_eq_of_beq I hsz _ _ _ _ _ (by simp only [entryWord]; decide) hsel

theorem entrySelector (i : Entry) : selectorOf (entryTransition i) = entryBytes i := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact durationSelectorBytes
  · exact nounsSelectorBytes
  · exact setMinBidIncrementPercentageSelectorBytes
  · exact unpauseSelectorBytes
  · exact wethSelectorBytes
  · exact pausedSelectorBytes
  · exact createBidSelectorBytes
  · exact setTimeBufferSelectorBytes
  · exact renounceOwnershipSelectorBytes
  · exact auctionSelectorBytes
  · exact pauseSelectorBytes
  · exact initializeSelectorBytes
  · exact ownerSelectorBytes
  · exact settleAuctionSelectorBytes
  · exact minBidIncrementPercentageSelectorBytes
  · exact setReservePriceSelectorBytes
  · exact reservePriceSelectorBytes
  · exact timeBufferSelectorBytes
  · exact settleCurrentAndCreateNewAuctionSelectorBytes
  · exact transferOwnershipSelectorBytes

theorem transitionCovered (t : TransitionDecl) (ht : t ∈ auctionContract.transitions) :
    ∃ i : Entry, t = entryTransition i := by
  change t ∈ [initializeTransition,
    createBidTransition,
    settleAndCreateTransition,
    settleAuctionTransition,
    pauseTransition,
    unpauseTransition,
    setTimeBufferTransition,
    setReservePriceTransition,
    setMinBidIncTransition,
    transferOwnershipTransition,
    renounceOwnershipTransition,
    ownerGetter,
    pausedGetter,
    nounsGetter,
    wethGetter,
    timeBufferGetter,
    reservePriceGetter,
    minBidIncGetter,
    durationGetter,
    auctionGetter] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨11, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨18, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨19, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨17, rfl⟩
  · exact ⟨16, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨9, rfl⟩

theorem dispatchEntry {cd : ByteArray} (i : Entry)
    (hsel : (entryBytes i == cd.extract 0 4) = true) :
    dispatchMsg auctionContract cd = some (entryTransition i) := by
  have hcd := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList auctionContract cd (by rfl)]
  change dispatchList [initializeTransition,
    createBidTransition,
    settleAndCreateTransition,
    settleAuctionTransition,
    pauseTransition,
    unpauseTransition,
    setTimeBufferTransition,
    setReservePriceTransition,
    setMinBidIncTransition,
    transferOwnershipTransition,
    renounceOwnershipTransition,
    ownerGetter,
    pausedGetter,
    nounsGetter,
    wethGetter,
    timeBufferGetter,
    reservePriceGetter,
    minBidIncGetter,
    durationGetter,
    auctionGetter] cd = some (entryTransition i)
  simp only [dispatchList, selectorOf,
    durationSelectorBytes,
    nounsSelectorBytes,
    setMinBidIncrementPercentageSelectorBytes,
    unpauseSelectorBytes,
    wethSelectorBytes,
    pausedSelectorBytes,
    createBidSelectorBytes,
    setTimeBufferSelectorBytes,
    renounceOwnershipSelectorBytes,
    auctionSelectorBytes,
    pauseSelectorBytes,
    initializeSelectorBytes,
    ownerSelectorBytes,
    settleAuctionSelectorBytes,
    minBidIncrementPercentageSelectorBytes,
    setReservePriceSelectorBytes,
    reservePriceSelectorBytes,
    timeBufferSelectorBytes,
    settleCurrentAndCreateNewAuctionSelectorBytes,
    transferOwnershipSelectorBytes, hcd]
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

theorem dispatchNone {cd : ByteArray}
    (hnm : ∀ i : Entry, (entryBytes i == cd.extract 0 4) = false) :
    dispatchMsg auctionContract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  obtain ⟨i, rfl⟩ := transitionCovered t ht
  rw [entrySelector]
  exact hnm i

theorem dispatchShort {cd : ByteArray} (hsz : cd.size < 4) :
    dispatchMsg auctionContract cd = none := by
  rw [dispatchMsg_eq_dispatchList auctionContract cd (by rfl)]
  apply dispatchList_none_short _ _ hsz
  intro t ht
  obtain ⟨i, rfl⟩ := transitionCovered t ht
  rw [entrySelector, entryBytes_size]

/-- The body entry reached after selector routing, before its per-entry value guard. -/
abbrev EntryReached (i : Entry) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap)
    (A : Substate) (I : ExecutionEnv) (g : UInt256) : Prop :=
  ∃ k C, RD auctionBytecode I (Sat256.ofUInt256 g)
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (entryPc i)
    [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C

end Auction

namespace Reasoning.Reach

/-- LIBRARY CANDIDATE: the Shanghai `PUSH0; DUP1; REVERT` terminal. -/
theorem RD.auctionRevert0 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) : RDrev code g s0 :=
  h.push0 hd0 (by omega)
    |>.dup1 hd1 (by omega)
    |>.rev 0 hd2 (fun s _ hstks => memExpRevert0 s hstks) (by omega)

end Reasoning.Reach
