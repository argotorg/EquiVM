import Solm.Benchmarks.Auction.DispatchFacts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

namespace Auction

theorem auctionPrologue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) :
    RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 3 18 := by
  exact evm_run (RD.initState hcode) with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by native_decide) (by native_decide) ]

theorem auctionReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨18⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd13⟩ := solcCalldataOk
    (bodyPc := ⟨5⟩) (selLoadTgt := ⟨283⟩) (opR := .PUSH2) (wR := 2)
    (auctionPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode)
    hsz hsize (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by
      native_decide) (by native_decide)
  exact solcSelectorLoad rd13 (by native_decide) (by native_decide) (by native_decide) (by
    native_decide) (by simp)

theorem auctionReachGroup {ee g s0 word mem aw rdata acc k C}
    (h : RD auctionBytecode ee g s0 ⟨18⟩ [word] mem aw rdata acc k C) :
    ∃ k' C', RD auctionBytecode ee g s0 (groupFirstPc (selectedGroup word))
      [word] mem aw rdata acc k' C' := by
  by_cases hroot : UInt256.gt (armSelNat auctionBytecode ⟨18⟩) word = ⟨0⟩
  · have rd29 := h.selectorSplitNotTakenResolved
      (tgt := ⟨157⟩) (nextPc := ⟨29⟩) (op := .PUSH2) (width := 2)
      (by unfold selectorSplitWellFormed; native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) hroot (by simp)
    by_cases hupper : UInt256.gt (armSelNat auctionBytecode ⟨29⟩) word = ⟨0⟩
    · have rd40 := rd29.selectorSplitNotTakenResolved
        (tgt := ⟨98⟩) (nextPc := ⟨40⟩) (op := .PUSH2) (width := 2)
        (by unfold selectorSplitWellFormed; native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) hupper (by simp)
      exact ⟨_, _, by simpa only [selectedGroup, if_pos hroot, if_pos hupper,
        groupFirstPc] using rd40⟩
    · have rd98 := rd29.selectorSplitTakenResolved
        (tgt := ⟨98⟩) (op := .PUSH2) (width := 2)
        (by unfold selectorSplitWellFormed; native_decide)
        (by native_decide) (by native_decide) (by native_decide) hupper (by jump_dest) (by simp)
      have rd99 := rd98.jumpdest (by native_decide) (by simp)
      exact ⟨_, _, by simpa only [selectedGroup, if_pos hroot, if_neg hupper,
        groupFirstPc] using rd99⟩
  · have rd157 := h.selectorSplitTakenResolved
      (tgt := ⟨157⟩) (op := .PUSH2) (width := 2)
      (by unfold selectorSplitWellFormed; native_decide)
      (by native_decide) (by native_decide) (by native_decide) hroot (by jump_dest) (by simp)
    have rd158 := rd157.jumpdest (by native_decide) (by simp)
    by_cases hlower : UInt256.gt (armSelNat auctionBytecode ⟨158⟩) word = ⟨0⟩
    · have rd169 := rd158.selectorSplitNotTakenResolved
        (tgt := ⟨227⟩) (nextPc := ⟨169⟩) (op := .PUSH2) (width := 2)
        (by unfold selectorSplitWellFormed; native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) hlower (by simp)
      exact ⟨_, _, by simpa only [selectedGroup, if_neg hroot, if_pos hlower,
        groupFirstPc] using rd169⟩
    · have rd227 := rd158.selectorSplitTakenResolved
        (tgt := ⟨227⟩) (op := .PUSH2) (width := 2)
        (by unfold selectorSplitWellFormed; native_decide)
        (by native_decide) (by native_decide) (by native_decide) hlower (by jump_dest) (by simp)
      have rd228 := rd227.jumpdest (by native_decide) (by simp)
      exact ⟨_, _, by simpa only [selectedGroup, if_neg hroot, if_neg hlower,
        groupFirstPc] using rd228⟩

theorem auctionReachEntry {cA gh bl σ σ₀ A I} {g : UInt256} (i : Entry)
    (hcode : I.code = auctionBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (entryBytes i)) :
    EntryReached i cA gh bl σ σ₀ A I g := by
  have hword := entryWord_eq i hsz hsel
  obtain ⟨_, _, rd18⟩ := auctionReachSplit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hsz hsize
  obtain ⟨_, _, rdGroup⟩ := auctionReachGroup rd18
  have hg : selectedGroup (solcSelectorWord I) = entryGroup i := by
    rw [hword, selectedGroup_entry]
  rw [hg] at rdGroup
  exact RD.dispatchTo (entryPc i) (i.val % 5) rdGroup
    (fun j hj => groupArmsWellFormed (entryGroup i) ⟨j, by omega⟩)
    (fun j hj => by rw [hword]; exact entryArmsMiss i ⟨j, by omega⟩ hj)
    (by rw [hword]; exact entryArmHit i)
    (by rw [entryArmTarget]; exact entryJumpdest i)
    (entryArmTarget i) (by simp)

theorem auctionXShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) (hsz : I.calldata.size < 4) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd5 := auctionPrologue
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  exact evm_run rd5 with [
    push1 ⟨4⟩, calldatasize, lt, push2 ⟨283⟩,
    jumpiT (lt_four_ne_zero_of_lt hsz) (by jump_dest), jumpdest,
    raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]

theorem auctionSkipGroup {ee g s0 word mem aw rdata acc k C} (group : Fin 4)
    (h : RD auctionBytecode ee g s0 (groupFirstPc group) [word] mem aw rdata acc k C)
    (hm : ∀ j : Fin 5,
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode (groupFirstPc group) j.val)) word = ⟨0⟩) :
    ∃ k' C', RD auctionBytecode ee g s0 (nthArmPc auctionBytecode (groupFirstPc group) 5)
      [word] mem aw rdata acc k' C' := by
  have skip : ∀ n, n ≤ 5 →
      ∃ k' C', RD auctionBytecode ee g s0
        (nthArmPc auctionBytecode (groupFirstPc group) n) [word] mem aw rdata acc k' C' := by
    intro n hn
    induction n with
    | zero => exact ⟨k, C, h⟩
    | succ n ih =>
      obtain ⟨_, _, rd⟩ := ih (by omega)
      have rdNext := rd.selectorArmNotTakenAuto
        (groupArmsWellFormed group ⟨n, by omega⟩) (hm ⟨n, by omega⟩) (by simp)
      rw [groupNextPc group ⟨n, by omega⟩] at rdNext
      exact ⟨_, _, rdNext⟩
  exact skip 5 (by omega)

theorem auctionGroupMissRevert {ee g s0 word mem aw rdata acc k C} (group : Fin 4)
    (h : RD auctionBytecode ee g s0
      (nthArmPc auctionBytecode (groupFirstPc group) 5) [word] mem aw rdata acc k C) :
    RDrev auctionBytecode g s0 := by
  rw [groupEnd] at h
  rcases group with ⟨group, hg⟩
  interval_cases group <;> simp only [groupEndPc] at h
  · exact (h.jumpdest (by native_decide) (by simp)).auctionRevert0
      (by native_decide) (by native_decide) (by native_decide) (by simp)
  · exact h.auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by simp)
  · exact h.auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by simp)
  · exact h.auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem auctionXNoMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i : Entry, ¬ selIs I (entryBytes i)) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd18⟩ := auctionReachSplit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz hsize
  obtain ⟨_, _, rdGroup⟩ := auctionReachGroup rd18
  obtain ⟨_, _, rdMiss⟩ := auctionSkipGroup _ rdGroup (by
    intro j
    rw [groupArmEq hsz]
    have hf : (entryBytes (groupEntry (selectedGroup (solcSelectorWord I)) j) ==
        I.calldata.extract 0 4) = false := by
      simpa only [selIs, Bool.not_eq_true] using
        hnm (groupEntry (selectedGroup (solcSelectorWord I)) j)
    rw [hf]
    rfl)
  exact auctionGroupMissRevert _ rdMiss

end Auction
