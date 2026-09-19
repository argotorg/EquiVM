import Solm.Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

namespace Auction

abbrev guardTarget (i : Entry) : UInt256 := entryPc i + ⟨11⟩
abbrev guardTestPc (i : Entry) : UInt256 := entryPc i + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩
abbrev guardedBodyPc (i : Entry) : UInt256 := guardTarget i + ⟨1⟩ + ⟨1⟩

def entryGuardWf (i : Entry) : Prop :=
  decode auctionBytecode (entryPc i) = some (.JUMPDEST, .none) ∧
  decode auctionBytecode (entryPc i + ⟨1⟩) = some (.CALLVALUE, .none) ∧
  decode auctionBytecode (entryPc i + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none) ∧
  decode auctionBytecode (entryPc i + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none) ∧
  decode auctionBytecode (guardTestPc i) = some (.Push .PUSH2, some (guardTarget i, 2)) ∧
  decode auctionBytecode (guardTestPc i + UInt256.ofNat 3) = some (.JUMPI, .none) ∧
  decode auctionBytecode (guardTestPc i + UInt256.ofNat 3 + ⟨1⟩) = some (.PUSH0, .none) ∧
  decode auctionBytecode (guardTestPc i + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩) =
    some (.DUP1, .none) ∧
  decode auctionBytecode (guardTestPc i + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.REVERT, .none) ∧
  decode auctionBytecode (guardTarget i) = some (.JUMPDEST, .none) ∧
  decode auctionBytecode (guardTarget i + ⟨1⟩) = some (.POP, .none) ∧
  (D_J auctionBytecode 0).contains (guardTarget i) = true

theorem entryGuards : ∀ i : Entry, i ≠ 6 → entryGuardWf i := by
  unfold entryGuardWf
  native_decide

theorem guardedBody (i : Entry) (hi : i ≠ 6) :
    ∃ rest, (entryTransition i).body = nonpayable :: rest := by
  rcases i with ⟨i, hib⟩
  interval_cases i <;> first | exact ⟨_, rfl⟩ | exact (hi rfl).elim

theorem entryGuardPrefix {I g s0 sel mem aw rdata acc k C} (i : Entry) (hi : i ≠ 6)
    (h : RD auctionBytecode I g s0 (entryPc i) [sel] mem aw rdata acc k C) :
    RD auctionBytecode I g s0 (guardTestPc i)
      [UInt256.isZero I.weiValue, I.weiValue, sel] mem aw rdata acc (k + 4) (C + 9) := by
  obtain ⟨hd0, hd1, hd2, hd3, _⟩ := entryGuards i hi
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov), raw callvalue hd1 (by evm_ov),
    raw dup1 hd2 (by evm_ov), raw iszero hd3 (by evm_ov) ]

theorem entryGuardZero {I g s0 sel mem aw rdata acc k C} (i : Entry) (hi : i ≠ 6)
    (h : RD auctionBytecode I g s0 (entryPc i) [sel] mem aw rdata acc k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k' C', RD auctionBytecode I g s0 (guardedBodyPc i) [sel] mem aw rdata acc k' C' := by
  obtain ⟨_, _, _, _, hpush, hji, _, _, _, hjd, hpop, htarget⟩ := entryGuards i hi
  have rd := entryGuardPrefix i hi h
  exact ⟨_, _, evm_run rd with [
    raw push2 (guardTarget i) hpush (by evm_ov),
    raw jumpiT hji (by rw [hwv]; decide) htarget (by evm_ov),
    raw jumpdest hjd (by evm_ov), raw pop hpop (by evm_ov) ]⟩

theorem entryGuardNonzero {I g s0 sel mem aw rdata acc k C} (i : Entry) (hi : i ≠ 6)
    (h : RD auctionBytecode I g s0 (entryPc i) [sel] mem aw rdata acc k C)
    (hwv : I.weiValue ≠ ⟨0⟩) : RDrev auctionBytecode g s0 := by
  obtain ⟨_, _, _, _, hpush, hji, hr0, hr1, hr2, _⟩ := entryGuards i hi
  have rd := entryGuardPrefix i hi h
  exact evm_run rd with [
    raw push2 (guardTarget i) hpush (by evm_ov),
    raw jumpiNT hji (isZero_eq_zero_of_ne hwv) (by evm_ov),
    raw auctionRevert0 hr0 hr1 hr2 (by evm_ov) ]

theorem entryNonpayableRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (i : Entry) (hi : i ≠ 6) (hcode : I.code = auctionBytecode)
    (hsel : selIs I (entryBytes i)) (hreach : EntryReached i cA gh bl σ_evm σ₀ A I g)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd⟩ := hreach
  have hrev := entryGuardNonzero i hi rd hwv
  have hd := dispatchEntry i hsel
  apply hrev.reEquivElim hcode
  intro _ _ hXi
  by_cases hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
      ((entryTransition i).params.map Param.name)
      (transitionSignature (entryTransition i)).paramTypes I.calldata = none
  · exact reEquiv_decodingFailed hd hdec hXi (by rfl) (by rfl)
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    have hbody : ExecTransitionBody auctionConfig auctionContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
        (entryTransition i).body .reverted := by
      obtain ⟨rest, hrest⟩ := guardedBody i hi
      rw [hrest]
      exact bodyReverts_nonPayable hwv
    exact reEquiv_execution hd hca hbody (by rw [hXi]; exact .revert rfl rfl)
      (by rfl) (by rfl)

end Auction
