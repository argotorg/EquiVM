import Benchmarks.Auction.CreateBidHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem evalExpr_createBid_minBidRhs_revert_addOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hmulFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddOverflow : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (u256 (.binary .add (auctionMemField "amount")
          (.binary .div (u256 (.binary .mul (auctionMemField "amount")
            (.storage minBidIncRef))) (.intLit 100)))) =
      .revert := by
  simp only [u256, evalExpr?, evalExpr_createBid_mem_amount, evalExpr_createBid_minBid,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [uint256Int]
  rw [if_neg (by
    apply not_or.mpr
    constructor
    · exact not_lt_of_ge (Int.natCast_nonneg _)
    · exact not_le_of_gt (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hmulFit)))]
  simp
  intro _
  exact Int.ofNat_le.mpr (by simpa [UInt256.size] using haddOverflow)

theorem evalExpr_createBid_minBidGuard_revert_addOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hmulFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddOverflow : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (.binary .ge (.env .callvalue)
          (u256 (.binary .add (auctionMemField "amount")
            (.binary .div (u256 (.binary .mul (auctionMemField "amount")
              (.storage minBidIncRef))) (.intLit 100))))) =
      .revert := by
  simp only [evalExpr?, evalExpr_createBid_callvalue,
    evalExpr_createBid_minBidRhs_revert_addOverflow evm I hmulFit haddOverflow,
    EvalResult.bind, bind]

theorem auctionCreateBidTransitionReverts_minBidAddOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddOverflow : UInt256.size ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_noun_eq_true (auctionCreateBidEnterState evm) I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_time_lt_true (auctionCreateBidEnterState evm) I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_reserve_ge_true (auctionCreateBidEnterState evm) I hreserve)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_createBid_minBidGuard_revert_addOverflow
        (auctionCreateBidEnterState evm) I hmulFit haddOverflow))

theorem evalExpr_createBid_minBidGuard_false (evm : EVM.State) (I : ExecutionEnv)
    (hmulFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid : evm.executionEnv.weiValue.toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (.binary .ge (.env .callvalue)
          (u256 (.binary .add (auctionMemField "amount")
            (.binary .div (u256 (.binary .mul (auctionMemField "amount")
              (.storage minBidIncRef))) (.intLit 100))))) =
      .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_createBid_callvalue, u256, evalExpr_createBid_mem_amount,
    evalExpr_createBid_minBid, EvalResult.bind, bind, evalBinaryOp?]
  simp [uint256Int]
  rw [if_neg (by
    apply not_or.mpr
    constructor
    · exact not_lt_of_ge (Int.natCast_nonneg _)
    · exact not_le_of_gt (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hmulFit)))]
  simp
  rw [if_neg (by
    apply not_or.mpr
    constructor
    · exact not_lt_of_ge (Int.natCast_nonneg _)
    · exact not_le_of_gt (Int.ofNat_lt.mpr (by simpa [UInt256.size] using haddFit)))]
  simp
  exact_mod_cast hbid

theorem auctionCreateBidTransitionReverts_minBidTooLow (evm : EVM.State)
    (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid : (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot (auctionCreateBidEnterState evm) I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_noun_eq_true (auctionCreateBidEnterState evm) I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_time_lt_true (auctionCreateBidEnterState evm) I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_createBid_reserve_ge_true (auctionCreateBidEnterState evm) I hreserve)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_createBid_minBidGuard_false
        (auctionCreateBidEnterState evm) I hmulFit haddFit hbid))

-- GENERALIZES Benchmarks.Auction.UnpauseMintTrace.auctionCreateAuctionCheckedAddOverflow:
-- the same solc checked-add overflow routine at active words 10.
set_option maxHeartbeats 1000000 in
theorem auctionCreateBidCheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5704⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 10)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have hgt : UInt256.gt a (b + a) = ⟨1⟩ :=
    auctionCreateAuctionCheckedAddOverflowGt a b hover
  have rd5711₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd5711 := rd5711₀
  rw [hgt] at rd5711
  have rd5712₀ := evm_run rd5711 with [iszero]
  have rd5712 := rd5712₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5712
  have rd5630 := evm_run rd5712 with [
    push2 ⟨4886⟩, jumpiNT (by decide), push2 ⟨4886⟩, push2 ⟨5630⟩,
    jump (by jump_dest)]
  exact auctionCreateBidPanicOverflowRevert rd5630 (by evm_ov)

theorem auctionCreateBid_minBidDiv_toNat (amount minBid : UInt256)
    (hmulFit : amount.toNat * minBid.toNat < UInt256.size) :
    (UInt256.div (UInt256.mul minBid amount) ⟨100⟩).toNat =
      amount.toNat * minBid.toNat / 100 := by
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt]
  · rw [show (⟨100⟩ : UInt256).toNat = 100 by rfl]
    rw [Nat.mul_comm]
  · simpa [Nat.mul_comm] using hmulFit

theorem auctionCreateBidX_revert_minBidAddOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddOverflow : UInt256.size ≤
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let minBidRaw := auctionSlotWord ⟨205⟩ σ1 I
  let minBid := UInt256.land minBidRaw ⟨255⟩
  let minBidStep := UInt256.div (UInt256.mul minBid amount) ⟨100⟩
  obtain ⟨_, _, rd1547⟩ := auctionCreateBidX_toMinBidAddCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit hreach
  obtain ⟨_, _, rd1547'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1547⟩
      [minBidStep, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, minBidRaw, minBid,
        minBidStep] using rd1547⟩
  have rd5704 := evm_run rd1547' with [
    jumpdest, dup2, push1 ⟨32⟩, add,
    raw mload 0 amount (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push2 ⟨1562⟩, swap2, swap1, push2 ⟨5704⟩, jump (by jump_dest)]
  have hstepNat : minBidStep.toNat = amount.toNat * minBid.toNat / 100 := by
    simpa [minBidStep, amount, minBid] using auctionCreateBid_minBidDiv_toNat amount minBid
      (by simpa [amount, minBid, minBidRaw, σ1] using hmulFit)
  have haddEVM : UInt256.size ≤ amount.toNat + minBidStep.toNat := by
    simpa [amount, minBid, minBidRaw, minBidStep, σ1, hstepNat] using haddOverflow
  exact auctionCreateBidCheckedAddOverflow
    (a := amount) (b := minBidStep) (ret := ⟨1562⟩)
    (R := [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 haddEVM (by simp)

theorem auctionCreateBidX_toMinBidCompare {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1562⟩
      [UInt256.div
          (UInt256.mul
            (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I) ⟨255⟩)
            (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)) ⟨100⟩ +
        auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I,
        ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let minBidRaw := auctionSlotWord ⟨205⟩ σ1 I
  let minBid := UInt256.land minBidRaw ⟨255⟩
  let minBidStep := UInt256.div (UInt256.mul minBid amount) ⟨100⟩
  obtain ⟨_, _, rd1547⟩ := auctionCreateBidX_toMinBidAddCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit hreach
  obtain ⟨_, _, rd1547'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1547⟩
      [minBidStep, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, minBidRaw, minBid,
        minBidStep] using rd1547⟩
  have rd5704 := evm_run rd1547' with [
    jumpdest, dup2, push1 ⟨32⟩, add,
    raw mload 0 amount (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push2 ⟨1562⟩, swap2, swap1, push2 ⟨5704⟩, jump (by jump_dest)]
  have hstepNat : minBidStep.toNat = amount.toNat * minBid.toNat / 100 := by
    simpa [minBidStep, amount, minBid] using auctionCreateBid_minBidDiv_toNat amount minBid
      (by simpa [amount, minBid, minBidRaw, σ1] using hmulFit)
  have haddEVM : amount.toNat + minBidStep.toNat < UInt256.size := by
    simpa [amount, minBid, minBidRaw, minBidStep, σ1, hstepNat] using haddFit
  obtain ⟨_, _, rd1562⟩ := auctionCreateAuctionCheckedAddOk
    (a := amount) (b := minBidStep) (ret := ⟨1562⟩)
    (R := [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 haddEVM (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, minBidRaw, minBid,
      minBidStep] using rd1562⟩

def auctionCreateBidMinBidAmountStringWord0 : UInt256 :=
  ⟨0x4d7573742073656e64206d6f7265207468616e206c6173742062696420627920⟩

def auctionCreateBidMinBidAmountStringWord1 : UInt256 :=
  ⟨0x6d696e426964496e6372656d656e7450657263656e7461676520616d6f756e74⟩

noncomputable def auctionCreateBidMinBidAmountMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨64⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionCreateBidMinBidAmountMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionCreateBidMinBidAmountStringWord0).write 0
    (auctionCreateBidMinBidAmountMem2 noun amount start finish bidder settled) 388 32

noncomputable def auctionCreateBidMinBidAmountMem4
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionCreateBidMinBidAmountStringWord1).write 0
    (auctionCreateBidMinBidAmountMem3 noun amount start finish bidder settled) 420 32

theorem auctionCreateBidMinBidAmountMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidMinBidAmountMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionCreateBidMinBidAmountMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨64⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidMinBidAmountMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidMinBidAmountMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionCreateBidMinBidAmountMem3
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidMinBidAmountMem2 noun amount start finish bidder settled)
    auctionCreateBidMinBidAmountStringWord0 388 388 420
    (auctionCreateBidMinBidAmountMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidMinBidAmountMem4_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidMinBidAmountMem4 noun amount start finish bidder settled).size = 452 := by
  unfold auctionCreateBidMinBidAmountMem4
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidMinBidAmountMem3 noun amount start finish bidder settled)
    auctionCreateBidMinBidAmountStringWord1 420 420 452
    (auctionCreateBidMinBidAmountMem3_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidMinBidAmountMem4_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidMinBidAmountMem4 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidMinBidAmountMem4
  rw [toByteArray_write_read_below_of_gap auctionCreateBidMinBidAmountStringWord1 _ 420 64
    (by rw [auctionCreateBidMinBidAmountMem3_size]; omega) (by omega)
    (by rw [auctionCreateBidMinBidAmountMem3_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidMinBidAmountMem3
  rw [toByteArray_write_read_below_of_gap auctionCreateBidMinBidAmountStringWord0 _ 388 64
    (by rw [auctionCreateBidMinBidAmountMem2_size]; omega) (by omega)
    (by rw [auctionCreateBidMinBidAmountMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidMinBidAmountMem2
  rw [toByteArray_write_read_below_of_gap (⟨64⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidMinBidAmountMem4_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidMinBidAmountMem4 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidMinBidAmountMem4 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidMinBidAmountMem4_size]; decide)
    (auctionCreateBidMinBidAmountMem4_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

theorem auctionCreateBidX_revert_minBidTooLow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hnoun :
      auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I = auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hreserve : (auctionSlotWord ⟨204⟩ (auctionCreateBidEnterMap σ I) I).toNat ≤
      I.weiValue.toNat)
    (hmulFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
        (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid : I.weiValue.toNat <
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let minBidRaw := auctionSlotWord ⟨205⟩ σ1 I
  let minBid := UInt256.land minBidRaw ⟨255⟩
  let minBidStep := UInt256.div (UInt256.mul minBid amount) ⟨100⟩
  let minRequired := minBidStep + amount
  obtain ⟨_, _, rd1562⟩ := auctionCreateBidX_toMinBidCompare
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hreach
  obtain ⟨_, _, rd1562'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1562⟩
      [minRequired, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, minBidRaw, minBid,
        minBidStep, minRequired] using rd1562⟩
  have hstepNat : minBidStep.toNat = amount.toNat * minBid.toNat / 100 := by
    simpa [minBidStep, amount, minBid] using auctionCreateBid_minBidDiv_toNat amount minBid
      (by simpa [amount, minBid, minBidRaw, σ1] using hmulFit)
  have hrequiredNat :
      minRequired.toNat = amount.toNat + amount.toNat * minBid.toNat / 100 := by
    dsimp [minRequired]
    rw [uadd_toNat, hstepNat, Nat.mod_eq_of_lt]
    · rw [Nat.add_comm]
    · simpa [hstepNat, Nat.add_comm, amount, minBid, minBidRaw, minBidStep, σ1] using
        haddFit
  have hlt : UInt256.lt I.weiValue minRequired = ⟨1⟩ := by
    apply ult_one
    rw [hrequiredNat]
    simpa [amount, minBid, minBidRaw, σ1] using hbid
  have rd1566 := evm_run rd1562' with [jumpdest, callvalue, lt, iszero]
  have hcond : UInt256.isZero (UInt256.lt I.weiValue minRequired) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1570 := evm_run rd1566 with [push2 ⟨1681⟩, jumpiNT hcond]
  have rd1574 := evm_run rd1570 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd1581 := rd1574.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd1598 := evm_run rd1581 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 (auctionCreateBidMinBidAmountMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1635 := rd1598.pushConst auctionCreateBidMinBidAmountStringWord0
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1636 := evm_run rd1635 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionCreateBidMinBidAmountMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1669 := rd1636.pushConst auctionCreateBidMinBidAmountStringWord1
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1677₀ := evm_run rd1669 with [
    push1 ⟨100⟩, dup3, add,
    raw mstore 3 (auctionCreateBidMinBidAmountMem4 noun amount start finish bidder settled)
      (UInt256.ofNat 15) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add]
  have rd1677 := rd1677₀
  rw [show (⟨132⟩ : UInt256) + ⟨320⟩ = ⟨452⟩ by decide] at rd1677
  have rd994 := evm_run rd1677 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 15) (by decide)
      mem_cost
      (auctionCreateBidMinBidAmountMem4_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨452⟩ : UInt256) ⟨320⟩ = ⟨132⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

end Auction
