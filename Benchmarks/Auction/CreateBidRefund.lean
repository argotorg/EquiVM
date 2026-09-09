import Benchmarks.Auction.CreateBidSuccess
import Benchmarks.Auction.SettleAuctionTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem evalExpr_createBid_lastBidderStore_mem_amount
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm' (auctionMemField "amount") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore,
    auctionSettleAuctionSnapshotValue, auctionSettleAuctionSnapshotFields, evalExpr?,
    EvalResult.ofOption, lookupField?, lookupAssoc, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self, EvalResult.bind, bind]

theorem evalExprs_createBid_refund_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm [.var "lastBidder", auctionMemField "amount"] =
      .ok
        [.address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat)] := by
  simp [evalExprs?, evalExpr_createBid_lastBidder,
    evalExpr_createBid_lastBidderStore_mem_amount, EvalResult.bind, bind, pure]

theorem evalExpr_createBid_lastBidderStore_insert_refund_mem_endTime
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evm I).insert "_refund" .unit }
        evm' (auctionMemField "endTime") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore,
    auctionSettleAuctionSnapshotValue, auctionSettleAuctionSnapshotFields, evalExpr?,
    EvalResult.ofOption, lookupField?, lookupAssoc, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self, EvalResult.bind, bind]

theorem evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evm I).insert "_refund" .unit }
        evm' (.storage timeBufferRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨203⟩).toNat)) := by
  have hbase :
      ((auctionCreateBidLastBidderStore evm I).insert "_refund" .unit).get?
          timeBufferRef.base =
        none := by
    have hlookup :=
      store_get_ne (auctionCreateBidLastBidderStore evm I)
        (k := "_refund") (a := timeBufferRef.base) .unit (by decide)
    rw [hlookup]
    exact auctionCreateBidLastBidderStore_timeBuffer_get? evm I
  have her : evalStorageRef auctionConfig
      { contract := auctionContract,
        locals := (auctionCreateBidLastBidderStore evm I).insert "_refund" .unit }
      evm' timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  exact evalExpr_storage_scalar_value (cfg := auctionConfig)
    (solm :=
      { contract := auctionContract,
        locals := (auctionCreateBidLastBidderStore evm I).insert "_refund" .unit })
    (evm := evm') (slot := timeBufferRef)
    (er := ({ base := "timeBuffer", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨203⟩)
    hbase her hty (by rfl)
    (by simpa using auctionStorageLocLoad_uint256 evm' ⟨203⟩)

theorem evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund_extended
    (evm evm' : EVM.State) (I : ExecutionEnv) (extended : Bool) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := ((auctionCreateBidLastBidderStore evm I).insert "_refund" .unit).insert
            "extended" (.bool extended) }
        evm' (.storage timeBufferRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨203⟩).toNat)) := by
  have hbase :
      (((auctionCreateBidLastBidderStore evm I).insert "_refund" .unit).insert "extended"
          (.bool extended)).get? timeBufferRef.base =
        none := by
    have hlookup :=
      store_get_ne2 (auctionCreateBidLastBidderStore evm I)
        (k1 := "_refund") (k2 := "extended") (a := timeBufferRef.base)
        .unit (.bool extended) (by decide) (by decide)
    rw [hlookup]
    exact auctionCreateBidLastBidderStore_timeBuffer_get? evm I
  have her : evalStorageRef auctionConfig
      { contract := auctionContract,
        locals := ((auctionCreateBidLastBidderStore evm I).insert "_refund" .unit).insert
          "extended" (.bool extended) }
      evm' timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  exact evalExpr_storage_scalar_value (cfg := auctionConfig)
    (solm :=
      { contract := auctionContract,
        locals := ((auctionCreateBidLastBidderStore evm I).insert "_refund" .unit).insert
          "extended" (.bool extended) })
    (evm := evm') (slot := timeBufferRef)
    (er := ({ base := "timeBuffer", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := auctionUint256Loc ⟨203⟩)
    hbase her hty (by rfl)
    (by simpa using auctionStorageLocLoad_uint256 evm' ⟨203⟩)

theorem evalExpr_createBid_extended_true_after_refund
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (hle :
      (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evmSnapshot I).insert "_refund" .unit }
        evmCurrent
        (.binary .lt (.binary .sub (auctionMemField "endTime") now)
          (.storage timeBufferRef)) =
      .ok (.bool true) := by
  have hsubNat :
      (UInt256.sub
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat =
        (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat := by
    exact usub_toNat hle
  have hextendedNat :
      (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat := by
    calc
      (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat =
        (UInt256.sub
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat := hsubNat.symm
      _ < (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat :=
        hextended
  have hlt :
      Int.ofNat
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
        Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
      Int.ofNat
        (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat := by
    calc
      Int.ofNat
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
        Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat =
          Int.ofNat
            ((Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
              (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat) := by
            exact (Int.ofNat_sub hle).symm
      _ < Int.ofNat
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat :=
        Int.ofNat_lt.mpr hextendedNat
  simp only [evalExpr?, evalExpr_createBid_lastBidderStore_insert_refund_mem_endTime,
    evalExpr_settleAuction_now, evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund,
    EvalResult.bind, bind, evalBinaryOp?]
  change EvalResult.ok
      (Value.bool
        (decide
          (Int.ofNat
              (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
          Int.ofNat
            (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat))) =
    EvalResult.ok (Value.bool true)
  rw [show
      decide
        (Int.ofNat
            (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
        Int.ofNat
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) =
        true by
    exact decide_eq_true hlt]

theorem evalExpr_createBid_extended_false_after_refund
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (hle :
      (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat)
    (hnotExtended :
      (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat ≤
        (UInt256.sub
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evmSnapshot I).insert "_refund" .unit }
        evmCurrent
        (.binary .lt (.binary .sub (auctionMemField "endTime") now)
          (.storage timeBufferRef)) =
      .ok (.bool false) := by
  have hsubNat :
      (UInt256.sub
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat =
        (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat := by
    exact usub_toNat hle
  have hnotlt :
      ¬ (Int.ofNat
            (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
        Int.ofNat
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) := by
    have hnotExtendedNat :
        (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat ≤
          (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat := by
      calc
        (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat ≤
            (UInt256.sub
              (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩)
              (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)).toNat := hnotExtended
        _ = (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat := hsubNat
    have hge :
        Int.ofNat
            (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat ≤
          Int.ofNat
              (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat := by
      calc
        Int.ofNat
            (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat ≤
          Int.ofNat
            ((Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
              (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat) := by
            exact Int.ofNat_le.mpr hnotExtendedNat
        _ = Int.ofNat
              (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat :=
          Int.ofNat_sub hle
    exact not_lt_of_ge hge
  simp only [evalExpr?, evalExpr_createBid_lastBidderStore_insert_refund_mem_endTime,
    evalExpr_settleAuction_now, evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund,
    EvalResult.bind, bind, evalBinaryOp?]
  change EvalResult.ok
      (Value.bool
        (decide
          (Int.ofNat
              (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
            Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
          Int.ofNat
            (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat))) =
    EvalResult.ok (Value.bool false)
  rw [show
      decide
        (Int.ofNat
            (Solm.EVM.storageLoad evmSnapshot evmSnapshot.executionEnv.codeOwner ⟨210⟩).toNat -
          Int.ofNat (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat <
        Int.ofNat
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) =
        false by
      exact decide_eq_false hnotlt]

theorem evalExpr_createBid_extendedEndTime_after_refund
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (haddFit :
      (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat <
        UInt256.size) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := ((auctionCreateBidLastBidderStore evmSnapshot I).insert "_refund" .unit).insert
            "extended" (.bool true) }
        evmCurrent
        (u256 (.binary .add now (.storage timeBufferRef))) =
      .ok (.int (Int.ofNat
        (UInt256.add (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩)).toNat)) := by
  simp only [evalExpr?, evalExpr_settleAuction_now,
    evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund_extended, u256, EvalResult.bind,
    bind, evalBinaryOp?]
  simp [uint256Int]
  rw [if_neg (by
    apply not_or.mpr
    constructor
    · exact not_lt_of_ge (add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
    · exact not_le_of_gt (by
        have hsum :
            Int.ofNat
              ((UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
                (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner
                  ⟨203⟩).toNat) < Int.ofNat UInt256.size :=
          Int.ofNat_lt.mpr haddFit
        simpa [UInt256.size] using hsum))]
  simp only [pure]
  rw [show
      (UInt256.add (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩)).toNat =
        (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat by
    change
      ((UInt256.ofNat evmCurrent.executionEnv.header.timestamp +
          Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) =
        (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat
    rw [uadd_toNat, Nat.mod_eq_of_lt haddFit]]
  simp

theorem evalExpr_createBid_extendedEndTime_revert_after_refund
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := ((auctionCreateBidLastBidderStore evmSnapshot I).insert "_refund" .unit).insert
            "extended" (.bool true) }
        evmCurrent
        (u256 (.binary .add now (.storage timeBufferRef))) =
      .revert := by
  simp only [evalExpr?, evalExpr_settleAuction_now,
    evalExpr_createBid_timeBuffer_lastBidderStore_insert_refund_extended, u256, EvalResult.bind,
    bind, evalBinaryOp?]
  simp [uint256Int]
  intro _
  exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)

theorem auctionCreateBidTransitionReverts_refundLowLevelFailureWethNoCode
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {out : ByteArray}
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
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hrefund : callViaEVM (auctionCreateBidEnterState evm)
      (EVM.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat))
      (Int.ofNat
        (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat)
      ByteArray.empty (false, evmRefund, out) true)
    (hwethCode :
      (UInt256.ofNat (((evmRefund.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consRevert
        (internalCallFunctionRevert
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode evmEnter evmRefund
            recipient amount
            (by simpa [evmEnter, recipient, amount] using hrefund)
            (by simpa [evmEnter, recipient, amount] using hwethCode)))))

theorem auctionCreateBidTransitionReverts_extensionOverflow_refundLowLevelSuccess
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {out : ByteArray}
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
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hrefund : callViaEVM (auctionCreateBidEnterState evm)
      (EVM.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat))
      (Int.ofNat
        (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat)
      ByteArray.empty (true, evmRefund, out))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsRefund.insert "extended" (.bool true)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (auctionSafeTransferBodyReturns_lowLevelSuccess evmEnter evmRefund recipient amount
            (by simpa [evmEnter, recipient, amount] using hrefund)))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hextended))) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (result := .reverted)
    (by simp [evalExpr?, EvalResult.ofOption]) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (by
          simpa [localsExtended, localsRefund, localsLast, evmBidder, evmAmount] using
            evalExpr_createBid_extendedEndTime_revert_after_refund evmEnter evmBidder I
              (by simpa [evmBidder, evmAmount] using hover)))

theorem auctionCreateBidTransitionReturns_noExtension_refundLowLevelSuccess
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {out : ByteArray}
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
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hrefund : callViaEVM (auctionCreateBidEnterState evm)
      (EVM.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat))
      (Int.ofNat
        (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat)
      ByteArray.empty (true, evmRefund, out))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hnotExtended :
      (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat ≤
        (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            ((auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "_refund" .unit).insert "extended" (.bool false) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund)))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsRefund.insert "extended" (.bool false)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (auctionSafeTransferBodyReturns_lowLevelSuccess evmEnter evmRefund recipient amount
            (by simpa [evmEnter, recipient, amount] using hrefund)))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_false_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hnotExtended))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (by simp [evalExpr?, EvalResult.ofOption])
      ExecBlock.nil) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered evmBidder localsExtended)
      (auctionCreateBidAssignStatusNotEntered evmBidder localsExtended
        (by
          simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil

theorem auctionCreateBidTransitionReturns_extension_refundLowLevelSuccess
    (evm evmRefund : EVM.State) (I : ExecutionEnv) {out : ByteArray}
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
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hrefund : callViaEVM (auctionCreateBidEnterState evm)
      (EVM.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat))
      (Int.ofNat
        (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat)
      ByteArray.empty (true, evmRefund, out))
    (hle :
      (UInt256.ofNat
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat ≤
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (haddExtFit :
      (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState evmRefund)).executionEnv.codeOwner
          ⟨203⟩).toNat <
        UInt256.size) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            ((auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "_refund" .unit).insert "extended" (.bool true) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidExtendedState
            (auctionCreateBidBidderState (auctionCreateBidAmountState evmRefund))))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let localsRefund := localsLast.insert "_refund" .unit
  let evmAmount := auctionCreateBidAmountState evmRefund
  let evmBidder := auctionCreateBidBidderState evmAmount
  let evmExtended := auctionCreateBidExtendedState evmBidder
  let localsExtended := localsRefund.insert "extended" (.bool true)
  have hassignEnd :
      assignStorageRef? auctionConfig
          { contract := auctionContract, locals := localsExtended }
          evmBidder .storage (aField "endTime")
          (.int (Int.ofNat
            (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
              (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩)).toNat)) =
        .ok ({ contract := auctionContract, locals := localsExtended }, evmExtended) := by
    exact auctionCreateAuctionAssignUint256Field evmBidder localsExtended "endTime" ⟨210⟩
      (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
        (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩))
      (by
        simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
          auctionCreateBidSnapshotStore, auctionCreateBidStore])
      (by decide) (by rfl)
  dsimp [createBidTransition]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_status_ne_entered_true evm I hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_entered evm I)
      (auctionCreateBidAssignStatusEntered evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_snapshot evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_noun_eq_true evmEnter I hnoun)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_time_lt_true evmEnter I htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_reserve_ge_true evmEnter I hreserve)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createBid_minBidGuard_true evmEnter I hmulFit haddFit hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_mem_bidder evmEnter I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_createBid_lastBidder_ne_zero_true evmEnter I hbidder)
      (ExecBlock.consNormal
        (internalCallFunctionReturn
          (by
            simpa [evmEnter, recipient, amount] using
              evalExprs_createBid_refund_args evmEnter I)
          auctionLookupCallable_safeTransfer
          (by simpa [recipient, amount] using bindParams_safeTransfer recipient amount)
          (auctionSafeTransferBodyReturns_lowLevelSuccess evmEnter evmRefund recipient amount
            (by simpa [evmEnter, recipient, amount] using hrefund)))
        ExecBlock.nil)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmRefund localsRefund)
      (auctionCreateAuctionAssignUint256Field evmRefund localsRefund "amount" ⟨208⟩
        evmRefund.executionEnv.weiValue
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsRefund)
      (auctionCreateAuctionAssignAddressField evmAmount localsRefund "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (by
          simp [localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true_after_refund evmEnter evmBidder I
      (by simpa [evmBidder, evmAmount] using hle)
      (by simpa [evmEnter, evmBidder, evmAmount] using hextended))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := auctionContract, locals := localsExtended } evmExtended)
      (by simp [evalExpr?, EvalResult.ofOption]) ?_) ?_
  · exact ExecBlock.consNormal
      (ExecStmt.assign
        (by
          simpa [localsExtended, localsRefund, localsLast, evmBidder, evmAmount] using
            evalExpr_createBid_extendedEndTime_after_refund evmEnter evmBidder I
              (by simpa [evmBidder, evmAmount] using haddExtFit))
        hassignEnd)
      ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered evmExtended localsExtended)
      (auctionCreateBidAssignStatusNotEntered evmExtended localsExtended
        (by
          simp [localsExtended, localsRefund, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil

theorem auctionCreateBidX_toExtensionCheck_afterRefundJoin {cA gh bl σ σ₀ A I}
    {g : Sat256} {marker : UInt256}
    (hperm : I.perm = true)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionCreateBidBidderMap
        (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let packedAfterAmount := auctionSlotWord ⟨211⟩ σAmount I
  obtain ⟨_, _, rd1715'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    obtain ⟨k, C, rd⟩ := rd1715
    exact ⟨k, C, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd⟩
  have rd1719 := evm_run rd1715' with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720₀⟩ := rd1719.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1720⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σAmount) k C := by
    exact ⟨_, _, by simpa [σAmount, auctionCreateBidAmountMap] using rd1720₀⟩
  have rd1723₀ := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1723₁⟩ := rd1723₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1724⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
      [packedAfterAmount, ⟨211⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σAmount) k C := by
    exact ⟨_, _, by
      simpa [packedAfterAmount, auctionSlotWord] using rd1723₁⟩
  have hsourceClean : UInt256.land (auctionSourceWord I) solcAddrMask = auctionSourceWord I :=
    solcAddrMask_clean (auctionSourceWord_canonical I)
  have hpostWord :
      UInt256.lor (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            packedAfterAmount) =
        setAddressOffset0Word packedAfterAmount (auctionSourceWord I) := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask) packedAfterAmount]
    change UInt256.lor (auctionSourceWord I)
        (UInt256.land packedAfterAmount (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word packedAfterAmount (auctionSourceWord I)
    unfold setAddressOffset0Word
    rw [hsourceClean, u256_lor_comm]
  have rd1737₀ := evm_run rd1724 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, lor, swap1]
  have rd1737 := rd1737₀
  rw [hpostWord] at rd1737
  obtain ⟨_, _, rd1738₀⟩ := rd1737.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1738⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionCreateBidBidderMap σAmount I) k C := by
    exact ⟨_, _, by
      simpa [auctionCreateBidBidderMap, packedAfterAmount, σAmount] using rd1738₀⟩
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount] using rd1738⟩

theorem auctionCreateBidX_toRefundTransferEntry {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidOk :
      (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat +
        ((auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I).toNat *
          (UInt256.land (auctionSlotWord ⟨205⟩ (auctionCreateBidEnterMap σ I) I)
            ⟨255⟩).toNat) / 100 ≤ I.weiValue.toNat)
    (hbidder :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) ≠
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I,
        auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I),
        ⟨1715⟩,
        auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I),
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
  obtain ⟨_, _, rd1681⟩ := auctionCreateBidX_toLastBidderCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hreach
  obtain ⟨_, _, rd1681'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1681⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1681⟩
  have rd1686₀ := evm_run rd1681' with [
    jumpdest, push1 ⟨128⟩, dup2, add]
  have rd1686 := rd1686₀
  rw [show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ by decide] at rd1686
  have rd1697₀ := evm_run rd1686 with [
    raw mload 0 bidder (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and]
  have hmask :
      UInt256.land bidder
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        bidder := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    exact solcAddrMask_clean (by
      simpa [bidder, auctionPackedBidderWord] using solcAddrMask_result_canonical packed)
  have rd1697 := rd1697₀
  rw [hmask] at rd1697
  have rd1698₀ := evm_run rd1697 with [iszero]
  have rd1698 := rd1698₀
  have hbidderNZ : bidder ≠ ⟨0⟩ := by
    simpa [bidder, packed, σ1] using hbidder
  rw [isZero_eq_zero_of_ne hbidderNZ] at rd1698
  have rd1702 := evm_run rd1698 with [push2 ⟨1715⟩, jumpiNT (by decide)]
  have rd3337 := evm_run rd1702 with [
    push2 ⟨1715⟩, dup2, dup4, push1 ⟨32⟩, add,
    raw mload 0 amount (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload160 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push2 ⟨3337⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd3337⟩

noncomputable def auctionCreateBidRefundZeroLenMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32

noncomputable def auctionCreateBidRefundFreeMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨352⟩ : UInt256)).write 0
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled) 64 32

noncomputable def auctionCreateBidRefundLoopMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled) 352 32

theorem auctionCreateBidRefundZeroLenMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled).size = 352 := by
  unfold auctionCreateBidRefundZeroLenMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
    (⟨0⟩ : UInt256) 320 320 352
    (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundFreeMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled).size = 352 := by
  unfold auctionCreateBidRefundFreeMem
  exact toByteArray_write32_size_of_le
    (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled)
    (⟨352⟩ : UInt256) 64 352 352
    (auctionCreateBidRefundZeroLenMem_size noun amount start finish bidder settled)
    (by rw [auctionCreateBidRefundZeroLenMem_size]; omega) (by decide)

theorem auctionCreateBidRefundLoopMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).size = 384 := by
  unfold auctionCreateBidRefundLoopMem
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidRefundFreeMem noun amount start finish bidder settled)
    (⟨0⟩ : UInt256) 352 352 384
    (auctionCreateBidRefundFreeMem_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidRefundFreeMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundFreeMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundFreeMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionCreateBidRefundFreeMem_size]; decide
  · decide
  · unfold auctionCreateBidRefundFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled)
      64
      (by rw [auctionCreateBidRefundZeroLenMem_size]; native_decide)

theorem auctionCreateBidRefundFreeMem_mload320
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨320⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundFreeMem noun amount start finish bidder settled).size
        ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundFreeMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
      ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionCreateBidRefundFreeMem_size]; decide
  · decide
  · unfold auctionCreateBidRefundFreeMem
    rw [write32_read_above (UInt256.toByteArray (⟨352⟩ : UInt256))
      (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled)
      64 (⟨320⟩ : UInt256).toNat
      (by rw [toByteArray_size])
      (by rw [auctionCreateBidRefundZeroLenMem_size]; decide)
      (by decide) (by rw [auctionCreateBidRefundZeroLenMem_size]; decide)]
    unfold auctionCreateBidRefundZeroLenMem
    change (((UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
        (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32)
        |>.readWithPadding 320 32) = UInt256.toByteArray (⟨0⟩ : UInt256)
    exact toByteArray_write_read_back_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      320
      (by rw [auctionSettleAuctionSnapshotMem_size]; native_decide)

theorem auctionCreateBidRefundLoopMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidRefundLoopMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionCreateBidRefundLoopMem_size]; decide
  · decide
  · unfold auctionCreateBidRefundLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionCreateBidRefundFreeMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionCreateBidRefundFreeMem_size]; decide) (by decide)
      (by rw [auctionCreateBidRefundFreeMem_size]; native_decide)]
    unfold auctionCreateBidRefundFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled) 64
      (by rw [auctionCreateBidRefundZeroLenMem_size]; native_decide)

theorem auctionCreateBidRefundTransferEntryToCall {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker noun amount start finish bidder settled : UInt256} {o : ByteArray} {k C : ℕ}
    (howner : UInt256.land owner solcAddrMask = owner)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3337⟩
      [amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4827⟩
      [⟨30000⟩, owner, amount, ⟨352⟩, ⟨0⟩, ⟨352⟩, ⟨0⟩, ⟨352⟩,
        amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner, ⟨3347⟩,
        amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionCreateBidRefundLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k' C' := by
  let memCall := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let memZero := auctionCreateBidRefundZeroLenMem noun amount start finish bidder settled
  let memFree := auctionCreateBidRefundFreeMem noun amount start finish bidder settled
  let memLoop := auctionCreateBidRefundLoopMem noun amount start finish bidder settled
  have rd4768 := evm_run rd with [
    jumpdest, push2 ⟨3347⟩, dup3, dup3, push2 ⟨4768⟩, jump (by jump_dest)]
  have rd4783 := evm_run rd4768 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost (by simpa [memCall] using
        auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push0, dup1, dup3,
    raw mstore (Cₘ (UInt256.ofNat 11) - Cₘ (UInt256.ofNat 10)) memZero
      (UInt256.ofNat 11) (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by native_decide))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, swap3,
    raw mstore 0 memFree (UInt256.ofNat 11) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4814 := evm_run rd4783 with [
    dup2, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    swap1, push2 ⟨30000⟩, swap1, dup6, swap1, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [memFree] using
        auctionCreateBidRefundFreeMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push2 ⟨4815⟩, swap2, swap1, push2 ⟨6093⟩, jump (by jump_dest)]
  have rd6106 := evm_run rd4814 with [
    jumpdest, push0, dup3,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost (by simpa [memFree] using
        auctionCreateBidRefundFreeMem_mload320 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push0, jumpdest, dup2, dup2, lt, iszero, push2 ⟨6124⟩,
    jumpiT (by native_decide) (by jump_dest)]
  have rd4815 := evm_run rd6106 with [
    jumpdest, pop, push0, swap3, add, swap2, dup3,
    raw mstore (Cₘ (UInt256.ofNat 12) - Cₘ (UInt256.ofNat 11)) memLoop
      (UInt256.ofNat 12) (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by native_decide))
      (by
        rw [show (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ by native_decide]
        rfl) (by rfl) (by evm_ov),
    pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd4827 := evm_run rd4815 with [
    jumpdest, push0, push1 ⟨64⟩,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 12) (by native_decide)
      mem_cost (by simpa [memLoop] using
        auctionCreateBidRefundLoopMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup9]
  have hzeroSub : ((⟨352⟩ : UInt256) + ⟨0⟩).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroSub' : (⟨352⟩ : UInt256).sub ⟨352⟩ = ⟨0⟩ := by
    native_decide
  have hzeroAdd : (⟨352⟩ : UInt256) + ⟨0⟩ = ⟨352⟩ := by
    native_decide
  have hownerRaw :
      UInt256.land owner
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    simpa [solcAddrMask] using howner
  exact ⟨_, _, by
    simpa [memCall, memZero, memFree, memLoop, hownerRaw, hzeroSub, hzeroSub', hzeroAdd]
      using rd4827⟩

theorem auctionCreateBidRefundCallSuccessEmptyReturnToJoin {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (ho : o.size = 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨1⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw o acc k' C' := by
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4874 := evm_run rd4838 with [
    push2 ⟨4874⟩, jumpiT (by rw [ho]; native_decide) (by jump_dest)]
  have rd4886 := evm_run rd4874 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap1, swap3, pop, pop, pop]
  have rd3347 := evm_run rd4886 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3570 := evm_run rd3347 with [
    jumpdest, push2 ⟨3570⟩, jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd3570 with [jumpdest, pop, pop, jump (by jump_dest)]⟩

theorem auctionCreateBidRefundCallSuccessNonemptyReturnToJoin {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨1⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem aw o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem' aw' o acc k' C' := by
  let oszWord := UInt256.ofNat o.size
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 :=
    UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
  let dataPtr := freePtr + ⟨32⟩
  let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
  let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
  have hoszWord_ne : oszWord ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    have hsizeZero : o.size = 0 := by
      simpa [oszWord, UInt256.toNat_ofNat_of_lt hosz] using hnat
    exact hne hsizeZero
  have heqZero : UInt256.eq oszWord ⟨0⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hoszWord_ne (uInt256_eq_one_eq heq)
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4844 := evm_run rd4838 with [
    push2 ⟨4874⟩,
    jumpiNT (by simpa [oszWord] using heqZero)]
  have rd4862 := evm_run rd4844 with [
    push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, push0, push1 ⟨32⟩, dup5, add]
  have rd4863 := RD.returndatacopy (Cₘ awCopy - Cₘ awLen) memCopy awCopy rd4862
    (by native_decide)
    (by
      change 0 + oszWord.toNat ≤ o.size
      rw [show oszWord.toNat = o.size by
        simpa [oszWord] using UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun _ haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, dataPtr, awCopy,
        oszWord])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  have rd3347 := evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3570 := evm_run rd3347 with [
    jumpdest, push2 ⟨3570⟩, jumpiT (by native_decide) (by jump_dest)]
  exact ⟨memCopy, awCopy, _, _, evm_run rd3570 with [
    jumpdest, pop, pop, jump (by jump_dest)]⟩

theorem auctionCreateBidRefundCallFailureEmptyReturnToFallback {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (ho : o.size = 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem aw o acc k' C' := by
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4874 := evm_run rd4838 with [
    push2 ⟨4874⟩, jumpiT (by rw [ho]; native_decide) (by jump_dest)]
  have rd4886 := evm_run rd4874 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap1, swap3, pop, pop, pop]
  exact ⟨_, _, evm_run rd4886 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

theorem auctionCreateBidRefundCallFailureNonemptyReturnToFallback {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem aw o acc k C) :
    ∃ mem' aw' k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem' aw' o acc k' C' := by
  let oszWord := UInt256.ofNat o.size
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 :=
    UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
  let dataPtr := freePtr + ⟨32⟩
  let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
  let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
  have hoszWord_ne : oszWord ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    have hsizeZero : o.size = 0 := by
      simpa [oszWord, UInt256.toNat_ofNat_of_lt hosz] using hnat
    exact hne hsizeZero
  have heqZero : UInt256.eq oszWord ⟨0⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hoszWord_ne (uInt256_eq_one_eq heq)
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4844 := evm_run rd4838 with [
    push2 ⟨4874⟩,
    jumpiNT (by simpa [oszWord] using heqZero)]
  have rd4862 := evm_run rd4844 with [
    push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, push0, push1 ⟨32⟩, dup5, add]
  have rd4863 := RD.returndatacopy (Cₘ awCopy - Cₘ awLen) memCopy awCopy rd4862
    (by native_decide)
    (by
      change 0 + oszWord.toNat ≤ o.size
      rw [show oszWord.toNat = o.size by
        simpa [oszWord] using UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun _ haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, dataPtr, awCopy,
        oszWord])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  exact ⟨memCopy, awCopy, _, _, evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

theorem auctionCreateBidX_toExtensionDecision_afterRefundJoin {cA gh bl σ σ₀ A I}
    {g : Sat256} {marker : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp),
        auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionCreateBidBidderMap
        (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) k C := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  obtain ⟨_, _, rd1738⟩ := auctionCreateBidX_toExtensionCheck_afterRefundJoin
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (marker := marker) hperm rd1715
  obtain ⟨_, _, rd1738'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder]
        using rd1738⟩
  obtain ⟨_, _, rd1740₀⟩ := (evm_run rd1738' with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1741⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1741⟩
      [timeBuffer, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1740₀⟩
  have rd1745₀ := evm_run rd1741 with [push1 ⟨96⟩, dup4, add]
  have rd1745 := rd1745₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1745
  have rd1746 := evm_run rd1745 with [
    raw mload 0 finish (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5723 := evm_run rd1746 with [
    push0, swap2, swap1, push2 ⟨1759⟩, swap1, timestamp, swap1, push2 ⟨5723⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidCheckedSubOk
    (a := finish) (b := UInt256.ofNat I.header.timestamp) (ret := ⟨1759⟩)
    (R := [timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
      auctionSelWord I])
    rd5723 (by simpa [finish, σ1] using Nat.le_of_lt htime) (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      timeBuffer] using rd1759⟩

theorem auctionCreateBidX_revert_extensionOverflow_afterRefundJoin {cA gh bl σ σ₀ A I}
    {g : Sat256} {marker : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I).toNat)
    (hextended :
      (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat +
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap
              (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionCreateBidEnterMap σ I) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionCreateBidEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let σAmount := auctionCreateBidAmountMap σ1 I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundJoin
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (marker := marker) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount, σ1] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  have hoverEVM : UInt256.size ≤ nowWord.toNat + timeBuffer.toNat := by
    simpa [nowWord, timeBuffer, σBidder, σAmount, σ1] using hover
  exact auctionCreateBidCheckedAddOverflow
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 hoverEVM (by simp)

theorem auctionCreateBidX_toExtensionCheck_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let packedAfterAmount := auctionSlotWord ⟨211⟩ σAmount I
  obtain ⟨_, _, rd1715'⟩ := rd1715
  have rd1719 := evm_run rd1715' with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720₀⟩ := rd1719.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1720⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [σAmount, auctionCreateBidAmountMap] using rd1720₀⟩
  have rd1723₀ := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1723₁⟩ := rd1723₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1724⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
      [packedAfterAmount, ⟨211⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σAmount) k C := by
    exact ⟨_, _, by simpa [packedAfterAmount, auctionSlotWord] using rd1723₁⟩
  have hsourceClean : UInt256.land (auctionSourceWord I) solcAddrMask = auctionSourceWord I :=
    solcAddrMask_clean (auctionSourceWord_canonical I)
  have hpostWord :
      UInt256.lor (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            packedAfterAmount) =
        setAddressOffset0Word packedAfterAmount (auctionSourceWord I) := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask) packedAfterAmount]
    change UInt256.lor (auctionSourceWord I)
        (UInt256.land packedAfterAmount (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word packedAfterAmount (auctionSourceWord I)
    unfold setAddressOffset0Word
    rw [hsourceClean, u256_lor_comm]
  have rd1737₀ := evm_run rd1724 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, lor, swap1]
  have rd1737 := rd1737₀
  rw [hpostWord] at rd1737
  obtain ⟨_, _, rd1738₀⟩ := rd1737.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [auctionCreateBidBidderMap, packedAfterAmount, σAmount] using rd1738₀⟩

theorem auctionCreateBidX_toExtensionDecision_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [UInt256.sub finish (UInt256.ofNat I.header.timestamp),
        auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I,
        ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty
      (cA', auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) k C := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  obtain ⟨_, _, rd1738⟩ := auctionCreateBidX_toExtensionCheck_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm rd1715
  obtain ⟨_, _, rd1738'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder] using rd1738⟩
  obtain ⟨_, _, rd1740₀⟩ := (evm_run rd1738' with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1741⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1741⟩
      [timeBuffer, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1740₀⟩
  have rd1745₀ := evm_run rd1741 with [push1 ⟨96⟩, dup4, add]
  have rd1745 := rd1745₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1745
  have rd1746 := evm_run rd1745 with [
    raw mload 0 finish (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5723 := evm_run rd1746 with [
    push0, swap2, swap1, push2 ⟨1759⟩, swap1, timestamp, swap1, push2 ⟨5723⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidCheckedSubOk
    (a := finish) (b := UInt256.ofNat I.header.timestamp) (ret := ⟨1759⟩)
    (R := [timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
      auctionSelWord I])
    rd5723 (Nat.le_of_lt htime) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer] using rd1759⟩

theorem auctionCreateBidX_revert_extensionOverflow_afterRefundJoin_state
    {cA cA' gh bl σ σCall σ₀ A I} {g : Sat256} {marker : UInt256}
    {noun amount start finish bidder settled : UInt256}
    (hperm : I.perm = true)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < finish.toNat)
    (hextended :
      (UInt256.sub finish (UInt256.ofNat I.header.timestamp)).toNat <
        (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat +
          (auctionSlotWord ⟨203⟩
            (auctionCreateBidBidderMap (auctionCreateBidAmountMap σCall I) I) I).toNat)
    (rd1715 : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σCall) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σAmount := auctionCreateBidAmountMap σCall I
  let σBidder := auctionCreateBidBidderMap σAmount I
  let timeBuffer := auctionSlotWord ⟨203⟩ σBidder I
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  let nowWord := UInt256.ofNat I.header.timestamp
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_afterRefundJoin_state
    (cA := cA) (cA' := cA') (gh := gh) (bl := bl) (σ := σ) (σCall := σCall)
    (σ₀ := σ₀) (A := A) (g := g) (marker := marker)
    (noun := noun) (amount := amount) (start := start) (finish := finish)
    (bidder := bidder) (settled := settled) hperm htime rd1715
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [σAmount, σBidder, timeBuffer, timeLeft] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨1⟩ := by
    apply ult_one
    simpa [timeLeft, timeBuffer, σBidder, σAmount] using hextended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1764
  have rd1768 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiNT (by decide)]
  obtain ⟨_, _, rd1771₀⟩ := (evm_run rd1768 with [push1 ⟨203⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1771⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1772⟩
      [timeBuffer, ⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA', σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1771₀⟩
  have rd5704 := evm_run rd1771 with [
    push2 ⟨1781⟩, swap1, timestamp, push2 ⟨5704⟩, jump (by jump_dest)]
  have hoverEVM : UInt256.size ≤ nowWord.toNat + timeBuffer.toNat := by
    simpa [nowWord, timeBuffer, σBidder, σAmount] using hover
  exact auctionCreateBidCheckedAddOverflow
    (a := nowWord) (b := timeBuffer) (ret := ⟨1781⟩)
    (R := [⟨1⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I])
    rd5704 hoverEVM (by simp)

end Auction
