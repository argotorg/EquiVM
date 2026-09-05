import Benchmarks.Auction.CreateBidMinBid
import Benchmarks.Auction.CreateAuction

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionCreateBidAmountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨208⟩ I.weiValue

def auctionCreateBidBidderMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨211⟩
    (setAddressOffset0Word (auctionSlotWord ⟨211⟩ σ I) (auctionSourceWord I))

def auctionCreateBidUnlockedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩

def auctionCreateBidAmountState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨208⟩ evm.executionEnv.weiValue

def auctionCreateBidBidderState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)
      (UInt256.ofNat evm.executionEnv.source.val))

def auctionCreateBidUnlockedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨1⟩

theorem evalExpr_createBid_minBidGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (hmulFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      evm.executionEnv.weiValue.toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm
        (.binary .ge (.env .callvalue)
          (u256 (.binary .add (auctionMemField "amount")
            (.binary .div (u256 (.binary .mul (auctionMemField "amount")
              (.storage minBidIncRef))) (.intLit 100))))) =
      .ok (.bool true) := by
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

theorem evalExpr_createBid_sender (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_createBid_sender_word (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm sender =
      .ok (.address (AccountAddress.ofNat
        (UInt256.ofNat evm.executionEnv.source.val).toNat)) := by
  rw [evalExpr_createBid_sender]
  congr
  exact (by
    simpa [auctionSourceWord] using (auctionSource_ofNat evm.executionEnv).symm)

theorem evalExpr_createBid_notEntered (evm : EVM.State) (locals : Store) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm notEntered =
      .ok (.int 1) := by
  simp [notEntered, evalExpr?, pure]

theorem auctionCreateBidAssignStatusNotEntered (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_status" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm .storage
        statusRef (.int 1) =
      .ok ({ contract := auctionContract, locals := locals },
        auctionCreateBidUnlockedState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals } evm
      statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := locals }) (evm := evm)
    (evm' := auctionCreateBidUnlockedState evm) (slot := statusRef)
    (er := { base := "_status", steps := [] }) (ty := .elem (.int uint256Int))
    (loc := auctionUint256Loc ⟨101⟩) (n := 1) hbase her hty (by rfl)
    (by simpa [auctionCreateBidUnlockedState] using
      auctionStorageLocStore_uint256 evm ⟨101⟩ ⟨1⟩)

theorem evalExpr_createBid_mem_bidder (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidSnapshotStore evm I }
        evm (auctionMemField "bidder") =
      .ok (.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat)) := by
  simp [auctionMemField, auctionCreateBidSnapshotStore, auctionSettleAuctionSnapshotValue,
    auctionSettleAuctionSnapshotFields, evalExpr?, EvalResult.ofOption, lookupField?,
    lookupAssoc, EvalResult.bind, bind]

def auctionCreateBidLastBidderStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (auctionCreateBidSnapshotStore evm I).insert "lastBidder"
    (.address (AccountAddress.ofNat
      (auctionPackedBidderWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat))

theorem evalExpr_createBid_lastBidder (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm (.var "lastBidder") =
      .ok (.address (AccountAddress.ofNat
        (auctionPackedBidderWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat)) := by
  simp [evalExpr?, auctionCreateBidLastBidderStore, EvalResult.ofOption]

theorem evalExpr_createBid_lastBidder_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm (.binary .ne (.var "lastBidder") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_createBid_lastBidder, evalExpr_settleAuction_zeroAddr,
    EvalResult.bind, bind, evalBinaryOp?]
  rw [hbidder]
  rfl

theorem evalExpr_createBid_lastBidder_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm (.binary .ne (.var "lastBidder") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_createBid_lastBidder, evalExpr_settleAuction_zeroAddr,
    EvalResult.bind, bind, evalBinaryOp?]
  have hbeq :
      (Value.address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    rw [Value.address.injEq] at h
    exact hbidder h
  simp [hbeq]

theorem auctionCreateBidLastBidderStore_auction_get? (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidLastBidderStore evm I).get? "auction" = none := by
  simp [auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore, auctionCreateBidStore]

theorem auctionCreateBidLastBidderStore_timeBuffer_get? (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidLastBidderStore evm I).get? timeBufferRef.base = none := by
  simp [auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore, auctionCreateBidStore,
    timeBufferRef]

theorem auctionCreateBidLastBidderStore_status_get? (evm : EVM.State) (I : ExecutionEnv) :
    (auctionCreateBidLastBidderStore evm I).get? statusRef.base = none := by
  simp [auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore, auctionCreateBidStore,
    statusRef]

theorem evalExpr_createBid_lastBidderStore_mem_endTime
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm' (auctionMemField "endTime") =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat)) := by
  simp [auctionMemField, auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore,
    auctionSettleAuctionSnapshotValue, auctionSettleAuctionSnapshotFields, evalExpr?,
    EvalResult.ofOption, lookupField?, lookupAssoc, Std.HashMap.getElem_insert,
    Std.HashMap.getElem_insert_self, EvalResult.bind, bind]

theorem evalExpr_createBid_timeBuffer_lastBidderStore
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
        evm' (.storage timeBufferRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨203⟩).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionCreateBidLastBidderStore evm I }
      evm' timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := auctionCreateBidLastBidderStore_timeBuffer_get? evm I) (her := her)
    (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm' ⟨203⟩)

theorem evalExpr_createBid_timeBuffer_lastBidderStore_insert_extended
    (evm evm' : EVM.State) (I : ExecutionEnv) (extended : Bool) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evm I).insert "extended"
            (.bool extended) }
        evm' (.storage timeBufferRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨203⟩).toNat)) := by
  have hbase :
      ((auctionCreateBidLastBidderStore evm I).insert "extended" (.bool extended)).get?
          timeBufferRef.base =
        none := by
    simp [auctionCreateBidLastBidderStore, auctionCreateBidSnapshotStore, auctionCreateBidStore,
      timeBufferRef]
  have her : evalStorageRef auctionConfig
      { contract := auctionContract,
        locals := (auctionCreateBidLastBidderStore evm I).insert "extended"
          (.bool extended) }
      evm' timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := hbase) (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by simpa using auctionStorageLocLoad_uint256 evm' ⟨203⟩)

theorem evalExpr_createBid_extended_false
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
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evmSnapshot I }
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
  simp only [evalExpr?, evalExpr_createBid_lastBidderStore_mem_endTime,
    evalExpr_settleAuction_now, evalExpr_createBid_timeBuffer_lastBidderStore,
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

theorem evalExpr_createBid_extended_true
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
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evmSnapshot I }
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
  simp only [evalExpr?, evalExpr_createBid_lastBidderStore_mem_endTime,
    evalExpr_settleAuction_now, evalExpr_createBid_timeBuffer_lastBidderStore,
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

def auctionCreateBidExtendedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨210⟩
    (UInt256.add (UInt256.ofNat I.header.timestamp) (auctionSlotWord ⟨203⟩ σ I))

def auctionCreateBidExtendedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨210⟩
    (UInt256.add (UInt256.ofNat evm.executionEnv.header.timestamp)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨203⟩))

theorem evalExpr_createBid_extendedEndTime
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (haddFit :
      (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat <
        UInt256.size) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evmSnapshot I }
        evmCurrent
        (u256 (.binary .add now (.storage timeBufferRef))) =
      .ok (.int (Int.ofNat
        (UInt256.add (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩)).toNat)) := by
    simp only [evalExpr?, evalExpr_settleAuction_now,
      evalExpr_createBid_timeBuffer_lastBidderStore, u256, EvalResult.bind, bind, evalBinaryOp?]
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

theorem auctionCreateBidAssignEndTimeExtended
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionCreateBidLastBidderStore evmSnapshot I }
        evmCurrent .storage (aField "endTime")
        (.int (Int.ofNat
          (UInt256.add (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)
            (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩)).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionCreateBidLastBidderStore evmSnapshot I },
        auctionCreateBidExtendedState evmCurrent) := by
  exact auctionCreateAuctionAssignUint256Field evmCurrent
    (auctionCreateBidLastBidderStore evmSnapshot I) "endTime" ⟨210⟩
    (UInt256.add (UInt256.ofNat evmCurrent.executionEnv.header.timestamp)
      (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩))
    (auctionCreateBidLastBidderStore_auction_get? evmSnapshot I)
    (by decide) (by rfl)

theorem evalExpr_createBid_extendedEndTime_revert
    (evmSnapshot evmCurrent : EVM.State) (I : ExecutionEnv)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat evmCurrent.executionEnv.header.timestamp).toNat +
          (Solm.EVM.storageLoad evmCurrent evmCurrent.executionEnv.codeOwner ⟨203⟩).toNat) :
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := (auctionCreateBidLastBidderStore evmSnapshot I).insert "extended" (.bool true) }
        evmCurrent
        (u256 (.binary .add now (.storage timeBufferRef))) =
      .revert := by
  simp only [evalExpr?, evalExpr_settleAuction_now,
    evalExpr_createBid_timeBuffer_lastBidderStore_insert_extended, u256, EvalResult.bind,
    bind, evalBinaryOp?]
  simp [uint256Int]
  intro _
  exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)

theorem auctionCreateBidTransitionReturns_noExtension_noRefund (evm : EVM.State)
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
    (hbidderZero :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnotExtended :
      (Solm.EVM.storageLoad
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.codeOwner
          ⟨203⟩).toNat ≤
        (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.header.timestamp)).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            (auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "extended" (.bool false) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let evmAmount := auctionCreateBidAmountState evmEnter
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsLast.insert "extended" (.bool false)
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
    (ExecStmt.iteFalse (evalExpr_createBid_lastBidder_ne_zero_false evmEnter I hbidderZero)
      ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmEnter localsLast)
      (auctionCreateAuctionAssignUint256Field evmEnter localsLast "amount" ⟨208⟩
        evmEnter.executionEnv.weiValue
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsLast)
      (auctionCreateAuctionAssignAddressField evmAmount localsLast "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_false evmEnter evmBidder I
      (by
        simpa [evmBidder, evmAmount, auctionCreateBidBidderState,
          auctionCreateBidAmountState, storageStore_executionEnv] using Nat.le_of_lt htime)
      hnotExtended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (by simp [evalExpr?, EvalResult.ofOption])
      ExecBlock.nil) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered
      evmBidder localsExtended)
    (auctionCreateBidAssignStatusNotEntered
        evmBidder localsExtended
        (by
          simp [localsExtended, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil

theorem auctionCreateBidTransitionReturns_extension_noRefund (evm : EVM.State)
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
    (hbidderZero :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (haddExtFit :
      (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.codeOwner
          ⟨203⟩).toNat <
        UInt256.size) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body
      (.returned
        { contract := auctionContract,
          locals :=
            (auctionCreateBidLastBidderStore (auctionCreateBidEnterState evm) I).insert
              "extended" (.bool true) }
        (auctionCreateBidUnlockedState
          (auctionCreateBidExtendedState
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))))
        none) := by
  let evmEnter := auctionCreateBidEnterState evm
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let evmAmount := auctionCreateBidAmountState evmEnter
  let evmBidder := auctionCreateBidBidderState evmAmount
  let evmExtended := auctionCreateBidExtendedState evmBidder
  let localsExtended := localsLast.insert "extended" (.bool true)
  have hevalEnd :
      evalExpr? auctionConfig { contract := auctionContract, locals := localsExtended }
          evmBidder
          (u256 (.binary .add now (.storage timeBufferRef))) =
        .ok (.int (Int.ofNat
          (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
            (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩)).toNat)) := by
    dsimp [localsExtended, localsLast]
    simp only [evalExpr?, evalExpr_settleAuction_now,
      evalExpr_createBid_timeBuffer_lastBidderStore_insert_extended, u256, EvalResult.bind,
      bind, evalBinaryOp?]
    simp [uint256Int]
    rw [if_neg (by
      apply not_or.mpr
      constructor
      · exact not_lt_of_ge (add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      · exact not_le_of_gt (by
          have hsum :
              Int.ofNat
                ((UInt256.ofNat evmBidder.executionEnv.header.timestamp).toNat +
                  (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner
                    ⟨203⟩).toNat) < Int.ofNat UInt256.size :=
            Int.ofNat_lt.mpr haddExtFit
          simpa [UInt256.size] using hsum))]
    simp only [pure]
    rw [show
        (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
            (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩)).toNat =
          (UInt256.ofNat evmBidder.executionEnv.header.timestamp).toNat +
            (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩).toNat by
      change
        ((UInt256.ofNat evmBidder.executionEnv.header.timestamp +
            Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩).toNat) =
          (UInt256.ofNat evmBidder.executionEnv.header.timestamp).toNat +
            (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩).toNat
      rw [uadd_toNat, Nat.mod_eq_of_lt haddExtFit]]
    simp
  have hassignEnd :
      assignStorageRef? auctionConfig
          { contract := auctionContract, locals := localsExtended }
          evmBidder .storage (aField "endTime")
          (.int (Int.ofNat
            (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
              (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩)).toNat)) =
        .ok ({ contract := auctionContract, locals := localsExtended }, evmExtended) := by
    exact auctionCreateAuctionAssignUint256Field evmBidder
      localsExtended "endTime" ⟨210⟩
      (UInt256.add (UInt256.ofNat evmBidder.executionEnv.header.timestamp)
        (Solm.EVM.storageLoad evmBidder evmBidder.executionEnv.codeOwner ⟨203⟩))
      (by
        simp [localsExtended, localsLast, auctionCreateBidLastBidderStore,
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
    (ExecStmt.iteFalse (evalExpr_createBid_lastBidder_ne_zero_false evmEnter I hbidderZero)
      ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmEnter localsLast)
      (auctionCreateAuctionAssignUint256Field evmEnter localsLast "amount" ⟨208⟩
        evmEnter.executionEnv.weiValue
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsLast)
      (auctionCreateAuctionAssignAddressField evmAmount localsLast "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true evmEnter evmBidder I
      (by
        simpa [evmBidder, evmAmount, auctionCreateBidBidderState,
          auctionCreateBidAmountState, storageStore_executionEnv] using Nat.le_of_lt htime)
      hextended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := auctionContract, locals := localsExtended } evmExtended)
      (by simp [evalExpr?, EvalResult.ofOption]) ?_) ?_
  · exact ExecBlock.consNormal (ExecStmt.assign hevalEnd hassignEnd) ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_notEntered
      evmExtended localsExtended)
    (auctionCreateBidAssignStatusNotEntered
        evmExtended localsExtended
        (by
          simp [localsExtended, localsLast, auctionCreateBidLastBidderStore,
            auctionCreateBidSnapshotStore, auctionCreateBidStore])))
    ExecBlock.nil

theorem auctionCreateBidTransitionReverts_extensionOverflow_noRefund (evm : EVM.State)
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
    (hbidderZero :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hextended :
      (UInt256.sub
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩)
          (UInt256.ofNat
            (auctionCreateBidBidderState
              (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.header.timestamp)).toNat <
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.codeOwner
          ⟨203⟩).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.ofNat
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.header.timestamp).toNat +
        (Solm.EVM.storageLoad
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm)))
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState (auctionCreateBidEnterState evm))).executionEnv.codeOwner
          ⟨203⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let localsLast := auctionCreateBidLastBidderStore evmEnter I
  let evmAmount := auctionCreateBidAmountState evmEnter
  let evmBidder := auctionCreateBidBidderState evmAmount
  let localsExtended := localsLast.insert "extended" (.bool true)
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
    (ExecStmt.iteFalse (evalExpr_createBid_lastBidder_ne_zero_false evmEnter I hbidderZero)
      ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_callvalue evmEnter localsLast)
      (auctionCreateAuctionAssignUint256Field evmEnter localsLast "amount" ⟨208⟩
        evmEnter.executionEnv.weiValue
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_createBid_sender_word evmAmount localsLast)
      (auctionCreateAuctionAssignAddressField evmAmount localsLast "bidder" ⟨211⟩
        (UInt256.ofNat evmAmount.executionEnv.source.val)
        (auctionCreateBidLastBidderStore_auction_get? evmEnter I)
        (by simpa [auctionSourceWord] using auctionSourceWord_canonical evmAmount.executionEnv)
        (by decide) (by rfl))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createBid_extended_true evmEnter evmBidder I
      (by
        simpa [evmBidder, evmAmount, auctionCreateBidBidderState,
          auctionCreateBidAmountState, storageStore_executionEnv] using Nat.le_of_lt htime)
      hextended)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue
    (result := .reverted)
    (by simp [evalExpr?, EvalResult.ofOption]) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (by
        simpa [localsExtended, localsLast] using
          evalExpr_createBid_extendedEndTime_revert evmEnter evmBidder I hover))

theorem auctionCreateBid_noExtension_noRefund_bidderAccounts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (auctionCreateBidBidderMap
        (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ_evm I) I) I)
      (auctionCreateBidBidderState
        (auctionCreateBidAmountState
          (auctionCreateBidEnterState
            (initState cA gh bl σ_solm σ₀ g A I)))).accountMap := by
  let σEnterEvm := auctionCreateBidEnterMap σ_evm I
  let σEnterSolm := auctionCreateBidEnterMap σ_solm I
  let σAmountEvm := auctionCreateBidAmountMap σEnterEvm I
  let σAmountSolm := auctionCreateBidAmountMap σEnterSolm I
  let σBidderEvm := auctionCreateBidBidderMap σAmountEvm I
  let σBidderSolm := auctionCreateBidBidderMap σAmountSolm I
  have henter : accountMapEquiv σEnterEvm σEnterSolm := by
    simpa [σEnterEvm, σEnterSolm, auctionCreateBidEnterMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ hAccounts
  have hamount : accountMapEquiv σAmountEvm σAmountSolm := by
    simpa [σAmountEvm, σAmountSolm, auctionCreateBidAmountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨208⟩ I.weiValue henter
  have hslot211 :
      auctionSlotWord ⟨211⟩ σAmountEvm I = auctionSlotWord ⟨211⟩ σAmountSolm I :=
    accountMapEquiv_storage_findD hamount I.codeOwner ⟨211⟩ ⟨0⟩
  have hbidderVal :
      setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountEvm I) (auctionSourceWord I) =
        setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountSolm I) (auctionSourceWord I) := by
    rw [hslot211]
  have hbidder : accountMapEquiv σBidderEvm σBidderSolm := by
    unfold σBidderEvm σBidderSolm auctionCreateBidBidderMap
    rw [hbidderVal]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountSolm I) (auctionSourceWord I))
      hamount
  simpa [σEnterEvm, σEnterSolm, σAmountEvm, σAmountSolm, σBidderEvm, σBidderSolm,
    auctionCreateBidEnterMap, auctionCreateBidAmountMap, auctionCreateBidBidderMap,
    auctionCreateBidEnterState, auctionCreateBidAmountState, auctionCreateBidBidderState,
    initState, auctionSlotWord, auctionSourceWord, Solm.EVM.storageLoad, State.lookupAccount,
    storageStore_accountMap, storageStore_executionEnv] using hbidder

theorem auctionCreateBid_noExtension_noRefund_postAccounts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap
          (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ_evm I) I) I) I)
      (auctionCreateBidUnlockedState
        (auctionCreateBidBidderState
          (auctionCreateBidAmountState
            (auctionCreateBidEnterState
              (initState cA gh bl σ_solm σ₀ g A I))))).accountMap := by
  let σEnterEvm := auctionCreateBidEnterMap σ_evm I
  let σEnterSolm := auctionCreateBidEnterMap σ_solm I
  let σAmountEvm := auctionCreateBidAmountMap σEnterEvm I
  let σAmountSolm := auctionCreateBidAmountMap σEnterSolm I
  let σBidderEvm := auctionCreateBidBidderMap σAmountEvm I
  let σBidderSolm := auctionCreateBidBidderMap σAmountSolm I
  have henter : accountMapEquiv σEnterEvm σEnterSolm := by
    simpa [σEnterEvm, σEnterSolm, auctionCreateBidEnterMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ hAccounts
  have hamount : accountMapEquiv σAmountEvm σAmountSolm := by
    simpa [σAmountEvm, σAmountSolm, auctionCreateBidAmountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨208⟩ I.weiValue henter
  have hslot211 :
      auctionSlotWord ⟨211⟩ σAmountEvm I = auctionSlotWord ⟨211⟩ σAmountSolm I :=
    accountMapEquiv_storage_findD hamount I.codeOwner ⟨211⟩ ⟨0⟩
  have hbidderVal :
      setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountEvm I) (auctionSourceWord I) =
        setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountSolm I) (auctionSourceWord I) := by
    rw [hslot211]
  have hbidder : accountMapEquiv σBidderEvm σBidderSolm := by
    unfold σBidderEvm σBidderSolm auctionCreateBidBidderMap
    rw [hbidderVal]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (setAddressOffset0Word (auctionSlotWord ⟨211⟩ σAmountSolm I) (auctionSourceWord I))
      hamount
  have hunlocked :
      accountMapEquiv (auctionCreateBidUnlockedMap σBidderEvm I)
        (auctionCreateBidUnlockedMap σBidderSolm I) := by
    simpa [auctionCreateBidUnlockedMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hbidder
  simpa [σEnterEvm, σEnterSolm, σAmountEvm, σAmountSolm, σBidderEvm, σBidderSolm,
    auctionCreateBidEnterMap, auctionCreateBidAmountMap, auctionCreateBidBidderMap,
    auctionCreateBidUnlockedMap, auctionCreateBidEnterState, auctionCreateBidAmountState,
    auctionCreateBidBidderState, auctionCreateBidUnlockedState, initState, auctionSlotWord,
    auctionSourceWord, Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
    storageStore_executionEnv] using hunlocked

theorem auctionCreateBid_extension_noRefund_postAccounts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (auctionCreateBidUnlockedMap
        (auctionCreateBidExtendedMap
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ_evm I) I) I) I) I)
      (auctionCreateBidUnlockedState
        (auctionCreateBidExtendedState
          (auctionCreateBidBidderState
            (auctionCreateBidAmountState
              (auctionCreateBidEnterState
                (initState cA gh bl σ_solm σ₀ g A I)))))).accountMap := by
  let σEnterEvm := auctionCreateBidEnterMap σ_evm I
  let σAmountEvm := auctionCreateBidAmountMap σEnterEvm I
  let σBidderEvm := auctionCreateBidBidderMap σAmountEvm I
  let evmEnterSolm := auctionCreateBidEnterState (initState cA gh bl σ_solm σ₀ g A I)
  let evmAmountSolm := auctionCreateBidAmountState evmEnterSolm
  let evmBidderSolm := auctionCreateBidBidderState evmAmountSolm
  have hbidder :
      accountMapEquiv σBidderEvm evmBidderSolm.accountMap := by
    simpa [σEnterEvm, σAmountEvm, σBidderEvm, evmEnterSolm, evmAmountSolm,
      evmBidderSolm] using
      auctionCreateBid_noExtension_noRefund_bidderAccounts
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  have htimeBuffer :
      auctionSlotWord ⟨203⟩ σBidderEvm I =
        auctionSlotWord ⟨203⟩ evmBidderSolm.accountMap I :=
    accountMapEquiv_storage_findD hbidder I.codeOwner ⟨203⟩ ⟨0⟩
  have hnewEnd :
      UInt256.add (UInt256.ofNat I.header.timestamp) (auctionSlotWord ⟨203⟩ σBidderEvm I) =
        UInt256.add (UInt256.ofNat I.header.timestamp)
          (auctionSlotWord ⟨203⟩ evmBidderSolm.accountMap I) := by
    rw [htimeBuffer]
  have hextended :
      accountMapEquiv (auctionCreateBidExtendedMap σBidderEvm I)
        (auctionCreateBidExtendedMap evmBidderSolm.accountMap I) := by
    unfold auctionCreateBidExtendedMap
    rw [hnewEnd]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨210⟩
      (UInt256.add (UInt256.ofNat I.header.timestamp)
        (auctionSlotWord ⟨203⟩ evmBidderSolm.accountMap I)) hbidder
  have hunlocked :
      accountMapEquiv
        (auctionCreateBidUnlockedMap (auctionCreateBidExtendedMap σBidderEvm I) I)
        (auctionCreateBidUnlockedMap (auctionCreateBidExtendedMap evmBidderSolm.accountMap I) I) := by
    simpa [auctionCreateBidUnlockedMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hextended
  simpa [σEnterEvm, σAmountEvm, σBidderEvm, evmEnterSolm, evmAmountSolm, evmBidderSolm,
    auctionCreateBidEnterMap, auctionCreateBidAmountMap, auctionCreateBidBidderMap,
    auctionCreateBidExtendedMap, auctionCreateBidUnlockedMap, auctionCreateBidEnterState,
    auctionCreateBidAmountState, auctionCreateBidBidderState, auctionCreateBidExtendedState,
    auctionCreateBidUnlockedState, initState, auctionSlotWord, auctionSourceWord,
    Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
    storageStore_executionEnv] using hunlocked

theorem auctionCreateBidCheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5723⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [hsubNat]; omega)
  have rd5729₀ := evm_run h with [
    jumpdest, dup2, dup2, sub, dup2, dup2, gt]
  have rd5729 := rd5729₀
  rw [hgt] at rd5729
  have rd5730₀ := evm_run rd5729 with [iszero]
  have rd5730 := rd5730₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd5730
  have rd4886 := evm_run rd5730 with [
    push2 ⟨4886⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd4886 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

theorem auctionCreateBidX_toLastBidderCheck {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1681⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
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
  have hminReqLe : minRequired.toNat ≤ I.weiValue.toNat := by
    rw [hrequiredNat]
    simpa [amount, minBid, minBidRaw, σ1] using hbidOk
  have hlt : UInt256.lt I.weiValue minRequired = ⟨0⟩ :=
    ult_zero hminReqLe
  have hcond : UInt256.isZero (UInt256.lt I.weiValue minRequired) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1681 := evm_run rd1562' with [
    jumpdest, callvalue, lt, iszero, push2 ⟨1681⟩, jumpiT hcond (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd1681⟩

theorem auctionCreateBidX_toNoRefund {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
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
    raw mload 0 bidder (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and]
  have hmask : UInt256.land bidder
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = ⟨0⟩ := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide]
    rw [show bidder = ⟨0⟩ by simpa [bidder, packed, σ1] using hbidderZero]
    native_decide
  have rd1697 := rd1697₀
  rw [hmask] at rd1697
  have rd1698₀ := evm_run rd1697 with [iszero]
  have rd1698 := rd1698₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1698
  have rd1715 := evm_run rd1698 with [
    push2 ⟨1715⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, hbidderZero] using rd1715⟩

theorem auctionCreateBidX_toExtensionCheck_noRefund {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
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
  obtain ⟨_, _, rd1715⟩ := auctionCreateBidX_toNoRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero hreach
  obtain ⟨_, _, rd1715'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, hbidderZero] using
        rd1715⟩
  have rd1719 := evm_run rd1715' with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720₀⟩ := rd1719.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1720⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σAmount) k C := by
    exact ⟨_, _, by simpa [σAmount, auctionCreateBidAmountMap] using rd1720₀⟩
  have rd1723₀ := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1723₁⟩ := rd1723₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1724⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1724⟩
      [packedAfterAmount, ⟨211⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
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
  obtain ⟨_, _, rd1738₀⟩ := rd1737.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1738⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionCreateBidBidderMap σAmount I) k C := by
    exact ⟨_, _, by
      simpa [auctionCreateBidBidderMap, packedAfterAmount, σAmount] using rd1738₀⟩
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount,
      hbidderZero] using rd1738⟩

theorem auctionCreateBidX_toExtensionDecision_noRefund {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp),
        auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I,
        ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
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
  obtain ⟨_, _, rd1738⟩ := auctionCreateBidX_toExtensionCheck_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero hreach
  obtain ⟨_, _, rd1738'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1738⟩
      [⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        hbidderZero] using rd1738⟩
  obtain ⟨_, _, rd1740₀⟩ := (evm_run rd1738' with [push1 ⟨203⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd1741⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1741⟩
      [timeBuffer, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by simpa [timeBuffer, auctionSlotWord] using rd1740₀⟩
  have rd1745₀ := evm_run rd1741 with [push1 ⟨96⟩, dup4, add]
  have rd1745 := rd1745₀
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ by decide] at rd1745
  have rd1746 := evm_run rd1745 with [
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd5723 := evm_run rd1746 with [
    push0, swap2, swap1, push2 ⟨1759⟩, swap1, timestamp, swap1, push2 ⟨5723⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidCheckedSubOk
    (a := finish) (b := UInt256.ofNat I.header.timestamp) (ret := ⟨1759⟩)
    (R := [timeBuffer, ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
      auctionSelWord I])
    rd5723 (by simpa [finish, σ1] using Nat.le_of_lt htime) (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      timeBuffer, hbidderZero] using rd1759⟩

theorem auctionCreateBidX_toAuctionBid_noExtension_noRefund {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat ≤
        (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
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
  let timeLeft := UInt256.sub finish (UInt256.ofNat I.header.timestamp)
  obtain ⟨_, _, rd1759⟩ := auctionCreateBidX_toExtensionDecision_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero hreach
  obtain ⟨_, _, rd1759'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [timeLeft, timeBuffer, ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        timeBuffer, timeLeft, hbidderZero] using rd1759⟩
  have hlt : UInt256.lt timeLeft timeBuffer = ⟨0⟩ := by
    apply ult_zero
    simpa [timeLeft, timeBuffer, σBidder, σAmount, σ1] using hnotExtended
  have rd1764₀ := evm_run rd1759' with [jumpdest, lt, swap1, pop, dup1, iszero]
  have rd1764 := rd1764₀
  rw [hlt] at rd1764
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1764
  have rd1792 := evm_run rd1764 with [push2 ⟨1792⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      timeBuffer, timeLeft, hbidderZero] using rd1792⟩

noncomputable def auctionCreateBidAuctionBidMem0
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32

noncomputable def auctionCreateBidAuctionBidMem1
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0
    (auctionCreateBidAuctionBidMem0 noun amount start finish bidder settled I) 352 32

noncomputable def auctionCreateBidAuctionBidMem2
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray extended).write 0
    (auctionCreateBidAuctionBidMem1 noun amount start finish bidder settled I) 384 32

theorem auctionCreateBidAuctionBidMem0_size
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionBidMem0 noun amount start finish bidder settled I).size = 352 := by
  unfold auctionCreateBidAuctionBidMem0
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
    (auctionSourceWord I) 320 320 352
    (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidAuctionBidMem1_size
    (noun amount start finish bidder settled : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionBidMem1 noun amount start finish bidder settled I).size = 384 := by
  unfold auctionCreateBidAuctionBidMem1
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidAuctionBidMem0 noun amount start finish bidder settled I)
    I.weiValue 352 352 384
    (auctionCreateBidAuctionBidMem0_size noun amount start finish bidder settled I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidAuctionBidMem2_size
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled extended I).size =
      416 := by
  unfold auctionCreateBidAuctionBidMem2
  exact toByteArray_write32_size_of_ge
    (auctionCreateBidAuctionBidMem1 noun amount start finish bidder settled I)
    extended 384 384 416
    (auctionCreateBidAuctionBidMem1_size noun amount start finish bidder settled I)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionCreateBidAuctionBidMem2_read64
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled extended I).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionCreateBidAuctionBidMem2
  rw [toByteArray_write_read_below_of_gap extended _ 384 64
    (by rw [auctionCreateBidAuctionBidMem1_size]; omega) (by omega)
    (by rw [auctionCreateBidAuctionBidMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidAuctionBidMem1
  rw [toByteArray_write_read_below_of_gap I.weiValue _ 352 64
    (by rw [auctionCreateBidAuctionBidMem0_size]; omega) (by omega)
    (by rw [auctionCreateBidAuctionBidMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionCreateBidAuctionBidMem0
  rw [toByteArray_write_read_below_of_gap (auctionSourceWord I) _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionCreateBidAuctionBidMem2_mload64
    (noun amount start finish bidder settled extended : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled extended I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled extended I)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionCreateBidAuctionBidMem2_size]; decide)
    (auctionCreateBidAuctionBidMem2_read64 noun amount start finish bidder settled extended I)
    (by decide) (by decide)

def auctionCreateBidAuctionBidTopic : UInt256 :=
  ⟨0x1159164c56f277e6fc99c11731bd380e0347deb969b75523398734c252706ea3⟩

theorem auctionCreateBidX_toAuctionBidLog_noExtension_noRefund
    {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat ≤
        (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic,
        auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I,
        ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2
        (auctionAuctionNounWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionStartWord (auctionCreateBidEnterMap σ I) I)
        (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I))
        ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty
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
  obtain ⟨_, _, rd1792⟩ := auctionCreateBidX_toAuctionBid_noExtension_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero
    hnotExtended hreach
  obtain ⟨_, _, rd1792'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1792⟩
      [⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        hbidderZero] using rd1792⟩
  have rd1794 := evm_run rd1792' with [
    jumpdest, dup3,
    raw mload 0 noun (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload128 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    caller, dup2]
  have rd1801 := evm_run rd1794 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem0 noun amount start finish bidder settled I)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1807₀ := evm_run rd1801 with [callvalue, push1 ⟨32⟩, dup3, add]
  have rd1807 := rd1807₀
  rw [show (⟨320⟩ : UInt256) + ⟨32⟩ = ⟨352⟩ by decide] at rd1807
  have rd1808 := evm_run rd1807 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem1 noun amount start finish bidder settled I)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1814₀ := evm_run rd1808 with [dup4, iszero, iszero, dup2, dup4, add]
  have rd1814 := rd1814₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1814
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd1814
  rw [show (⟨64⟩ : UInt256) + ⟨320⟩ = ⟨384⟩ by decide] at rd1814
  have rd1815 := evm_run rd1814 with [
    raw mstore 3 (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1816 := evm_run rd1815 with [swap1]
  have rd1817₀ := evm_run rd1816 with [
    raw mload 0 ⟨320⟩ (UInt256.ofNat 13) (by decide)
      mem_cost
      (auctionCreateBidAuctionBidMem2_mload64 noun amount start finish bidder settled ⟨0⟩ I)
      (by decide) (by evm_ov)]
  have rd1850 := rd1817₀.pushConst auctionCreateBidAuctionBidTopic
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd1858₀ := evm_run rd1850 with [swap2, dup2, swap1, sub, push1 ⟨96⟩, add, swap1]
  have rd1858 := rd1858₀
  rw [show UInt256.sub (⟨320⟩ : UInt256) ⟨320⟩ = ⟨0⟩ by decide] at rd1858
  rw [show (⟨96⟩ : UInt256) + ⟨0⟩ = ⟨96⟩ by decide] at rd1858
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
      hbidderZero] using rd1858⟩

theorem auctionCreateBidX_success_noExtension_noRefund
    {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionCreateBidEnterMap σ I) I) =
        ⟨0⟩)
    (hnotExtended :
      (auctionSlotWord ⟨203⟩
          (auctionCreateBidBidderMap
            (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I).toNat ≤
        (UInt256.sub (auctionAuctionEndWord (auctionCreateBidEnterMap σ I) I)
          (UInt256.ofNat I.header.timestamp)).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1165⟩
      [auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionCreateBidUnlockedMap
        (auctionCreateBidBidderMap
          (auctionCreateBidAmountMap (auctionCreateBidEnterMap σ I) I) I) I)
      ByteArray.empty := by
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
  obtain ⟨_, _, rd1858⟩ := auctionCreateBidX_toAuctionBidLog_noExtension_noRefund
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hstatus hnoun htime hreserve hmulFit haddFit hbidOk hbidderZero
    hnotExtended hreach
  obtain ⟨_, _, rd1858'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      [⟨320⟩, ⟨96⟩, auctionCreateBidAuctionBidTopic, noun,
        ⟨0⟩, ⟨0⟩, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty (cA, σBidder) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, σAmount, σBidder,
        hbidderZero] using rd1858⟩
  have rd1859 := Auction.RD.log2 0 (UInt256.ofNat 13) rd1858'
    (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  have rd1864₀ := evm_run rd1859 with [dup1, iszero]
  have rd1864 := rd1864₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1864
  have rd1923 := evm_run rd1864 with [
    push2 ⟨1923⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1930 := evm_run rd1923 with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931₀⟩ := rd1930.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
      [⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionCreateBidAuctionBidMem2 noun amount start finish bidder settled ⟨0⟩ I)
      (UInt256.ofNat 13) ByteArray.empty (cA, auctionCreateBidUnlockedMap σBidder I) k C := by
    exact ⟨_, _, by simpa [auctionCreateBidUnlockedMap] using rd1931₀⟩
  have rd413 := evm_run rd1931 with [pop, pop, jump (by jump_dest), jumpdest]
  exact rd413.stop (by decide) (by evm_ov)

end Auction
