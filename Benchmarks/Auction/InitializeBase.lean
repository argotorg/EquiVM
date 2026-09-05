import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionInitializeNounsWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev auctionInitializeWethWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev auctionInitializeTimeBufferWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev auctionInitializeReservePriceWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev auctionInitializeMinBidIncrementPercentageWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 132

abbrev auctionInitializeDurationWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 164

def auctionInitializeStore (I : ExecutionEnv) : Store :=
  let s0 : Store := ∅
  let s1 := s0.insert "_nouns"
    (.address (AccountAddress.ofNat (auctionInitializeNounsWord I).toNat))
  let s2 := s1.insert "_weth"
    (.address (AccountAddress.ofNat (auctionInitializeWethWord I).toNat))
  let s3 := s2.insert "_timeBuffer"
    (.int (Int.ofNat (auctionInitializeTimeBufferWord I).toNat))
  let s4 := s3.insert "_reservePrice"
    (.int (Int.ofNat (auctionInitializeReservePriceWord I).toNat))
  let s5 := s4.insert "_minBidIncrementPercentage"
    (.int (Int.ofNat (auctionInitializeMinBidIncrementPercentageWord I).toNat))
  s5.insert "_duration" (.int (Int.ofNat (auctionInitializeDurationWord I).toNat))

theorem auctionInitializeStore_nounsArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_nouns" =
      some (.address (AccountAddress.ofNat (auctionInitializeNounsWord I).toNat)) := by
  rw [auctionInitializeStore]
  repeat rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem auctionInitializeStore_wethArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_weth" =
      some (.address (AccountAddress.ofNat (auctionInitializeWethWord I).toNat)) := by
  rw [auctionInitializeStore]
  repeat rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem auctionInitializeStore_timeBufferArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_timeBuffer" =
      some (.int (Int.ofNat (auctionInitializeTimeBufferWord I).toNat)) := by
  rw [auctionInitializeStore]
  repeat rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem auctionInitializeStore_reservePriceArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_reservePrice" =
      some (.int (Int.ofNat (auctionInitializeReservePriceWord I).toNat)) := by
  rw [auctionInitializeStore]
  repeat rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem auctionInitializeStore_minBidIncrementPercentageArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_minBidIncrementPercentage" =
      some (.int (Int.ofNat (auctionInitializeMinBidIncrementPercentageWord I).toNat)) := by
  rw [auctionInitializeStore]
  repeat rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem auctionInitializeStore_durationArg (I : ExecutionEnv) :
    (auctionInitializeStore I).get? "_duration" =
      some (.int (Int.ofNat (auctionInitializeDurationWord I).toNat)) := by
  rw [auctionInitializeStore]
  exact store_get_self _ _ _

theorem auctionInitializeStore_base_none (I : ExecutionEnv) {x : Ident}
    (hx : x ∈ ["_initialized", "_initializing", "_paused", "_status", "_owner", "nouns",
      "weth", "timeBuffer", "reservePrice", "minBidIncrementPercentage", "duration"]) :
    (auctionInitializeStore I).get? x = none := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [auctionInitializeStore]
    repeat rw [store_get_ne _ _ (by decide)]
    simp

def auctionInitializeTopStore (I : ExecutionEnv) (b : Bool) : Store :=
  (auctionInitializeStore I).insert "isTopLevelCall" (.bool b)

theorem auctionInitializeTopStore_base_none (I : ExecutionEnv) (b : Bool) {x : Ident}
    (hx : x ∈ ["_initialized", "_initializing", "_paused", "_status", "_owner", "nouns",
      "weth", "timeBuffer", "reservePrice", "minBidIncrementPercentage", "duration"]) :
    (auctionInitializeTopStore I b).get? x = none := by
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide)]
  exact auctionInitializeStore_base_none I hx

def auctionInitializingByte (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨256⟩) ⟨255⟩

def auctionInitializedByte (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩

theorem evalExpr_initialize_initializing_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none)
    (hzero : auctionInitializingByte evm = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
        evm (.storage initializingRef) = .ok (.bool false) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals }
      evm initializingRef = .ok { base := "_initializing", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializingRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initializing", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar_value (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  simpa [auctionInitializingByte] using
    auctionStorageLocLoad_bool_offset_false evm ⟨0⟩ (⟨1, by decide⟩ : Fin 32) hzero

theorem evalExpr_initialize_initializing_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none)
    (hnz : auctionInitializingByte evm ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
        evm (.storage initializingRef) = .ok (.bool true) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals }
      evm initializingRef = .ok { base := "_initializing", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializingRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initializing", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar_value (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  simpa [auctionInitializingByte] using
    auctionStorageLocLoad_bool_offset_true evm ⟨0⟩ (⟨1, by decide⟩ : Fin 32) hnz

theorem evalExpr_initialize_initialized_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initialized" = none)
    (hzero : auctionInitializedByte evm = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
        evm (.storage initializedRef) = .ok (.bool false) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals }
      evm initializedRef = .ok { base := "_initialized", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initialized", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar_value (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  simpa [auctionInitializedByte, auctionBoolLoc, boolOffset0Loc] using
    auctionStorageLocLoad_bool_offset0_false evm ⟨0⟩ hzero

theorem evalExpr_initialize_initialized_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initialized" = none)
    (hnz : auctionInitializedByte evm ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals }
        evm (.storage initializedRef) = .ok (.bool true) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := locals }
      evm initializedRef = .ok { base := "_initialized", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initialized", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar_value (t := .bool) (hbase := hbase) (her := her) (hty := hty)
    (hloc := by rfl)]
  simpa [auctionInitializedByte, auctionBoolLoc, boolOffset0Loc] using
    auctionStorageLocLoad_bool_offset0_true evm ⟨0⟩ hnz

theorem evalExpr_initialize_guard_true_nested (evm : EVM.State) (locals : Store)
    (hbaseI : locals.get? "_initializing" = none)
    (hnz : auctionInitializingByte evm ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_initialize_initializing_true evm locals hbaseI hnz]
  rfl

theorem evalExpr_initialize_guard_true_top (evm : EVM.State) (locals : Store)
    (hbaseI : locals.get? "_initializing" = none)
    (hbaseD : locals.get? "_initialized" = none)
    (hinit0 : auctionInitializingByte evm = ⟨0⟩)
    (hized0 : auctionInitializedByte evm = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_initialize_initializing_false evm locals hbaseI hinit0,
    evalExpr_initialize_initialized_false evm locals hbaseD hized0, evalUnaryOp?]
  rfl

theorem evalExpr_initialize_guard_false_initialized (evm : EVM.State) (locals : Store)
    (hbaseI : locals.get? "_initializing" = none)
    (hbaseD : locals.get? "_initialized" = none)
    (hinit0 : auctionInitializingByte evm = ⟨0⟩)
    (hizednz : auctionInitializedByte evm ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_initialize_initializing_false evm locals hbaseI hinit0,
    evalExpr_initialize_initialized_true evm locals hbaseD hizednz, evalUnaryOp?]
  rfl

def auctionInitializeSetInitializingTrueState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (auctionSetBoolOffset1TrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

def auctionInitializeSetInitializedTrueState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨1⟩)

def auctionInitializeSetInitializingFalseState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (auctionSetBoolOffset1FalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

theorem auctionInitializeAssignInitializingTrue (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        initializingRef (.bool true) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetInitializingTrueState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      initializingRef = .ok { base := "_initializing", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializingRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initializing", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionInitializeSetInitializingTrueState evm)
    (slot := initializingRef) (er := { base := "_initializing", steps := [] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨0⟩ 1) (value := .bool true)
    (auctionInitializeTopStore_base_none I b (by simp [initializingRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetInitializingTrueState] using
        auctionStorageLocStore_bool_true_offset1 evm ⟨0⟩)

theorem auctionInitializeAssignInitializedTrue (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        initializedRef (.bool true) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetInitializedTrueState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      initializedRef = .ok { base := "_initialized", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initialized", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionInitializeSetInitializedTrueState evm)
    (slot := initializedRef) (er := { base := "_initialized", steps := [] })
    (ty := .elem .bool) (loc := auctionBoolLoc ⟨0⟩) (value := .bool true)
    (auctionInitializeTopStore_base_none I b (by simp [initializedRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetInitializedTrueState, auctionBoolLoc, boolOffset0Loc] using
        auctionStorageLocStore_bool_true_offset0 evm ⟨0⟩)

theorem auctionInitializeAssignInitializingFalse (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        initializingRef (.bool false) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetInitializingFalseState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      initializingRef = .ok { base := "_initializing", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, initializingRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_initializing", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionInitializeSetInitializingFalseState evm)
    (slot := initializingRef) (er := { base := "_initializing", steps := [] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨0⟩ 1) (value := .bool false)
    (auctionInitializeTopStore_base_none I b (by simp [initializingRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetInitializingFalseState] using
        auctionStorageLocStore_bool_false_offset1 evm ⟨0⟩)

def auctionInitializeSetStatusState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ ⟨1⟩

def auctionInitializeSetAddressState (evm : EVM.State) (slot val : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)

def auctionInitializeSetUint256State (evm : EVM.State) (slot val : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val

def auctionInitializeSetMinBidState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨205⟩
    (auctionSetUint8Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨205⟩)
      (auctionInitializeMinBidIncrementPercentageWord I))

theorem evalExpr_initialize_arg_nouns (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_nouns") =
        .ok (.address (AccountAddress.ofNat (auctionInitializeNounsWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_nounsArg]

theorem evalExpr_initialize_arg_weth (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_weth") =
        .ok (.address (AccountAddress.ofNat (auctionInitializeWethWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_wethArg]

theorem evalExpr_initialize_arg_timeBuffer (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_timeBuffer") =
        .ok (.int (Int.ofNat (auctionInitializeTimeBufferWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_timeBufferArg]

theorem evalExpr_initialize_arg_reservePrice (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_reservePrice") =
        .ok (.int (Int.ofNat (auctionInitializeReservePriceWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_reservePriceArg]

theorem evalExpr_initialize_arg_minBid (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_minBidIncrementPercentage") =
        .ok (.int (Int.ofNat (auctionInitializeMinBidIncrementPercentageWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_minBidIncrementPercentageArg]

theorem evalExpr_initialize_arg_duration (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "_duration") =
        .ok (.int (Int.ofNat (auctionInitializeDurationWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_ne _ _ (by decide)]
  rw [auctionInitializeStore_durationArg]

theorem evalExpr_initialize_isTopLevelCall (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.var "isTopLevelCall") = .ok (.bool b) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [auctionInitializeTopStore]
  rw [store_get_self]

theorem auctionInitializeAssignPausedFalse (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        pausedRef (.bool false) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionUnpausePostState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionUnpausePostState evm) (slot := pausedRef)
    (er := { base := "_paused", steps := [] }) (ty := .elem .bool)
    (loc := auctionBoolLoc ⟨51⟩) (value := .bool false)
    (auctionInitializeTopStore_base_none I b (by simp [pausedRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionUnpausePostState, auctionBoolLoc, boolOffset0Loc, auctionPausedSetFalseWord] using
        auctionStorageLocStore_bool_false_offset0 evm ⟨51⟩)

theorem auctionInitializeAssignStatus (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        statusRef (.int 1) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetStatusState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      statusRef = .ok { base := "_status", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, statusRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_status", steps := [] } : EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionInitializeSetStatusState evm) (slot := statusRef)
    (er := { base := "_status", steps := [] }) (ty := .elem (.int uint256Int))
    (loc := auctionUint256Loc ⟨101⟩) (n := 1)
    (auctionInitializeTopStore_base_none I b (by simp [statusRef])) her hty (by rfl)
    (by simpa [auctionInitializeSetStatusState] using
      auctionStorageLocStore_uint256 evm ⟨101⟩ ⟨1⟩)

theorem auctionInitializeAssignOwner (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        ownerRef (.address evm.executionEnv.source) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetAddressState evm ⟨151⟩ (auctionSourceWord evm.executionEnv)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have haddr : (.address evm.executionEnv.source : Value) =
      .address (AccountAddress.ofNat (auctionSourceWord evm.executionEnv).toNat) := by
    rw [auctionSource_ofNat]
  rw [haddr]
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetAddressState evm ⟨151⟩ (auctionSourceWord evm.executionEnv))
    (slot := ownerRef) (er := { base := "_owner", steps := [] }) (ty := .elem .address)
    (loc := auctionAddrLoc ⟨151⟩)
    (value := .address (AccountAddress.ofNat (auctionSourceWord evm.executionEnv).toNat))
    (auctionInitializeTopStore_base_none I b (by simp [ownerRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetAddressState] using
        auctionStorageLocStore_address_offset0 evm ⟨151⟩ (auctionSourceWord evm.executionEnv)
          (auctionSourceWord_canonical evm.executionEnv))

theorem auctionInitializeAssignPausedTrue (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        pausedRef (.bool true) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionPausePostState evm) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionPausePostState evm) (slot := pausedRef)
    (er := { base := "_paused", steps := [] }) (ty := .elem .bool)
    (loc := auctionBoolLoc ⟨51⟩) (value := .bool true)
    (auctionInitializeTopStore_base_none I b (by simp [pausedRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionPausePostState, auctionBoolLoc, boolOffset0Loc, auctionPausedSetTrueWord,
        setBoolOffset0Word] using
        auctionStorageLocStore_bool_true_offset0 evm ⟨51⟩)

theorem auctionInitializeAssignNouns (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hcanon : (auctionInitializeNounsWord I).toNat < EVM.addressModulus) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        nounsRef (.address (AccountAddress.ofNat (auctionInitializeNounsWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetAddressState evm ⟨201⟩ (auctionInitializeNounsWord I)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      nounsRef = .ok { base := "nouns", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, nounsRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "nouns", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetAddressState evm ⟨201⟩ (auctionInitializeNounsWord I))
    (slot := nounsRef) (er := { base := "nouns", steps := [] }) (ty := .elem .address)
    (loc := auctionAddrLoc ⟨201⟩)
    (value := .address (AccountAddress.ofNat (auctionInitializeNounsWord I).toNat))
    (auctionInitializeTopStore_base_none I b (by simp [nounsRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetAddressState] using
        auctionStorageLocStore_address_offset0 evm ⟨201⟩ (auctionInitializeNounsWord I) hcanon)

theorem auctionInitializeAssignWeth (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hcanon : (auctionInitializeWethWord I).toNat < EVM.addressModulus) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        wethRef (.address (AccountAddress.ofNat (auctionInitializeWethWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetAddressState evm ⟨202⟩ (auctionInitializeWethWord I)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      wethRef = .ok { base := "weth", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, wethRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "weth", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetAddressState evm ⟨202⟩ (auctionInitializeWethWord I))
    (slot := wethRef) (er := { base := "weth", steps := [] }) (ty := .elem .address)
    (loc := auctionAddrLoc ⟨202⟩)
    (value := .address (AccountAddress.ofNat (auctionInitializeWethWord I).toNat))
    (auctionInitializeTopStore_base_none I b (by simp [wethRef])) her hty (by rfl)
    (by trivial)
    (by
      simpa [auctionInitializeSetAddressState] using
        auctionStorageLocStore_address_offset0 evm ⟨202⟩ (auctionInitializeWethWord I) hcanon)

theorem auctionInitializeAssignTimeBuffer (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        timeBufferRef (.int (Int.ofNat (auctionInitializeTimeBufferWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetUint256State evm ⟨203⟩ (auctionInitializeTimeBufferWord I)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      timeBufferRef = .ok { base := "timeBuffer", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "timeBuffer", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetUint256State evm ⟨203⟩ (auctionInitializeTimeBufferWord I))
    (slot := timeBufferRef) (er := { base := "timeBuffer", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc ⟨203⟩)
    (n := Int.ofNat (auctionInitializeTimeBufferWord I).toNat)
    (auctionInitializeTopStore_base_none I b (by simp [timeBufferRef])) her hty (by rfl)
    (by
      simpa [auctionInitializeSetUint256State] using
        auctionStorageLocStore_uint256 evm ⟨203⟩ (auctionInitializeTimeBufferWord I))

theorem auctionInitializeAssignReservePrice (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        reservePriceRef (.int (Int.ofNat (auctionInitializeReservePriceWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetUint256State evm ⟨204⟩ (auctionInitializeReservePriceWord I)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      reservePriceRef = .ok { base := "reservePrice", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, reservePriceRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "reservePrice", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetUint256State evm ⟨204⟩ (auctionInitializeReservePriceWord I))
    (slot := reservePriceRef) (er := { base := "reservePrice", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc ⟨204⟩)
    (n := Int.ofNat (auctionInitializeReservePriceWord I).toNat)
    (auctionInitializeTopStore_base_none I b (by simp [reservePriceRef])) her hty (by rfl)
    (by
      simpa [auctionInitializeSetUint256State] using
        auctionStorageLocStore_uint256 evm ⟨204⟩ (auctionInitializeReservePriceWord I))

theorem auctionInitializeAssignMinBid (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hcanon : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        minBidIncRef (.int (Int.ofNat (auctionInitializeMinBidIncrementPercentageWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetMinBidState evm I) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      minBidIncRef = .ok { base := "minBidIncrementPercentage", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, minBidIncRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "minBidIncrementPercentage", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint8Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm) (evm' := auctionInitializeSetMinBidState evm I) (slot := minBidIncRef)
    (er := { base := "minBidIncrementPercentage", steps := [] })
    (ty := .elem (.int uint8Int)) (loc := auctionUint8LocAt ⟨205⟩ 0)
    (n := Int.ofNat (auctionInitializeMinBidIncrementPercentageWord I).toNat)
    (auctionInitializeTopStore_base_none I b (by simp [minBidIncRef])) her hty (by rfl)
    (by
      simpa [auctionInitializeSetMinBidState, auctionUint8Loc] using
        auctionStorageLocStore_uint8_offset0 evm ⟨205⟩
          (auctionInitializeMinBidIncrementPercentageWord I) hcanon)

theorem auctionInitializeAssignDuration (evm : EVM.State) (I : ExecutionEnv) (b : Bool) :
    assignStorageRef? auctionConfig
        { contract := auctionContract, locals := auctionInitializeTopStore I b } evm .storage
        durationRef (.int (Int.ofNat (auctionInitializeDurationWord I).toNat)) =
      .ok ({ contract := auctionContract, locals := auctionInitializeTopStore I b },
        auctionInitializeSetUint256State evm ⟨206⟩ (auctionInitializeDurationWord I)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm
      durationRef = .ok { base := "duration", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, durationRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "duration", steps := [] } : EvaledStorageRef) =
        some (.elem (.int uint256Int)) := by
    decide
  exact assignStorageRef_storage_scalar (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := auctionInitializeTopStore I b })
    (evm := evm)
    (evm' := auctionInitializeSetUint256State evm ⟨206⟩ (auctionInitializeDurationWord I))
    (slot := durationRef) (er := { base := "duration", steps := [] })
    (ty := .elem (.int uint256Int)) (loc := auctionUint256Loc ⟨206⟩)
    (n := Int.ofNat (auctionInitializeDurationWord I).toNat)
    (auctionInitializeTopStore_base_none I b (by simp [durationRef])) her hty (by rfl)
    (by
      simpa [auctionInitializeSetUint256State] using
        auctionStorageLocStore_uint256 evm ⟨206⟩ (auctionInitializeDurationWord I))

def auctionInitializeCoreStmts : List Stmt :=
  [ .assign .storage pausedRef (.boolLit false),
    .assign .storage statusRef notEntered,
    .assign .storage ownerRef sender,
    .require (.unary .not (.storage pausedRef)),
    .assign .storage pausedRef (.boolLit true),
    .assign .storage nounsRef (.var "_nouns"),
    .assign .storage wethRef (.var "_weth"),
    .assign .storage timeBufferRef (.var "_timeBuffer"),
    .assign .storage reservePriceRef (.var "_reservePrice"),
    .assign .storage minBidIncRef (.var "_minBidIncrementPercentage"),
    .assign .storage durationRef (.var "_duration") ]

def auctionInitializeFinalStmt : Stmt :=
  .ite (.var "isTopLevelCall")
    [ .assign .storage initializingRef (.boolLit false) ] []

def auctionInitializeCorePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let s1 := auctionUnpausePostState evm
  let s2 := auctionInitializeSetStatusState s1
  let s3 := auctionInitializeSetAddressState s2 ⟨151⟩ (auctionSourceWord s2.executionEnv)
  let s4 := auctionPausePostState s3
  let s5 := auctionInitializeSetAddressState s4 ⟨201⟩ (auctionInitializeNounsWord I)
  let s6 := auctionInitializeSetAddressState s5 ⟨202⟩ (auctionInitializeWethWord I)
  let s7 := auctionInitializeSetUint256State s6 ⟨203⟩ (auctionInitializeTimeBufferWord I)
  let s8 := auctionInitializeSetUint256State s7 ⟨204⟩ (auctionInitializeReservePriceWord I)
  let s9 := auctionInitializeSetMinBidState s8 I
  auctionInitializeSetUint256State s9 ⟨206⟩ (auctionInitializeDurationWord I)

def auctionInitializeTopPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  auctionInitializeSetInitializingFalseState
    (auctionInitializeCorePostState
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm)) I)

def auctionInitializeNestedPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  auctionInitializeCorePostState evm I

theorem auctionPausedClearedWord_low_zero (w : UInt256) :
    UInt256.land (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨255⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  rw [packedSetFalseWord_toNat]
  have h255 : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by decide
  rw [h255, nat_land_mask_eq_mod]
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm]
  rw [Nat.mul_mod_right]
  rfl

theorem auctionUnpausePostState_paused_zero (evm : EVM.State) :
    UInt256.land
        (Solm.EVM.storageLoad (auctionUnpausePostState evm)
          (auctionUnpausePostState evm).executionEnv.codeOwner ⟨51⟩) ⟨255⟩ = ⟨0⟩ := by
  unfold auctionUnpausePostState auctionPausedSetFalseWord
  rw [storageStore_executionEnv]
  cases hacc : evm.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      rw [storageStore_absent evm evm.executionEnv.codeOwner
        (by simpa [State.lookupAccount] using hacc)]
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc]
  | some _ =>
      rw [storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner
        (by simpa [State.lookupAccount] using hacc)]
      exact auctionPausedClearedWord_low_zero _

theorem auctionInitializeCorePausedZero (evm : EVM.State) :
    let s1 := auctionUnpausePostState evm
    let s2 := auctionInitializeSetStatusState s1
    let s3 := auctionInitializeSetAddressState s2 ⟨151⟩ (auctionSourceWord s2.executionEnv)
    UInt256.land (Solm.EVM.storageLoad s3 s3.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
      ⟨0⟩ := by
  dsimp only
  unfold auctionInitializeSetAddressState
  rw [storageStore_executionEnv]
  rw [storageLoad_storageStore_ne (hne := by decide)]
  unfold auctionInitializeSetStatusState
  rw [storageStore_executionEnv]
  rw [storageLoad_storageStore_ne (hne := by decide)]
  exact auctionUnpausePostState_paused_zero evm

theorem evalExpr_initialize_paused_false (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.storage pausedRef) = .ok (.bool false) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := auctionInitializeTopStore I b } evm pausedRef =
        .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool)
    (hbase := auctionInitializeTopStore_base_none I b (by simp [pausedRef]))
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionBoolLoc, boolOffset0Loc] using
      auctionStorageLocLoad_bool_offset0_false evm ⟨51⟩ hzero)

theorem evalExpr_initialize_not_paused_true (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_initialize_paused_false evm I b hzero,
    evalUnaryOp?]
  rfl

theorem evalExpr_initialize_not_initializing_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none)
    (hzero : auctionInitializingByte evm = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (.storage initializingRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_initialize_initializing_false evm locals hbase hzero, evalUnaryOp?]
  rfl

theorem evalExpr_initialize_not_initializing_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none)
    (hnz : auctionInitializingByte evm ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (.storage initializingRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind,
    evalExpr_initialize_initializing_true evm locals hbase hnz, evalUnaryOp?]
  rfl

theorem auctionInitializeCoreBlock (evm : EVM.State) (I : ExecutionEnv) (b : Bool)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat <
      EVM.twoPow 8)
    (rest : List Stmt) {result : ExecResult}
    (hrest :
      ExecBlock auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
        (auctionInitializeCorePostState evm I) rest result) :
    ExecBlock auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I b }
      evm (auctionInitializeCoreStmts ++ rest) result := by
  dsimp [auctionInitializeCoreStmts, auctionInitializeCorePostState]
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionInitializeAssignPausedFalse evm I b)) ?_
  let s1 := auctionUnpausePostState evm
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [notEntered, evalExpr?, pure])
      (auctionInitializeAssignStatus s1 I b)) ?_
  let s2 := auctionInitializeSetStatusState s1
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [sender, evalExpr?, envValue, pure])
      (auctionInitializeAssignOwner s2 I b)) ?_
  let s3 := auctionInitializeSetAddressState s2 ⟨151⟩ (auctionSourceWord s2.executionEnv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalExpr_initialize_not_paused_true s3 I b
      (by simpa [s1, s2, s3] using auctionInitializeCorePausedZero evm)
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionInitializeAssignPausedTrue s3 I b)) ?_
  let s4 := auctionPausePostState s3
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_nouns s4 I b)
      (auctionInitializeAssignNouns s4 I b hcanonNouns)) ?_
  let s5 := auctionInitializeSetAddressState s4 ⟨201⟩ (auctionInitializeNounsWord I)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_weth s5 I b)
      (auctionInitializeAssignWeth s5 I b hcanonWeth)) ?_
  let s6 := auctionInitializeSetAddressState s5 ⟨202⟩ (auctionInitializeWethWord I)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_timeBuffer s6 I b)
      (auctionInitializeAssignTimeBuffer s6 I b)) ?_
  let s7 := auctionInitializeSetUint256State s6 ⟨203⟩ (auctionInitializeTimeBufferWord I)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_reservePrice s7 I b)
      (auctionInitializeAssignReservePrice s7 I b)) ?_
  let s8 := auctionInitializeSetUint256State s7 ⟨204⟩ (auctionInitializeReservePriceWord I)
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_minBid s8 I b)
      (auctionInitializeAssignMinBid s8 I b hcanonMinBid)) ?_
  let s9 := auctionInitializeSetMinBidState s8 I
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_arg_duration s9 I b)
      (auctionInitializeAssignDuration s9 I b)) ?_
  simpa [auctionInitializeCorePostState, s1, s2, s3, s4, s5, s6, s7, s8, s9] using hrest

theorem auctionInitializeFinalTopBlock (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I true }
      evm [auctionInitializeFinalStmt]
      (.ok { contract := auctionContract, locals := auctionInitializeTopStore I true }
        (auctionInitializeSetInitializingFalseState evm)) := by
  dsimp [auctionInitializeFinalStmt]
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_initialize_isTopLevelCall evm I true) ?_) ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionInitializeAssignInitializingFalse evm I true)) ExecBlock.nil

theorem auctionInitializeFinalNestedBlock (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock auctionConfig { contract := auctionContract, locals := auctionInitializeTopStore I false }
      evm [auctionInitializeFinalStmt]
      (.ok { contract := auctionContract, locals := auctionInitializeTopStore I false } evm) := by
  dsimp [auctionInitializeFinalStmt]
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_initialize_isTopLevelCall evm I false) ?_) ExecBlock.nil
  exact ExecBlock.nil

theorem auctionInitializeBodyReverts_callvalue (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionInitializeStore I)
      initializeTransition.body .reverted := by
  simpa [initializeTransition, nonpayable] using
    bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
      (evm := evm) (locals := auctionInitializeStore I)
      (rest := List.drop 1 initializeTransition.body) hwv

theorem auctionInitializeBodyReverts_initialized (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hinit0 : auctionInitializingByte evm = ⟨0⟩)
    (hizednz : auctionInitializedByte evm ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionInitializeStore I)
      initializeTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [initializeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_initialize_guard_false_initialized evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp [initializingRef]))
      (auctionInitializeStore_base_none I (by simp [initializedRef])) hinit0 hizednz))

theorem auctionInitializeBodyReturns_top (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hinit0 : auctionInitializingByte evm = ⟨0⟩)
    (hized0 : auctionInitializedByte evm = ⟨0⟩)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionInitializeStore I)
      initializeTransition.body
      (.returned { contract := auctionContract, locals := auctionInitializeTopStore I true }
        (auctionInitializeTopPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  dsimp [initializeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_initialize_guard_true_top evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp [initializingRef]))
      (auctionInitializeStore_base_none I (by simp [initializedRef])) hinit0 hized0)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_initialize_not_initializing_true evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp [initializingRef])) hinit0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_initialize_isTopLevelCall evm I true) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (auctionInitializeAssignInitializingTrue evm I true)) ?_
    let s0 := auctionInitializeSetInitializingTrueState evm
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (auctionInitializeAssignInitializedTrue s0 I true)) ExecBlock.nil
  let s1 := auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm)
  have hfinal := auctionInitializeFinalTopBlock (auctionInitializeCorePostState s1 I) I
  have hcore := auctionInitializeCoreBlock s1 I true hcanonNouns hcanonWeth hcanonMinBid
    [auctionInitializeFinalStmt] (hrest := hfinal)
  simpa [auctionInitializeTopPostState, s1] using hcore

theorem auctionInitializeBodyReturns_nested (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz : auctionInitializingByte evm ≠ ⟨0⟩)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionInitializeStore I)
      initializeTransition.body
      (.returned { contract := auctionContract, locals := auctionInitializeTopStore I false }
        (auctionInitializeNestedPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  dsimp [initializeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_initialize_guard_true_nested evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp [initializingRef])) hnz)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_initialize_not_initializing_false evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp [initializingRef])) hnz)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_initialize_isTopLevelCall evm I false) ExecBlock.nil) ?_
  have hfinal := auctionInitializeFinalNestedBlock (auctionInitializeCorePostState evm I) I
  have hcore := auctionInitializeCoreBlock evm I false hcanonNouns hcanonWeth hcanonMinBid
    [auctionInitializeFinalStmt] (hrest := hfinal)
  simpa [auctionInitializeNestedPostState] using hcore

theorem auctionInitializeCorePostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeCorePostState evm₁ I)
      (auctionInitializeCorePostState evm₂ I) := by
  unfold auctionInitializeCorePostState
  have h1 : EVMStateEquiv (auctionUnpausePostState evm₁) (auctionUnpausePostState evm₂) := by
    unfold auctionUnpausePostState auctionPausedSetFalseWord
    exact h.storageStore_codeOwner ⟨51⟩ (by rw [h.storageLoad_codeOwner ⟨51⟩])
  have h2 : EVMStateEquiv (auctionInitializeSetStatusState (auctionUnpausePostState evm₁))
      (auctionInitializeSetStatusState (auctionUnpausePostState evm₂)) := by
    unfold auctionInitializeSetStatusState
    exact h1.storageStore_codeOwner ⟨101⟩ rfl
  let s2₁ := auctionInitializeSetStatusState (auctionUnpausePostState evm₁)
  let s2₂ := auctionInitializeSetStatusState (auctionUnpausePostState evm₂)
  have h3 : EVMStateEquiv
      (auctionInitializeSetAddressState s2₁ ⟨151⟩ (auctionSourceWord s2₁.executionEnv))
      (auctionInitializeSetAddressState s2₂ ⟨151⟩ (auctionSourceWord s2₂.executionEnv)) := by
    unfold auctionInitializeSetAddressState
    exact h2.storageStore_codeOwner ⟨151⟩ (by
      rw [h2.storageLoad_codeOwner ⟨151⟩]
      rw [h2.executionEnv])
  let s3₁ := auctionInitializeSetAddressState s2₁ ⟨151⟩ (auctionSourceWord s2₁.executionEnv)
  let s3₂ := auctionInitializeSetAddressState s2₂ ⟨151⟩ (auctionSourceWord s2₂.executionEnv)
  have h4 : EVMStateEquiv (auctionPausePostState s3₁) (auctionPausePostState s3₂) := by
    unfold auctionPausePostState auctionPausedSetTrueWord
    exact h3.storageStore_codeOwner ⟨51⟩ (by rw [h3.storageLoad_codeOwner ⟨51⟩])
  let s4₁ := auctionPausePostState s3₁
  let s4₂ := auctionPausePostState s3₂
  have h5 : EVMStateEquiv
      (auctionInitializeSetAddressState s4₁ ⟨201⟩ (auctionInitializeNounsWord I))
      (auctionInitializeSetAddressState s4₂ ⟨201⟩ (auctionInitializeNounsWord I)) := by
    unfold auctionInitializeSetAddressState
    exact h4.storageStore_codeOwner ⟨201⟩ (by rw [h4.storageLoad_codeOwner ⟨201⟩])
  let s5₁ := auctionInitializeSetAddressState s4₁ ⟨201⟩ (auctionInitializeNounsWord I)
  let s5₂ := auctionInitializeSetAddressState s4₂ ⟨201⟩ (auctionInitializeNounsWord I)
  have h6 : EVMStateEquiv
      (auctionInitializeSetAddressState s5₁ ⟨202⟩ (auctionInitializeWethWord I))
      (auctionInitializeSetAddressState s5₂ ⟨202⟩ (auctionInitializeWethWord I)) := by
    unfold auctionInitializeSetAddressState
    exact h5.storageStore_codeOwner ⟨202⟩ (by rw [h5.storageLoad_codeOwner ⟨202⟩])
  let s6₁ := auctionInitializeSetAddressState s5₁ ⟨202⟩ (auctionInitializeWethWord I)
  let s6₂ := auctionInitializeSetAddressState s5₂ ⟨202⟩ (auctionInitializeWethWord I)
  have h7 : EVMStateEquiv
      (auctionInitializeSetUint256State s6₁ ⟨203⟩ (auctionInitializeTimeBufferWord I))
      (auctionInitializeSetUint256State s6₂ ⟨203⟩ (auctionInitializeTimeBufferWord I)) := by
    unfold auctionInitializeSetUint256State
    exact h6.storageStore_codeOwner ⟨203⟩ rfl
  let s7₁ := auctionInitializeSetUint256State s6₁ ⟨203⟩ (auctionInitializeTimeBufferWord I)
  let s7₂ := auctionInitializeSetUint256State s6₂ ⟨203⟩ (auctionInitializeTimeBufferWord I)
  have h8 : EVMStateEquiv
      (auctionInitializeSetUint256State s7₁ ⟨204⟩ (auctionInitializeReservePriceWord I))
      (auctionInitializeSetUint256State s7₂ ⟨204⟩ (auctionInitializeReservePriceWord I)) := by
    unfold auctionInitializeSetUint256State
    exact h7.storageStore_codeOwner ⟨204⟩ rfl
  let s8₁ := auctionInitializeSetUint256State s7₁ ⟨204⟩ (auctionInitializeReservePriceWord I)
  let s8₂ := auctionInitializeSetUint256State s7₂ ⟨204⟩ (auctionInitializeReservePriceWord I)
  have h9 : EVMStateEquiv (auctionInitializeSetMinBidState s8₁ I)
      (auctionInitializeSetMinBidState s8₂ I) := by
    unfold auctionInitializeSetMinBidState
    exact h8.storageStore_codeOwner ⟨205⟩ (by rw [h8.storageLoad_codeOwner ⟨205⟩])
  let s9₁ := auctionInitializeSetMinBidState s8₁ I
  let s9₂ := auctionInitializeSetMinBidState s8₂ I
  have h10 : EVMStateEquiv
      (auctionInitializeSetUint256State s9₁ ⟨206⟩ (auctionInitializeDurationWord I))
      (auctionInitializeSetUint256State s9₂ ⟨206⟩ (auctionInitializeDurationWord I)) := by
    unfold auctionInitializeSetUint256State
    exact h9.storageStore_codeOwner ⟨206⟩ rfl
  simpa [s2₁, s2₂, s3₁, s3₂, s4₁, s4₂, s5₁, s5₂, s6₁, s6₂, s7₁, s7₂, s8₁,
    s8₂, s9₁, s9₂] using h10

theorem auctionInitializeTopPostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeTopPostState evm₁ I)
      (auctionInitializeTopPostState evm₂ I) := by
  unfold auctionInitializeTopPostState auctionInitializeSetInitializingFalseState
  have h1 : EVMStateEquiv (auctionInitializeSetInitializingTrueState evm₁)
      (auctionInitializeSetInitializingTrueState evm₂) := by
    unfold auctionInitializeSetInitializingTrueState
    exact h.storageStore_codeOwner ⟨0⟩ (by rw [h.storageLoad_codeOwner ⟨0⟩])
  have h2 : EVMStateEquiv
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm₁))
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm₂)) := by
    unfold auctionInitializeSetInitializedTrueState
    exact h1.storageStore_codeOwner ⟨0⟩ (by rw [h1.storageLoad_codeOwner ⟨0⟩])
  have h3 := auctionInitializeCorePostState_equiv I h2
  exact h3.storageStore_codeOwner ⟨0⟩ (by rw [h3.storageLoad_codeOwner ⟨0⟩])

theorem auctionInitializeNestedPostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeNestedPostState evm₁ I)
      (auctionInitializeNestedPostState evm₂ I) := by
  simpa [auctionInitializeNestedPostState] using auctionInitializeCorePostState_equiv I h

theorem auctionInitializingByte_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionInitializingByte (initState cA gh bl σ σ₀ g A I) =
      UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ := by
  simp [auctionInitializingByte, auctionSlotWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount]

theorem auctionInitializedByte_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionInitializedByte (initState cA gh bl σ σ₀ g A I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ := by
  simp [auctionInitializedByte, auctionSlotWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount]

theorem auctionInitializingByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (h : accountMapEquiv σ τ) :
    UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ τ I) ⟨256⟩) ⟨255⟩ := by
  rw [show auctionSlotWord ⟨0⟩ σ I = auctionSlotWord ⟨0⟩ τ I from
    accountMapEquiv_storage_findD h I.codeOwner ⟨0⟩ ⟨0⟩]

theorem auctionInitializedByte_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (h : accountMapEquiv σ τ) :
    UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ =
      UInt256.land (auctionSlotWord ⟨0⟩ τ I) ⟨255⟩ := by
  rw [show auctionSlotWord ⟨0⟩ σ I = auctionSlotWord ⟨0⟩ τ I from
    accountMapEquiv_storage_findD h I.codeOwner ⟨0⟩ ⟨0⟩]

theorem auctionDispatch_initialize {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 11)) :
    dispatchMsg auctionContract I.calldata = some initializeTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [])
    (post := [createBidTransition, settleAndCreateTransition, settleAuctionTransition,
      pauseTransition, unpauseTransition, setTimeBufferTransition, setReservePriceTransition,
      setMinBidIncTransition, transferOwnershipTransition, renounceOwnershipTransition,
      ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter,
      minBidIncGetter, durationGetter, auctionGetter])
    (ti := initializeTransition)
    (htr := by rfl)
  · intro t ht
    simp at ht
  · rw [selectorOf, initializeSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

-- LIBRARY CANDIDATE: ABI scalar-word decode for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hcanon128 : (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 =
      some [.address (AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rw [auctionDecodeScalarWord_uint8_ok (start := 128) hlen128 hcanon128]
  rw [decodeScalarWord_uint256_ok (start := 160) hlen160]
  rfl

-- LIBRARY CANDIDATE: first address non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: second address non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

-- LIBRARY CANDIDATE: uint8 non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon4 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hnc128 : ¬ (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rw [auctionDecodeScalarWord_uint8_none_noncanon (start := 128) hlen128 hnc128]

-- LIBRARY CANDIDATE: short calldata branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_short {bytes : List UInt8}
    (hshort : bytes.length < 192) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  cases hdec :
      decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 with
  | none => rfl
  | some values =>
      have hlen := decodeScalarWords?_some_length (types :=
        [addr, addr, uint256, uint256, uint8, uint256]) (bytes := bytes) (cursor := 0)
        (values := values) (Nat.zero_le _) hdec
      exfalso
      norm_num at hlen
      omega

theorem auctionDecode_initialize {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat <
      EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata =
      some (auctionInitializeStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((I.calldata.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((I.calldata.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((I.calldata.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake164 : ((I.calldata.toList.drop 164).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have hword68 : ABI.bytesToWord ((I.calldata.toList.drop 68).take 32) =
      auctionInitializeTimeBufferWord I := by
    simpa [auctionInitializeTimeBufferWord] using decode_word_at_eq I.calldata 68 (by omega)
      (by norm_num)
  have hword100 : ABI.bytesToWord ((I.calldata.toList.drop 100).take 32) =
      auctionInitializeReservePriceWord I := by
    simpa [auctionInitializeReservePriceWord] using decode_word_at_eq I.calldata 100
      (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((I.calldata.toList.drop 132).take 32) =
      auctionInitializeMinBidIncrementPercentageWord I := by
    simpa [auctionInitializeMinBidIncrementPercentageWord] using
      decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have hword164 : ABI.bytesToWord ((I.calldata.toList.drop 164).take 32) =
      auctionInitializeDurationWord I := by
    simpa [auctionInitializeDurationWord] using decode_word_at_eq I.calldata 164
      (by omega) (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  have htake132' : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake132
  have htake164' : (((I.calldata.toList.drop 4).drop 160).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake164
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata =
    some (auctionInitializeStore I)
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_ok (bytes := I.calldata.toList.drop 4)
    htake4 htake36' htake68' htake100' htake132' htake164'
    (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanonWeth)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
          auctionInitializeMinBidIncrementPercentageWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
      exact hcanonMinBid)]
  change decodeCalldata.insertValues
      ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
        "_duration"]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 160).take 32)).toNat)] ∅ =
    some (auctionInitializeStore I)
  simp [decodeCalldata.insertValues, auctionInitializeStore]
  rw [hword4, hword36, hword68, hword100, hword132, hword164]

theorem auctionDecode_initialize_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_short (bytes := I.calldata.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem auctionDecode_initialize_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem auctionDecode_initialize_none_noncanon_nouns {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionInitializeNounsWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon0 (bytes := I.calldata.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc)]

theorem auctionDecode_initialize_none_noncanon_weth {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeWethWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon1 (bytes := I.calldata.toList.drop 4)
    htake4 htake36' (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hnc)]

theorem auctionDecode_initialize_none_noncanon_minBid {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((I.calldata.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((I.calldata.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((I.calldata.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have hword132 : ABI.bytesToWord ((I.calldata.toList.drop 132).take 32) =
      auctionInitializeMinBidIncrementPercentageWord I := by
    simpa [auctionInitializeMinBidIncrementPercentageWord] using
      decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  have htake132' : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake132
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon4 (bytes := I.calldata.toList.drop 4)
    htake4 htake36' htake68' htake100' htake132'
    (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanonWeth)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
          auctionInitializeMinBidIncrementPercentageWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
      exact hnc)]

theorem auctionReachInitializeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 11)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨705⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x87, 0xf4, 0x9f, 0x54]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x87f49f54⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x87 0xf4 0x9f 0x54 ⟨0x87f49f54⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper :
      UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    decide
  have h98 := RD.selectorSplitTakenAuto h29 auctionUpperSplitWellFormed hupper
    (by jump_dest) (by simp)
  have h99 := h98.jumpdest (by decide) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc 1))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨705⟩ 1 h99
    (fun j hj => auctionUpperLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_initialize_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨705⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd705⟩ := hreach
  exact evm_run rd705 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨716⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionInitializeX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5400⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨731⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd705⟩ := hreach
  exact ⟨_, _, evm_run rd705 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨716⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨731⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5400⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1200000 in
theorem auctionDecodeInitializeOk5400 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanonWeth : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hcanonMinBid : (calldataWord ee.calldata 132).toNat < EVM.twoPow 8)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret
      ([calldataWord ee.calldata 164, calldataWord ee.calldata 132,
        calldataWord ee.calldata 100, calldataWord ee.calldata 68,
        calldataWord ee.calldata 36, calldataWord ee.calldata 4] ++ R)
      mem aw rdata acc k' C' := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqB : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      solcAddrCanon_eq hcanonWeth
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heqB] at rd5392b
  have rd5448 := evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5476pre := evm_run rd5448 with [
    swap5, pop, push1 ⟨64⟩, dup8, add, calldataload, swap4, pop,
    push1 ⟨96⟩, dup8, add, calldataload, swap3, pop,
    push2 ⟨5476⟩, push1 ⟨128⟩, dup9, add, push2 ⟨5304⟩, jump (by jump_dest)]
  have hclean : UInt256.land (calldataWord ee.calldata 132) ⟨255⟩ =
      calldataWord ee.calldata 132 :=
    auctionLand255_eq_self_of_uint8 (calldataWord ee.calldata 132) hcanonMinBid
  have heqU : UInt256.eq (calldataWord ee.calldata 132)
      (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) = ⟨1⟩ := by
    rw [hclean, u256_eq_refl]
  have rd5320 := evm_run rd5476pre with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiT (by
      change UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes
            ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32)) ⟨255⟩) ≠ ⟨0⟩
      simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide] using
        (show UInt256.eq (calldataWord ee.calldata 132)
          (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) ≠ ⟨0⟩ from by
          rw [heqU]; decide)) (by jump_dest), jumpdest]
  have rd5476 := evm_run rd5320 with [swap2, swap1, pop, jump (by jump_dest), jumpdest]
  exact ⟨_, _, by
    simpa [calldataWord,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨96⟩).toNat = 100 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨160⟩).toNat = 164 from by decide] using
      evm_run rd5476 with [
        swap2, pop, push1 ⟨160⟩, dup8, add, calldataload, swap1, pop,
        swap3, swap6, pop, swap3, swap6, pop, swap3, swap6, jump hret]⟩

theorem auctionDecodeInitializeLenRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  exact evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiNT (by rw [hsltval]; decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 800000 in
theorem auctionDecodeInitializeNoncanonNounsRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hnc : ¬ (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq0word : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro heqword
    apply hnc
    apply solcAddrCanonical_of_clean
    rw [← heqword, u256_eq_refl]
  have heq0 : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨0⟩ := by
    simpa [calldataWord] using heq0word
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heq0] at rd5392a
  exact evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiNT (by decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 1000000 in
theorem auctionDecodeInitializeNoncanonWethRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hnc : ¬ (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq0word : UInt256.eq (calldataWord ee.calldata 36)
      (UInt256.land (calldataWord ee.calldata 36) solcAddrMask) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro heqword
    apply hnc
    apply solcAddrCanonical_of_clean
    rw [← heqword, u256_eq_refl]
  have heq0 : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨0⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      heq0word
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heq0] at rd5392b
  exact evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiNT (by decide),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 1200000 in
theorem auctionDecodeInitializeNoncanonMinBidRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanonWeth : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hnc : ¬ (calldataWord ee.calldata 132).toNat < EVM.twoPow 8)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqB : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      solcAddrCanon_eq hcanonWeth
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heqB] at rd5392b
  have rd5448 := evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5476pre := evm_run rd5448 with [
    swap5, pop, push1 ⟨64⟩, dup8, add, calldataload, swap4, pop,
    push1 ⟨96⟩, dup8, add, calldataload, swap3, pop,
    push2 ⟨5476⟩, push1 ⟨128⟩, dup9, add, push2 ⟨5304⟩, jump (by jump_dest)]
  have hne : calldataWord ee.calldata 132 ≠
      UInt256.land (calldataWord ee.calldata 132) ⟨255⟩ :=
    (auctionLand255_ne_self_of_not_uint8 (calldataWord ee.calldata 132) hnc).symm
  have heq0 : UInt256.eq (calldataWord ee.calldata 132)
      (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) = ⟨0⟩ := by
    exact u256_eq_of_ne hne
  exact evm_run rd5476pre with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiNT (by
      change UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes
            ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32)) ⟨255⟩) = ⟨0⟩
      simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide] using
        heq0),
    push0, dup1, raw rev 0 (by decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionInitializeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat <
      EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  obtain ⟨_, _, rd731₀⟩ :=
    auctionDecodeInitializeOk5400 (R := [⟨413⟩, sel]) rd5400 hslt
      (by simpa [auctionInitializeNounsWord] using hcanonNouns)
      (by simpa [auctionInitializeWethWord] using hcanonWeth)
      (by simpa [auctionInitializeMinBidIncrementPercentageWord] using hcanonMinBid)
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd731⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨731⟩
      [calldataWord I.calldata 164, calldataWord I.calldata 132,
        calldataWord I.calldata 100, calldataWord I.calldata 68,
        calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd731₀⟩
  exact ⟨_, _, by
    simpa [auctionInitializeDurationWord, auctionInitializeMinBidIncrementPercentageWord,
      auctionInitializeReservePriceWord, auctionInitializeTimeBufferWord,
      auctionInitializeWethWord, auctionInitializeNounsWord] using
      evm_run rd731 with [jumpdest, push2 ⟨2130⟩, jump (by jump_dest)]⟩

theorem auctionInitializeX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 196)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz4) (by simpa using hshort)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeLenRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hbig) hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeLenRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_nouns {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonNounsRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_weth {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonWethRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hcanonNouns)
    (by simpa [auctionInitializeWethWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_minBid {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonMinBidRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hcanonNouns)
    (by simpa [auctionInitializeWethWord] using hcanonWeth)
    (by simpa [auctionInitializeMinBidIncrementPercentageWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Auction
