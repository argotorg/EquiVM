import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

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
    (auctionStorageLocStore_uint256 evm ⟨203⟩ (auctionInitializeTimeBufferWord I))

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
    (auctionStorageLocStore_uint256 evm ⟨204⟩ (auctionInitializeReservePriceWord I))

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
    (auctionStorageLocStore_uint8_offset0 evm ⟨205⟩
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
    (auctionStorageLocStore_uint256 evm ⟨206⟩ (auctionInitializeDurationWord I))

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
  rw [Nat.mul_mod_left]
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
      simp only [Solm.EVM.storageLoad, State.lookupAccount, hacc]
      rfl
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
  exact evalExpr_storage_scalar_value (t := .bool) (loc := auctionBoolLoc ⟨51⟩)
    (hbase := auctionInitializeTopStore_base_none I b (by simp [pausedRef]))
    (her := her) (hty := hty) (hloc := rfl)
    (hload := auctionStorageLocLoad_bool_offset0_false evm ⟨51⟩ hzero)

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
    (ExecStmt.assign (by simp [sender, evalExpr?, envValue, pure, s2])
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
  exact hrest

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
      (auctionInitializeStore_base_none I (by simp))
      (auctionInitializeStore_base_none I (by simp)) hinit0 hizednz))

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
      (auctionInitializeStore_base_none I (by simp))
      (auctionInitializeStore_base_none I (by simp)) hinit0 hized0)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_initialize_not_initializing_true evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp)) hinit0)) ?_
  let s1 := auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm)
  refine ExecBlock.consNormal
    (solm' := { contract := auctionContract, locals := auctionInitializeTopStore I true })
    (evm' := s1)
    (ExecStmt.iteTrue (evalExpr_initialize_isTopLevelCall evm I true) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (auctionInitializeAssignInitializingTrue evm I true)) ?_
    let s0 := auctionInitializeSetInitializingTrueState evm
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (auctionInitializeAssignInitializedTrue s0 I true)) ExecBlock.nil
  have hfinal := auctionInitializeFinalTopBlock (auctionInitializeCorePostState s1 I) I
  have hcore := auctionInitializeCoreBlock s1 I true hcanonNouns hcanonWeth hcanonMinBid
    [auctionInitializeFinalStmt] (hrest := hfinal)
  exact hcore

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
      (auctionInitializeStore_base_none I (by simp)) hnz)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_initialize_not_initializing_false evm (auctionInitializeStore I)
      (auctionInitializeStore_base_none I (by simp)) hnz)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_initialize_isTopLevelCall evm I false) ExecBlock.nil) ?_
  have hfinal := auctionInitializeFinalNestedBlock (auctionInitializeCorePostState evm I) I
  have hcore := auctionInitializeCoreBlock evm I false hcanonNouns hcanonWeth hcanonMinBid
    [auctionInitializeFinalStmt] (hrest := hfinal)
  exact hcore

-- Check each update with abstract states before composing the initializer's storage writes.
private theorem initializeSetAddress_equiv {s t : EVM.State} (h : EVMStateEquiv s t)
    (slot : UInt256) {v w : UInt256} (hv : v = w) :
    EVMStateEquiv (auctionInitializeSetAddressState s slot v)
      (auctionInitializeSetAddressState t slot w) := by
  exact h.storageStore_codeOwner slot
    (congrArg₂ setAddressOffset0Word (h.storageLoad_codeOwner slot) hv)

private theorem initializeSetUint256_equiv {s t : EVM.State} (h : EVMStateEquiv s t)
    (slot v : UInt256) :
    EVMStateEquiv (auctionInitializeSetUint256State s slot v)
      (auctionInitializeSetUint256State t slot v) :=
  h.storageStore_codeOwner slot rfl

private theorem initializePause_equiv {s t : EVM.State} (h : EVMStateEquiv s t) :
    EVMStateEquiv (auctionPausePostState s) (auctionPausePostState t) := by
  exact h.storageStore_codeOwner ⟨51⟩
    (congrArg (fun w ↦ setBoolOffset0Word w ⟨1⟩) (h.storageLoad_codeOwner ⟨51⟩))

private theorem initializeSetMinBid_equiv {s t : EVM.State} (h : EVMStateEquiv s t)
    (I : ExecutionEnv) :
    EVMStateEquiv (auctionInitializeSetMinBidState s I)
      (auctionInitializeSetMinBidState t I) := by
  exact h.storageStore_codeOwner ⟨205⟩
    (congrArg (fun w ↦ auctionSetUint8Offset0Word w
      (auctionInitializeMinBidIncrementPercentageWord I)) (h.storageLoad_codeOwner ⟨205⟩))

private theorem initializeClearFlag_equiv {s t : EVM.State} (h : EVMStateEquiv s t) :
    EVMStateEquiv (auctionInitializeSetInitializingFalseState s)
      (auctionInitializeSetInitializingFalseState t) := by
  exact h.storageStore_codeOwner ⟨0⟩
    (congrArg auctionSetBoolOffset1FalseWord (h.storageLoad_codeOwner ⟨0⟩))

theorem auctionInitializeCorePostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeCorePostState evm₁ I)
      (auctionInitializeCorePostState evm₂ I) := by
  have h1 : EVMStateEquiv (auctionUnpausePostState evm₁) (auctionUnpausePostState evm₂) := by
    unfold auctionUnpausePostState auctionPausedSetFalseWord
    exact h.storageStore_codeOwner ⟨51⟩ (by rw [h.storageLoad_codeOwner ⟨51⟩])
  have h2 : EVMStateEquiv (auctionInitializeSetStatusState (auctionUnpausePostState evm₁))
      (auctionInitializeSetStatusState (auctionUnpausePostState evm₂)) :=
    h1.storageStore_codeOwner ⟨101⟩ rfl
  have h3 := initializeSetAddress_equiv h2 ⟨151⟩ (congrArg auctionSourceWord h2.executionEnv)
  have h4 := initializePause_equiv h3
  have h5 := initializeSetAddress_equiv h4 ⟨201⟩ (v := auctionInitializeNounsWord I) rfl
  have h6 := initializeSetAddress_equiv h5 ⟨202⟩ (v := auctionInitializeWethWord I) rfl
  have h7 := initializeSetUint256_equiv h6 ⟨203⟩ (auctionInitializeTimeBufferWord I)
  have h8 := initializeSetUint256_equiv h7 ⟨204⟩ (auctionInitializeReservePriceWord I)
  have h9 := initializeSetMinBid_equiv h8 I
  exact initializeSetUint256_equiv h9 ⟨206⟩ (auctionInitializeDurationWord I)

theorem auctionInitializeTopPostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeTopPostState evm₁ I)
      (auctionInitializeTopPostState evm₂ I) := by
  have h1 : EVMStateEquiv (auctionInitializeSetInitializingTrueState evm₁)
      (auctionInitializeSetInitializingTrueState evm₂) := by
    unfold auctionInitializeSetInitializingTrueState
    exact h.storageStore_codeOwner ⟨0⟩ (by rw [h.storageLoad_codeOwner ⟨0⟩])
  have h2 : EVMStateEquiv
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm₁))
      (auctionInitializeSetInitializedTrueState (auctionInitializeSetInitializingTrueState evm₂)) := by
    unfold auctionInitializeSetInitializedTrueState
    exact h1.storageStore_codeOwner ⟨0⟩ (by rw [h1.storageLoad_codeOwner ⟨0⟩])
  exact initializeClearFlag_equiv (auctionInitializeCorePostState_equiv I h2)

theorem auctionInitializeNestedPostState_equiv {evm₁ evm₂ : EVM.State} (I : ExecutionEnv)
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (auctionInitializeNestedPostState evm₁ I)
      (auctionInitializeNestedPostState evm₂ I) := by
  exact auctionInitializeCorePostState_equiv I h

theorem auctionInitializingByte_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionInitializingByte (initState cA gh bl σ σ₀ g A I) =
      UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ := by
  simp [auctionInitializingByte, auctionSlotWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem auctionInitializedByte_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionInitializedByte (initState cA gh bl σ σ₀ g A I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ := by
  simp [auctionInitializedByte, auctionSlotWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

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

end Auction
