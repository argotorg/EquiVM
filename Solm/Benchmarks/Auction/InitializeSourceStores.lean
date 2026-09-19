import Solm.Benchmarks.Auction.InitializeState

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def InitializeArgs.bodyLocals (args : InitializeArgs) (top : Bool) : Store :=
  args.locals.insert "isTopLevelCall" (.bool top)

def initializeParamStatements : List Stmt :=
  [.assign .storage nounsRef (.var "_nouns"),
    .assign .storage wethRef (.var "_weth"),
    .assign .storage timeBufferRef (.var "_timeBuffer"),
    .assign .storage reservePriceRef (.var "_reservePrice"),
    .assign .storage minBidIncRef (.var "_minBidIncrementPercentage"),
    .assign .storage durationRef (.var "_duration")]

theorem initializeParamsSource (evm : EVM.State) (args : InitializeArgs) (top : Bool)
    (hc : args.canonical) :
    ExecBlock auctionConfig { contract := auctionContract, locals := args.bodyLocals top }
      evm initializeParamStatements
      (.ok { contract := auctionContract, locals := args.bodyLocals top } (args.storeState evm))
        := by
  apply ExecBlock.consNormal (ExecStmt.assign (value := .address (.ofNat args.nouns.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite evm _ _ "nouns" (.elem .address) (auctionAddrLoc ⟨201⟩) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_address_offset0 evm ⟨201⟩ args.nouns hc.1)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .address (.ofNat args.weth.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite _ _ _ "weth" (.elem .address) (auctionAddrLoc ⟨202⟩) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_address_offset0 _ ⟨202⟩ args.weth hc.2.1)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat args.timeBuffer.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite _ _ _ "timeBuffer" (.elem (.int uint256Int)) (auctionUint256Loc ⟨203⟩) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_uint256 _ ⟨203⟩ args.timeBuffer)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat args.reservePrice.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite _ _ _ "reservePrice" (.elem (.int uint256Int)) (auctionUint256Loc ⟨204⟩) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_uint256 _ ⟨204⟩ args.reservePrice)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat args.minBidIncrement.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite _ _ _ "minBidIncrementPercentage" (.elem (.int (.uint ⟨8, by decide⟩)))
      (auctionUint8LocAt ⟨205⟩ 0) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_uint8 _ ⟨205⟩ args.minBidIncrement hc.2.2)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat args.duration.toNat))
    (by simp [evalExpr?, InitializeArgs.bodyLocals, InitializeArgs.locals, EvalResult.ofOption,
      Std.HashMap.getElem_insert])
    (scalarWrite _ _ _ "duration" (.elem (.int uint256Int)) (auctionUint256Loc ⟨206⟩) _
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) (by native_decide) rfl
      (by trivial) (storageLocStore_uint256 _ ⟨206⟩ args.duration)))
  exact ExecBlock.nil

theorem initializeSetupSource (evm : EVM.State) (locals : Store)
    (hp : locals.get? "_paused" = none) (hs : locals.get? "_status" = none)
    (ho : locals.get? "_owner" = none) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      [.assign .storage pausedRef (.boolLit false), .assign .storage statusRef notEntered,
        .assign .storage ownerRef sender]
      (.ok { contract := auctionContract, locals := locals }
        (initializerOwnerState (initializerStatusState (initializerPauseState evm)))) := by
  apply ExecBlock.consNormal (ExecStmt.assign (value := .bool false)
    (by simp [evalExpr?, pure])
    (scalarWrite evm _ locals "_paused" (.elem .bool) (auctionBoolLoc ⟨51⟩) _
      hp (by native_decide) rfl (by trivial) (storageLocStore_bool_false_offset0 evm ⟨51⟩)))
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int 1)
    (by simp [notEntered, evalExpr?, pure])
    (scalarWrite _ _ locals "_status" (.elem (.int uint256Int)) (auctionUint256Loc ⟨101⟩) _
      hs (by native_decide) rfl (by trivial) (storageLocStore_uint256 _ ⟨101⟩ ⟨1⟩)))
  exact assignStorageBlock (value := .address (.ofNat
      (solcSourceWord (initializerStatusState (initializerPauseState evm)).executionEnv).toNat))
    (by rw [solcSource_ofNat]; simp [sender, evalExpr?, envValue, pure,
      initializerStatusState, initializerPauseState])
    (assignOwner _ locals _ ho (solcSourceWord_canonical _))

theorem initializerExitSource (evm : EVM.State) (locals : Store) (top : Bool)
    (hi : locals.get? "_initializing" = none)
    (ht : locals.get? "isTopLevelCall" = some (.bool top)) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      [.ite (.var "isTopLevelCall") [.assign .storage initializingRef (.boolLit false)] []]
      (.ok { contract := auctionContract, locals := locals } (initializerExitedState evm top)) := by
  apply ExecBlock.consNormal ?_ ExecBlock.nil
  cases top
  · apply ExecStmt.iteFalse
    · simp only [evalExpr?, ht, EvalResult.ofOption]
    · exact ExecBlock.nil
  · apply ExecStmt.iteTrue
    · simp only [evalExpr?, ht, EvalResult.ofOption]
    · exact assignStorageBlock (by simp [evalExpr?, pure]) (assignInitializing evm locals false hi)

end Auction
