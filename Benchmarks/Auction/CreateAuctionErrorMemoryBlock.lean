import Benchmarks.Auction.CreateAuctionErrorMemorySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

def errorGuardBlock : List Stmt :=
  [ .require (errorStringReturndataLongEnough "err"),
    .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
    .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
    .require (errorStringOffsetInBounds "err" "_errOffset"),
    .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
    .require (.binary .le (.var "_errLength") solcMaxU64Expr),
    .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
    .require (errorStringAllocationWithinU64 "_errOffset" "_errLength" (.var "_freePtr")),
    .require (errorStringAllocationNoWrap "_errOffset" "_errLength" (.var "_freePtr")),
    .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
    .require (.unary .not (.storage pausedRef)),
    .assign .storage pausedRef (.boolLit true) ]

def errorFailureBlock : List Stmt :=
  [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
      (.bytesLit errorStringSelector)) errorGuardBlock [ .require (.boolLit false) ] ]

theorem mintFailure {evm evmCall : EVM.State} {out : ByteArray} {free : UInt256}
    {result : ExecResult}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hfail : ExecBlock auctionConfig (createAuctionErrFrame free out) evmCall
      errorFailureBlock result) :
    ExecBlock auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body result := by
  have hs : ExecStmt auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body.head! result := by
    exact ExecStmt.checkedCallFail
      (evalExpr_createAuction_nouns_frame evm _ (by simp [auctionCreateAuctionMemoryLocals]))
      (by simp [evalExpr?, pure]) (by rfl) hcall hfail
  cases result with
  | ok => exact ExecBlock.consNormal hs ExecBlock.nil
  | returned => exact ExecBlock.consReturn hs
  | reverted => exact ExecBlock.consRevert hs
  | «break» => exact ExecBlock.consBreak hs
  | «continue» => exact ExecBlock.consContinue hs

theorem errorSelector {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {result : ExecResult} (hlen : 4 ≤ out.size)
    (hsel : out.extract 0 4 = errorStringSelector)
    (hbranch : ExecBlock auctionConfig (createAuctionErrFrame free out) evm
      errorGuardBlock result) :
    ExecBlock auctionConfig (createAuctionErrFrame free out) evm errorFailureBlock result := by
  have hs : ExecStmt auctionConfig (createAuctionErrFrame free out) evm
      errorFailureBlock.head! result :=
    ExecStmt.iteTrue (evalExpr_createAuction_err_slice_true evm free hlen hsel) hbranch
  cases result with
  | ok => exact ExecBlock.consNormal hs ExecBlock.nil
  | returned => exact ExecBlock.consReturn hs
  | reverted => exact ExecBlock.consRevert hs
  | «break» => exact ExecBlock.consBreak hs
  | «continue» => exact ExecBlock.consContinue hs

theorem errorShort {evm : EVM.State} {out : ByteArray} (free : UInt256)
    (hshort : out.size < 4) :
    ExecBlock auctionConfig (createAuctionErrFrame free out) evm errorFailureBlock .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.iteCondRevert (evalExpr_createAuction_err_slice_revert evm free hshort))

theorem errorOther {evm : EVM.State} {out : ByteArray} (free : UInt256)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ExecBlock auctionConfig (createAuctionErrFrame free out) evm errorFailureBlock .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.iteFalse (evalExpr_createAuction_err_slice_false evm free hlen hsel)
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure]))))

theorem offsetPrefix {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off : Nat} {tail : List Stmt} {result : ExecResult}
    (hlong : 68 ≤ out.size) (hsmall : (out.extract 4 out.size).size < 2 ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (htail : ExecBlock auctionConfig (createAuctionErrOffsetFrame free out off) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrFrame free out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err") ] ++ tail)
      result := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm free hlong)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_error_offset_decode_ok evm free
      (by omega) hsmall hoff)) htail

theorem lengthPrefix {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrOffsetFrame free out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++ tail)
      result := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_offset_max_true evm free hoffMax)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_offset_bounds_true evm free hoffBound)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_error_length_decode_ok evm free
      (by omega) hoffBound hlenWord)) htail

theorem allocationPrefix {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm
      ([ .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength") ] ++ tail)
      result := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm free hlenMax)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_payload_bounds_true evm free hpayloadBound))
    htail

theorem decodePrefix {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hsum : off + len + 63 < UInt256.size)
    (halloc : free.toNat + errorStringRoundedAllocNat off len ≤ ABI.solcMaxU64)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm
      ([ .require (errorStringAllocationWithinU64 "_errOffset" "_errLength" (.var "_freePtr")),
         .require (errorStringAllocationNoWrap "_errOffset" "_errLength" (.var "_freePtr")) ] ++ tail)
      result := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [halloc, decide_true] using evalExpr_createAuction_error_alloc_u64 evm free
      (out := out) hsum)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_createAuction_error_alloc_no_wrap evm free hsum)) htail

theorem pauseTail {evm : EVM.State} {out : ByteArray} {free : UInt256}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused : UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ = ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrLengthFrame free out off len) evm
      [ .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame free out off len decoded) (auctionPausePostState evm)) := by
  let f := createAuctionErrDecodedFrame free out off len decoded
  have hbase : f.locals.get? pausedRef.base = none := by
    simp [f, createAuctionErrDecodedFrame, createAuctionErrLengthFrame,
      createAuctionErrOffsetFrame, createAuctionErrFrame, auctionCreateAuctionMemoryLocals,
      pausedRef]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm free hlen hdec)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_pause_notPaused_true_frame evm f.locals hbase hnotPaused)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_pause_true_frame evm f.locals)
      (auctionPauseAssign_frame evm f.locals hbase)) ExecBlock.nil

end Auction.CreateMemory
