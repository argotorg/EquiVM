import Benchmarks.Auction.UnpauseCreateAuctionBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Auction

theorem execCreateAuctionErrorStringGuardBlock {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
         .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
      result := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset"),
       .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
       .require (.binary .le (.var "_errLength") solcMaxU64Expr),
       .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
       .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
       .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
    result ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
         .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
      result ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset"),
           .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
           .require (.binary .le (.var "_errLength") solcMaxU64Expr),
           .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
           .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
           .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
        result ?_ ?_
      · exact ExecStmt.requireTrue (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
          (.require (errorStringOffsetInBounds "err" "_errOffset"))
          (createAuctionErrOffsetFrame out off) evm
          ([ .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
             .require (.binary .le (.var "_errLength") solcMaxU64Expr),
             .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
             .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
             .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
          result ?_ ?_
        · exact ExecStmt.requireTrue
            (evalExpr_createAuction_error_offset_bounds_true evm hoffBound)
        · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
            (.letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset"))
            (createAuctionErrLengthFrame out off len) evm
            ([ .require (.binary .le (.var "_errLength") solcMaxU64Expr),
               .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
               .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
               .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
            result ?_ ?_
          · simpa [createAuctionErrOffsetFrame, createAuctionErrLengthFrame] using
              ExecStmt.letDecl
                (evalExpr_createAuction_error_length_decode_ok evm hlen hoffBound hlenWord)
          · refine @ExecBlock.consNormal
              auctionConfig (createAuctionErrLengthFrame out off len) evm
              (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
              (createAuctionErrLengthFrame out off len) evm
              ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
                 .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
                 .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
              result ?_ ?_
            · exact ExecStmt.requireTrue
                (evalExpr_createAuction_error_length_max_true evm hlenMax)
            · refine @ExecBlock.consNormal
                auctionConfig (createAuctionErrLengthFrame out off len) evm
                (.require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"))
                (createAuctionErrLengthFrame out off len) evm
                ([ .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
                   .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
                result ?_ ?_
              · exact ExecStmt.requireTrue
                  (evalExpr_createAuction_error_payload_bounds_true evm hpayloadBound)
              · refine @ExecBlock.consNormal
                  auctionConfig (createAuctionErrLengthFrame out off len) evm
                  (.require (errorStringAllocationWithinU64 "_errOffset" "_errLength"))
                  (createAuctionErrLengthFrame out off len) evm
                  ([ .require (errorStringAllocationNoWrap "_errOffset" "_errLength") ] ++ tail)
                  result ?_ ?_
                · exact ExecStmt.requireTrue
                    (evalExpr_createAuction_error_alloc_u64_true evm hoffMax hlenMax halloc)
                · exact @ExecBlock.consNormal
                    auctionConfig (createAuctionErrLengthFrame out off len) evm
                    (.require (errorStringAllocationNoWrap "_errOffset" "_errLength"))
                    (createAuctionErrLengthFrame out off len) evm tail result
                    (ExecStmt.requireTrue
                      (evalExpr_createAuction_error_alloc_no_wrap_true evm hoffMax hlenMax))
                    htail

theorem execCreateAuctionErrorStringOffsetMaxReverts {evm : EVM.State} {out : ByteArray}
    {off : Nat} {tail : List Stmt}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
      .reverted := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr) ] ++ tail)
      .reverted ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · exact ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_createAuction_error_offset_max_false evm hoffMax))

theorem execCreateAuctionErrorStringOffsetBoundsReverts {evm : EVM.State} {out : ByteArray}
    {off : Nat} {tail : List Stmt}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
      .reverted := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
      .reverted ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset") ] ++ tail)
        .reverted ?_ ?_
      · exact ExecStmt.requireTrue
          (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · exact ExecBlock.consRevert
          (ExecStmt.requireFalse
            (evalExpr_createAuction_error_offset_bounds_false evm hoffBound))

theorem execCreateAuctionErrorStringGuardPrefix {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt} {result : ExecResult}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (htail : ExecBlock auctionConfig (createAuctionErrLengthFrame out off len) evm tail result) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
        tail)
      result := by
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
    (.require (errorStringReturndataLongEnough "err"))
    (createAuctionErrFrame out) evm
    ([ .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
       .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
       .require (errorStringOffsetInBounds "err" "_errOffset"),
       .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
      tail)
    result ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_long_enough_true evm hlong)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrFrame out) evm
      (.letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"))
      (createAuctionErrOffsetFrame out off) evm
      ([ .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
        tail)
      result ?_ ?_
    · simpa [createAuctionErrFrame, createAuctionErrOffsetFrame] using
        ExecStmt.letDecl
          (evalExpr_createAuction_error_offset_decode_ok evm hlenOut hsmall hoff)
    · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
        (.require (.binary .le (.var "_errOffset") solcMaxU64Expr))
        (createAuctionErrOffsetFrame out off) evm
        ([ .require (errorStringOffsetInBounds "err" "_errOffset"),
           .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset") ] ++
          tail)
        result ?_ ?_
      · exact ExecStmt.requireTrue
          (evalExpr_createAuction_error_offset_max_true evm hoffMax)
      · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
          (.require (errorStringOffsetInBounds "err" "_errOffset"))
          (createAuctionErrOffsetFrame out off) evm
          ([ .letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset") ] ++ tail)
          result ?_ ?_
        · exact ExecStmt.requireTrue
            (evalExpr_createAuction_error_offset_bounds_true evm hoffBound)
        · refine @ExecBlock.consNormal auctionConfig (createAuctionErrOffsetFrame out off) evm
            (.letDecl "_errLength" (some uint256)
              (errorStringLengthDecode "err" "_errOffset"))
            (createAuctionErrLengthFrame out off len) evm tail result ?_ htail
          simpa [createAuctionErrOffsetFrame, createAuctionErrLengthFrame] using
            ExecStmt.letDecl
              (evalExpr_createAuction_error_length_decode_ok evm hlenOut hoffBound hlenWord)

theorem execCreateAuctionErrorStringLengthMaxReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr) ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_createAuction_error_length_max_false evm hlenMax))

theorem execCreateAuctionErrorStringPayloadBoundsReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength") ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
    (createAuctionErrLengthFrame out off len) evm
    ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm hlenMax)
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_createAuction_error_payload_bounds_false evm hpayloadBound))

theorem execCreateAuctionErrorStringAllocU64Reverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {tail : List Stmt}
    (hlenOut : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      ([ .require (errorStringReturndataLongEnough "err"),
         .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
         .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
         .require (errorStringOffsetInBounds "err" "_errOffset"),
         .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
         .require (.binary .le (.var "_errLength") solcMaxU64Expr),
         .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
         .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
      .reverted := by
  refine execCreateAuctionErrorStringGuardPrefix hlenOut hlong hsmall hoff hoffMax
    hoffBound hlenWord ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.require (.binary .le (.var "_errLength") solcMaxU64Expr))
    (createAuctionErrLengthFrame out off len) evm
    ([ .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
       .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
    .reverted ?_ ?_
  · exact ExecStmt.requireTrue (evalExpr_createAuction_error_length_max_true evm hlenMax)
  · refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
      (.require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"))
      (createAuctionErrLengthFrame out off len) evm
      ([ .require (errorStringAllocationWithinU64 "_errOffset" "_errLength") ] ++ tail)
      .reverted ?_ ?_
    · exact ExecStmt.requireTrue
        (evalExpr_createAuction_error_payload_bounds_true evm hpayloadBound)
    · exact ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_createAuction_error_alloc_u64_false evm hoffMax hlenMax halloc))

theorem execCreateAuctionErrorStringThenReturns {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")))
    (createAuctionErrDecodedFrame out off len decoded) evm
    [ .require (.unary .not (.storage pausedRef)),
      .assign .storage pausedRef (.boolLit true) ]
    (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) ?_ ?_
  · simpa [createAuctionErrLengthFrame, createAuctionErrDecodedFrame] using
      ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm hlen hdec)
  · have hbaseDecoded :
        (createAuctionErrDecodedFrame out off len decoded).locals.get? pausedRef.base = none := by
      simp [createAuctionErrDecodedFrame, pausedRef]
    refine @ExecBlock.consNormal
      auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
      (.require (.unary .not (.storage pausedRef)))
      (createAuctionErrDecodedFrame out off len decoded) evm
      [ .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm)) ?_ ?_
    · have hnotPausedDecoded :
          evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
            (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
        simpa [createAuctionErrDecodedFrame] using
          evalExpr_pause_notPaused_true_frame evm
            (createAuctionErrDecodedFrame out off len decoded).locals hbaseDecoded hnotPaused
      exact ExecStmt.requireTrue hnotPausedDecoded
    · have htrueDecoded :
          evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
            (.boolLit true) = .ok (.bool true) := by
        simpa [createAuctionErrDecodedFrame] using
          evalExpr_pause_true_frame evm (createAuctionErrDecodedFrame out off len decoded).locals
      have hassignDecoded :
          assignStorageRef? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
              .storage pausedRef (.bool true) =
            .ok (createAuctionErrDecodedFrame out off len decoded, auctionPausePostState evm) := by
        simpa [createAuctionErrDecodedFrame] using
          auctionPauseAssign_frame evm (createAuctionErrDecodedFrame out off len decoded).locals
            hbaseDecoded
      exact @ExecBlock.consNormal
        auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
        (.assign .storage pausedRef (.boolLit true))
        (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm) []
        (.ok (createAuctionErrDecodedFrame out off len decoded) (auctionPausePostState evm))
        (ExecStmt.assign htrueDecoded hassignDecoded) ExecBlock.nil

theorem execCreateAuctionErrorStringThenDecodeReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert
      (evalExpr_createAuction_error_decode_revert_lengthFrame evm hlen hdec))

theorem execCreateAuctionErrorStringThenPausedReverts {evm : EVM.State} {out : ByteArray}
    {off len : Nat} {decoded : Value}
    (hlen : 4 ≤ out.size) (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecBlock auctionConfig (createAuctionErrFrame out) evm
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
  refine execCreateAuctionErrorStringGuardBlock hlen hlong hsmall hoff hoffMax hoffBound
    hlenWord hlenMax hpayloadBound halloc ?_
  refine @ExecBlock.consNormal auctionConfig (createAuctionErrLengthFrame out off len) evm
    (.letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")))
    (createAuctionErrDecodedFrame out off len decoded) evm
    [ .require (.unary .not (.storage pausedRef)),
      .assign .storage pausedRef (.boolLit true) ]
    .reverted ?_ ?_
  · simpa [createAuctionErrLengthFrame, createAuctionErrDecodedFrame] using
      ExecStmt.letDecl (evalExpr_createAuction_error_decode_ok_lengthFrame evm hlen hdec)
  · have hbaseDecoded :
        (createAuctionErrDecodedFrame out off len decoded).locals.get? pausedRef.base = none := by
      simp [createAuctionErrDecodedFrame, pausedRef]
    have hpausedDecoded :
        evalExpr? auctionConfig (createAuctionErrDecodedFrame out off len decoded) evm
          (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
      simpa [createAuctionErrDecodedFrame] using
        evalExpr_pause_notPaused_false_frame evm
          (createAuctionErrDecodedFrame out off len decoded).locals hbaseDecoded hpaused
    exact ExecBlock.consRevert (ExecStmt.requireFalse hpausedDecoded)

theorem auctionCreateAuctionBodyReverts_callFailure_empty {evm evmCall : EVM.State}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, ByteArray.empty) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert
    (ExecStmt.iteCondRevert (evalExpr_createAuction_emptyErr_slice_revert evmCall))

theorem auctionCreateAuctionBodyReverts_callFailure_short {evm evmCall : EVM.State}
    {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hshort : out.size < 4) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert
    (ExecStmt.iteCondRevert (evalExpr_createAuction_err_slice_revert evmCall hshort))

theorem auctionCreateAuctionBodyReverts_callFailure_nonError {evm evmCall : EVM.State}
    {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse (evalExpr_createAuction_err_slice_false evmCall hlen hsel) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure]))

theorem auctionCreateAuctionBodyReturns_callFailure_errorString {evm evmCall : EVM.State}
    {out : ByteArray} {off len : Nat} {decoded : Value}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      (.returned (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall) none) := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      (.ok (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall)) :=
    execCreateAuctionErrorStringThenReturns hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec hnotPaused
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      (.ok (createAuctionErrDecodedFrame out off len decoded)
        (auctionPausePostState evmCall)) := by
    exact ExecBlock.consNormal
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
      ExecBlock.nil
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringShort
    {evm evmCall : EVM.State} {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hshort : out.size < 68) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue (evalExpr_createAuction_err_slice_true evmCall hlen hsel) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_createAuction_error_long_enough_false evmCall hshort))

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetMax
    {evm evmCall : EVM.State} {out : ByteArray} {off : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringOffsetMaxReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax
        (tail := [
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetBounds
    {evm evmCall : EVM.State} {out : ByteArray} {off : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringOffsetBoundsReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound
        (tail := [
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringLengthMax
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringLengthMaxReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax
        (tail := [
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringPayloadBounds
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringPayloadBoundsReverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound
        (tail := [
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringAllocU64
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted := by
    simpa using
      (execCreateAuctionErrorStringAllocU64Reverts (evm := evmCall) hlen hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc
        (tail := [
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]))
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringDecode
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted :=
    execCreateAuctionErrorStringThenDecodeReverts hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionCreateAuctionBodyReverts_callFailure_errorStringPaused
    {evm evmCall : EVM.State} {out : ByteArray} {off len : Nat} {decoded : Value}
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm createAuctionFn.body
      .reverted := by
  dsimp [createAuctionFn]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.checkedCallFail (evalExpr_createAuction_nouns evm)
    (evalExpr_createAuction_zero evm) (evalExprs_createAuction_mint_args evm) hcall ?_
  have hthen : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .require (errorStringReturndataLongEnough "err"),
        .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
        .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
        .require (errorStringOffsetInBounds "err" "_errOffset"),
        .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
        .require (.binary .le (.var "_errLength") solcMaxU64Expr),
        .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
        .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
        .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
        .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ]
      .reverted :=
    execCreateAuctionErrorStringThenPausedReverts hlen hlong hsmall hoff hoffMax hoffBound
      hlenWord hlenMax hpayloadBound halloc hdec hpaused
  have hcatch : ExecBlock auctionConfig (createAuctionErrFrame out) evmCall
      [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
          (.bytesLit errorStringSelector))
        [ .require (errorStringReturndataLongEnough "err"),
          .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
          .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
          .require (errorStringOffsetInBounds "err" "_errOffset"),
          .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
          .require (.binary .le (.var "_errLength") solcMaxU64Expr),
          .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
          .require (errorStringAllocationWithinU64 "_errOffset" "_errLength"),
          .require (errorStringAllocationNoWrap "_errOffset" "_errLength"),
          .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
          .require (.unary .not (.storage pausedRef)),
          .assign .storage pausedRef (.boolLit true) ]
        [ .require (.boolLit false) ] ]
      .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.iteTrue
        (by
          simpa [createAuctionErrFrame] using
            evalExpr_createAuction_err_slice_true evmCall hlen hsel)
        hthen)
  simpa [createAuctionErrFrame] using hcatch

theorem auctionUnpauseBodyReverts_create_callFailure_empty (evm evmCall : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, ByteArray.empty) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_empty hcall))

theorem auctionUnpauseBodyReverts_create_callFailure_short (evm evmCall : EVM.State)
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hshort : out.size < 4) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_short hcall hshort))

theorem auctionUnpauseBodyReverts_create_callFailure_nonError (evm evmCall : EVM.State)
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_nonError hcall hlen hsel))

theorem auctionUnpauseBodyReturns_create_callFailure_errorString (evm evmCall : EVM.State)
    {out : ByteArray} {off len : Nat} {decoded : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hnotPaused :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_c" none)
        (auctionPausePostState evmCall) none) := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_) ExecBlock.nil
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact internalCallFunctionReturn
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (calleeEvm := auctionPausePostState evmCall)
    (name := "_createAuction") (args := []) (retVar := "_c") (argVals := [])
    (callee := createAuctionFn) (locals := ∅)
      (calleeSolm := createAuctionErrDecodedFrame out off len decoded)
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionCreateAuctionBodyReturns_callFailure_errorString hcall hlen hsel hlong hsmall
        hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec hnotPaused)

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringShort
    (evm evmCall : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hshort : out.size < 68) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringShort hcall hlen hsel hshort))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetMax
    (evm evmCall : EVM.State) {out : ByteArray} {off : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : ABI.solcMaxU64 < off) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetMax hcall hlen hsel hlong
      hsmall hoff hoffMax))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetBounds
    (evm evmCall : EVM.State) {out : ByteArray} {off : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : out.size < off + 36) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringOffsetBounds hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringLengthMax
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : ABI.solcMaxU64 < len) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringLengthMax hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound hlenWord hlenMax))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringPayloadBounds
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : out.size < off + len + 36) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringPayloadBounds hcall hlen hsel
      hlong hsmall hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringAllocU64
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64) (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64) (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringAllocU64 hcall hlen hsel hlong
      hsmall hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringDecode
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringDecode hcall hlen hsel hlong hsmall
      hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec))

theorem auctionUnpauseBodyReverts_create_callFailure_errorStringPaused
    (evm evmCall : EVM.State) {out : ByteArray} {off len : Nat} {decoded : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hcond :
      evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } (auctionUnpausePostState evm)
        (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
          (.storage (aField "settled"))) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionUnpausePostState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionUnpausePostState evm)
            (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (false, evmCall, out) true)
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector)
    (hlong : 68 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hoffBound : off + 36 ≤ out.size)
    (hlenWord : ABI.readNat? (out.extract 4 out.size).toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ out.size)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded)
    (hpausedCall :
      UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  let evm' := auctionUnpausePostState evm
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_unpause_false evm) (auctionUnpauseAssign evm)) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue (by simpa [evm'] using hcond) ?_)
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := evm') (name := "_createAuction") (args := []) (retVar := "_c")
    (argVals := []) (callee := createAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionCreateAuctionBodyReverts_callFailure_errorStringPaused hcall hlen hsel hlong hsmall
      hoff hoffMax hoffBound hlenWord hlenMax hpayloadBound halloc hdec hpausedCall))

theorem auctionUnpausePostMap_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    accountMapEquiv (auctionUnpausePostMap σ I)
      (auctionUnpausePostState (initState cA gh bl σ σ₀ g A I)).accountMap := by
  apply accountMapEquiv.of_eq
  simp [auctionUnpausePostMap, auctionUnpausePostState, initState,
    storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem auctionUnpausePostState_equiv {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVMStateEquiv (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I))
      (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hσ : EVMStateEquiv (initState cA gh bl σ_evm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I) := by
    exact EVMStateEquiv.initState hAccounts
  exact hσ.storageStore_codeOwner ⟨51⟩ (by
    have hword : auctionSlotWord ⟨51⟩ σ_evm I = auctionSlotWord ⟨51⟩ σ_solm I := by
      simpa [auctionSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨51⟩ (default : UInt256)
    simpa [initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
      congrArg auctionPausedSetFalseWord hword)

theorem auctionUnpausePost_mintTarget_eq {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (AccountAddress.ofNat
        ((UInt256.land (auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I)
          solcAddrMask).toNat)) =
      EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad
            (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
            (auctionUnpausePostState
              (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
            ⟨201⟩) solcAddrMask).toNat)) := by
  have hslot : auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I =
      auctionSlotWord ⟨201⟩ σ_evm I := by
    simpa [auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ_evm I.codeOwner ⟨201⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ_evm I)) (by decide)
  have hload :
      Solm.EVM.storageLoad
          (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
          (auctionUnpausePostState
            (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
          ⟨201⟩ =
        auctionSlotWord ⟨201⟩ σ_solm I := by
    let evm := initState cA gh bl σ_solm σ₀ g A I
    have henv : (auctionUnpausePostState evm).executionEnv = evm.executionEnv := by
      simp [auctionUnpausePostState, storageStore_executionEnv]
    have hload0 : Solm.EVM.storageLoad (auctionUnpausePostState evm)
          evm.executionEnv.codeOwner ⟨201⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
      simpa [auctionUnpausePostState] using
        (storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
        (readSlot := ⟨201⟩) (writeSlot := ⟨51⟩)
        (val := auctionPausedSetFalseWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))
          (by decide))
    have hload1 : Solm.EVM.storageLoad (auctionUnpausePostState evm)
          (auctionUnpausePostState evm).executionEnv.codeOwner ⟨201⟩ =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
      simpa [henv] using hload0
    simpa [evm, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
      using hload1
  have hbase : auctionSlotWord ⟨201⟩ σ_evm I = auctionSlotWord ⟨201⟩ σ_solm I := by
    simpa [auctionSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨201⟩ (default : UInt256)
  rw [hslot, hload, hbase]

theorem auctionUnpauseMintCall_transport {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {z : Bool}
    {o : ByteArray} {A' : Substate}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM auctionConfig
      { initState cA gh bl σ_evm σ₀ g A I with accountMap := auctionUnpausePostMap σ_evm I }
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (auctionSlotWord ⟨201⟩ (auctionUnpausePostMap σ_evm I) I)
          solcAddrMask).toNat))) "mint" 0 []
      (z,
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) true) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM auctionConfig
        (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad
              (auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I))
              (auctionUnpausePostState
                (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
              ⟨201⟩) solcAddrMask).toNat))) "mint" 0 []
        (z,
          { auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I) with
            accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, o) true ∧
      EVMStateEquiv
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }
        { auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I) with
          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  let evmE0 := { initState cA gh bl σ_evm σ₀ g A I with
    accountMap := auctionUnpausePostMap σ_evm I }
  let evmS0 := auctionUnpausePostState (initState cA gh bl σ_solm σ₀ g A I)
  have htarget := auctionUnpausePost_mintTarget_eq (cA := cA) (gh := gh) (bl := bl)
    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have hcallTarget : typedCallViaEVM auctionConfig evmE0
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad evmS0 evmS0.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 []
      (z,
        { initState cA gh bl σ_evm σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) true := by
    simpa [evmE0, evmS0] using htarget ▸ hcall
  have hpostE : accountMapEquiv (auctionUnpausePostMap σ_evm I)
      (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I)).accountMap := by
    exact auctionUnpausePostMap_accountMap
  have hpostState : EVMStateEquiv
      (auctionUnpausePostState (initState cA gh bl σ_evm σ₀ g A I)) evmS0 := by
    simpa [evmS0] using auctionUnpausePostState_equiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  have hAccountsStart : accountMapEquiv evmE0.accountMap evmS0.accountMap := by
    simpa [evmE0] using accountMapEquiv.trans hpostE hpostState.accountMap
  obtain ⟨σ'_solm, A'_solm, hcallS, hσ'⟩ :=
    typedCallViaEVM_accountMapEquiv hcallTarget hAccountsStart
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by simp [evmE0, evmS0, auctionUnpausePostState, initState, storageStore_createdAccounts])
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, Solm.EVM.storageStore,
          State.lookupAccount]
        cases σ_solm.find? I.codeOwner <;> rfl)
      (by
        simp [evmE0, evmS0, auctionUnpausePostState, initState, storageStore_executionEnv])
  refine ⟨σ'_solm, A'_solm, ?_, ?_⟩
  · simpa [evmS0] using hcallS
  · refine ⟨?_, ?_, ?_⟩
    · simp [evmS0, auctionUnpausePostState, initState, storageStore_executionEnv]
    · rfl
    · exact hσ'

end Auction
