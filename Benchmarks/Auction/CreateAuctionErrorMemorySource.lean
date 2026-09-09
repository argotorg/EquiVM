import Benchmarks.Auction.CreateAuctionWithMemorySource
import Benchmarks.Auction.SourceLocalExpression
import Benchmarks.Auction.MemoryAllocationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction.CreateMemory

local macro "source_local" : tactic => `(tactic|
  repeat' first
    | apply SourceLocalExpression.intLit
    | apply SourceLocalExpression.boolLit
    | apply SourceLocalExpression.bytesLit
    | apply SourceLocalExpression.var
    | apply SourceLocalExpression.length
    | apply SourceLocalExpression.binary
    | apply SourceLocalExpression.unary
    | apply SourceLocalExpression.decode
    | apply SourceLocalExpression.slice
    | decide)

def createAuctionErrFrame (free : UInt256) (out : ByteArray) : Frame :=
  { contract := auctionContract
    locals := (auctionCreateAuctionMemoryLocals free).insert "err" (.bytes out) }

def createAuctionErrOffsetFrame (free : UInt256) (out : ByteArray) (off : Nat) : Frame :=
  { contract := auctionContract
    locals := ((createAuctionErrFrame free out).locals.insert "_errOffset" (.int (Int.ofNat off))) }

def createAuctionErrLengthFrame (free : UInt256) (out : ByteArray) (off len : Nat) : Frame :=
  { contract := auctionContract
    locals := ((createAuctionErrOffsetFrame free out off).locals.insert "_errLength"
      (.int (Int.ofNat len))) }

def createAuctionErrDecodedFrame (free : UInt256) (out : ByteArray) (off len : Nat)
    (decoded : Value) : Frame :=
  { contract := auctionContract
    locals := ((createAuctionErrLengthFrame free out off len).locals.insert "_errString" decoded) }

theorem createAuctionErrFrame_eval_eq (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {e : Expr} (he : SourceLocalExpression ["err", "_errOffset", "_errLength"] e) :
    evalExpr? auctionConfig (createAuctionErrFrame free out) evm e =
      evalExpr? auctionConfig (Auction.createAuctionErrFrame out) evm e := by
  apply he.eval_eq
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals simp [createAuctionErrFrame, Auction.createAuctionErrFrame, auctionCreateAuctionMemoryLocals]

theorem createAuctionErrOffsetFrame_eval_eq (evm : EVM.State) (free : UInt256) {out : ByteArray} {off : Nat}
    {e : Expr} (he : SourceLocalExpression ["err", "_errOffset", "_errLength"] e) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm e =
      evalExpr? auctionConfig (Auction.createAuctionErrOffsetFrame out off) evm e := by
  apply he.eval_eq
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals simp [createAuctionErrFrame, createAuctionErrOffsetFrame, Auction.createAuctionErrOffsetFrame, auctionCreateAuctionMemoryLocals, Std.HashMap.getElem_insert]

theorem createAuctionErrLengthFrame_eval_eq (evm : EVM.State) (free : UInt256) {out : ByteArray} {off len : Nat}
    {e : Expr} (he : SourceLocalExpression ["err", "_errOffset", "_errLength"] e) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm e =
      evalExpr? auctionConfig (Auction.createAuctionErrLengthFrame out off len) evm e := by
  apply he.eval_eq
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals simp [createAuctionErrFrame, createAuctionErrOffsetFrame, createAuctionErrLengthFrame, Auction.createAuctionErrLengthFrame, auctionCreateAuctionMemoryLocals, Std.HashMap.getElem_insert]

theorem evalExpr_createAuction_err_selector_slice_revert (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hshort : out.size < 4) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm (.bytesSlice (.var "err") (.intLit 0) (.intLit 4)) = .revert := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_err_selector_slice_revert evm hshort

theorem evalExpr_createAuction_err_selector_slice_ok (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hlen : 4 ≤ out.size) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm (.bytesSlice (.var "err") (.intLit 0) (.intLit 4)) =
        .ok (.bytes (out.extract 0 4)) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_err_selector_slice_ok evm hlen

theorem evalExpr_createAuction_err_slice_revert (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hshort : out.size < 4) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .revert := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_err_slice_revert evm hshort

theorem evalExpr_createAuction_err_slice_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 ≠ errorStringSelector) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .ok (.bool false) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_err_slice_false evm hlen hsel

theorem evalExpr_createAuction_err_slice_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hlen : 4 ≤ out.size) (hsel : out.extract 0 4 = errorStringSelector) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm
      (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
        (.bytesLit errorStringSelector)) = .ok (.bool true) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_err_slice_true evm hlen hsel

theorem evalExpr_createAuction_error_long_enough_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hlong : 68 ≤ out.size) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm (errorStringReturndataLongEnough "err") = .ok (.bool true) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_long_enough_true evm hlong

theorem evalExpr_createAuction_error_long_enough_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    (hshort : out.size < 68) :
    evalExpr? auctionConfig
      (createAuctionErrFrame free out)
      evm (errorStringReturndataLongEnough "err") = .ok (.bool false) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_long_enough_false evm hshort

theorem evalExpr_createAuction_error_offset_decode_ok (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off : Nat} (hlen : 4 ≤ out.size)
    (hsmall : (out.extract 4 out.size).size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? (out.extract 4 out.size).toList 0 = some off) :
    evalExpr? auctionConfig (createAuctionErrFrame free out) evm (errorStringOffsetDecode "err") =
      .ok (.int (Int.ofNat off)) := by
  rw [createAuctionErrFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_offset_decode_ok evm hlen hsmall hoff

theorem evalExpr_createAuction_error_offset_max_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off : Nat} (hoffMax : off ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm
      (.binary .le (.var "_errOffset") solcMaxU64Expr) = .ok (.bool true) := by
  rw [createAuctionErrOffsetFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_offset_max_true evm hoffMax

theorem evalExpr_createAuction_error_offset_max_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off : Nat} (hoffMax : ABI.solcMaxU64 < off) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm
      (.binary .le (.var "_errOffset") solcMaxU64Expr) = .ok (.bool false) := by
  rw [createAuctionErrOffsetFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_offset_max_false evm hoffMax

theorem evalExpr_createAuction_error_offset_bounds_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off : Nat} (hoffBound : off + 36 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm
      (errorStringOffsetInBounds "err" "_errOffset") = .ok (.bool true) := by
  rw [createAuctionErrOffsetFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_offset_bounds_true evm hoffBound

theorem evalExpr_createAuction_error_offset_bounds_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off : Nat} (hoffBound : out.size < off + 36) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm
      (errorStringOffsetInBounds "err" "_errOffset") = .ok (.bool false) := by
  rw [createAuctionErrOffsetFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_offset_bounds_false evm hoffBound

theorem evalExpr_createAuction_error_length_decode_ok (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} (hlenOut : 4 ≤ out.size) (hoffBound : off + 36 ≤ out.size)
    (hlen : ABI.readNat? (out.extract 4 out.size).toList off = some len) :
    evalExpr? auctionConfig (createAuctionErrOffsetFrame free out off) evm
      (errorStringLengthDecode "err" "_errOffset") = .ok (.int (Int.ofNat len)) := by
  rw [createAuctionErrOffsetFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_length_decode_ok evm hlenOut hoffBound hlen

theorem evalExpr_createAuction_error_length_max_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} (hlenMax : len ≤ ABI.solcMaxU64) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.binary .le (.var "_errLength") solcMaxU64Expr) = .ok (.bool true) := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_length_max_true evm hlenMax

theorem evalExpr_createAuction_error_length_max_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} (hlenMax : ABI.solcMaxU64 < len) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.binary .le (.var "_errLength") solcMaxU64Expr) = .ok (.bool false) := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_length_max_false evm hlenMax

theorem evalExpr_createAuction_error_payload_bounds_true (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} (hpayloadBound : off + len + 36 ≤ out.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringPayloadInBounds "err" "_errOffset" "_errLength") = .ok (.bool true) := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_payload_bounds_true evm hpayloadBound

theorem evalExpr_createAuction_error_payload_bounds_false (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} (hpayloadBound : out.size < off + len + 36) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringPayloadInBounds "err" "_errOffset" "_errLength") = .ok (.bool false) := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_payload_bounds_false evm hpayloadBound

theorem evalExpr_createAuction_error_decode_ok_lengthFrame (evm : EVM.State) (free : UInt256) {out : ByteArray}
    {off len : Nat} {decoded : Value} (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = some decoded) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.abiDecode .string (errorStringPayload "err")) = .ok decoded := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_decode_ok_lengthFrame evm hlen hdec

theorem evalExpr_createAuction_error_decode_revert_lengthFrame (evm : EVM.State) (free : UInt256)
    {out : ByteArray} {off len : Nat} (hlen : 4 ≤ out.size)
    (hdec : ABI.decodeReturnValue? .string (out.extract 4 out.size) = none) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.abiDecode .string (errorStringPayload "err")) = .revert := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_decode_revert_lengthFrame evm hlen hdec

theorem evalExpr_createAuction_error_rounded_alloc_ok (evm : EVM.State) (free : UInt256)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringRoundedAllocSize (.var "_errOffset") (.var "_errLength")) =
        .ok (.int (Int.ofNat (errorStringRoundedAllocNat off len))) := by
  rw [createAuctionErrLengthFrame_eval_eq evm free (by
    source_local)]
  exact Auction.evalExpr_createAuction_error_rounded_alloc_ok evm hsum

theorem evalExpr_createAuction_error_new_free_ok (evm : EVM.State) (free : UInt256)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringNewFreePtr "_errOffset" "_errLength" (.var "_freePtr")) =
        .ok (.int (Int.ofNat (free.toNat + errorStringRoundedAllocNat off len))) := by
  apply evalExpr_add_nat
  · simp [evalExpr?, createAuctionErrLengthFrame, createAuctionErrOffsetFrame,
      createAuctionErrFrame, auctionCreateAuctionMemoryLocals, Std.HashMap.getElem_insert,
      EvalResult.ofOption]
  · exact evalExpr_createAuction_error_rounded_alloc_ok evm free hsum

theorem evalExpr_createAuction_error_alloc_u64 (evm : EVM.State) (free : UInt256)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringAllocationWithinU64 "_errOffset" "_errLength" (.var "_freePtr")) =
        .ok (.bool (decide (free.toNat + errorStringRoundedAllocNat off len ≤ ABI.solcMaxU64))) := by
  change evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.binary .le (errorStringNewFreePtr "_errOffset" "_errLength" (.var "_freePtr"))
        solcMaxU64Expr) = _
  rw [Solm.evalExpr?.eq_def]
  simp only [evalExpr_createAuction_error_new_free_ok evm free hsum,
    solcMaxU64Expr, evalExpr?, bind, EvalResult.bind, evalBinaryOp?, pure]
  simp only [EvalResult.ok.injEq, Value.bool.injEq, decide_eq_decide]
  exact Int.ofNat_le

theorem evalExpr_createAuction_error_alloc_no_wrap (evm : EVM.State) (free : UInt256)
    {out : ByteArray} {off len : Nat} (hsum : off + len + 63 < UInt256.size) :
    evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (errorStringAllocationNoWrap "_errOffset" "_errLength" (.var "_freePtr")) =
        .ok (.bool true) := by
  change evalExpr? auctionConfig (createAuctionErrLengthFrame free out off len) evm
      (.binary .ge (errorStringNewFreePtr "_errOffset" "_errLength" (.var "_freePtr"))
        (.var "_freePtr")) = _
  rw [Solm.evalExpr?.eq_def]
  simp only [evalExpr_createAuction_error_new_free_ok evm free hsum, bind, EvalResult.bind]
  simp [evalExpr?, createAuctionErrLengthFrame, createAuctionErrOffsetFrame,
    createAuctionErrFrame, auctionCreateAuctionMemoryLocals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, evalBinaryOp?]

end Auction.CreateMemory
