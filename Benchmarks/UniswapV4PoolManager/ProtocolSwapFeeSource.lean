import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeWords
import Benchmarks.UniswapV4PoolManager.WordBoundedArithmeticSource
import Benchmarks.UniswapV4PoolManager.WordNarrowArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev protocolFeeZeroFunction : FunctionDecl := contract.functions[95]!
abbrev protocolFeeOneFunction : FunctionDecl := contract.functions[97]!
abbrev protocolSwapFeeFunction : FunctionDecl := contract.functions[101]!
theorem protocolFeeZero_lookup : lookupCallable? contract "ProtocolFeeLibrary_getZeroForOneFee" =
    some protocolFeeZeroFunction.toCallable := rfl
theorem protocolFeeOne_lookup : lookupCallable? contract "ProtocolFeeLibrary_getOneForZeroFee" =
    some protocolFeeOneFunction.toCallable := rfl
theorem protocolSwapFee_lookup : lookupCallable? contract "ProtocolFeeLibrary_calculateSwapFee" =
    some protocolSwapFeeFunction.toCallable := rfl

theorem protocolFeeZeroBody {f : Frame} {evm : State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm protocolFeeZeroFunction.body
      (.returned f evm (some [.int (Int.ofNat (protocolFeeZeroWord fee).toNat)])) := by
  have he := evalUintWordAnd (y := UInt256.ofNat 4095) ⟨24, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 4095) = .ok (.int (Int.ofNat (UInt256.ofNat 4095).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have hcast := evalExpr_cast_int (intType := .uint ⟨16, by decide⟩) he
  have hb : (protocolFeeZeroWord fee).toNat < 2^16 :=
    lt_of_lt_of_le (protocolFeeZeroWord_bound fee) (by decide)
  have hn := normalizeInt_uint_eq_self ⟨16, by decide⟩ (Int.ofNat (protocolFeeZeroWord fee).toNat)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hb)
  exact .execBlockRet (ABlock.start.returns (hcast.trans (congrArg (EvalResult.ok ∘ Value.int) hn)))

theorem protocolFeeOneBody {f : Frame} {evm : State} {fee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm protocolFeeOneFunction.body
      (.returned f evm (some [.int (Int.ofNat (protocolFeeOneWord fee).toNat)])) := by
  have he := evalUintWordShr (n := 12) ⟨24, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 12) = .ok (.int (Int.ofNat 12)) by simp only [evalExpr?, pure]; rfl)
  have hcast := evalExpr_cast_int (intType := .uint ⟨16, by decide⟩) he
  have hb : (protocolFeeOneWord fee).toNat < 2^16 :=
    lt_of_lt_of_le (protocolFeeOneWord_bound hc) (by decide)
  have hn := normalizeInt_uint_eq_self ⟨16, by decide⟩ (Int.ofNat (protocolFeeOneWord fee).toNat)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hb)
  exact .execBlockRet (ABlock.start.returns (hcast.trans (congrArg (EvalResult.ok ∘ Value.int) hn)))

theorem protocolFeeZeroCall {f : Frame} {evm : State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "ProtocolFeeLibrary_getZeroForOneFee" [e] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (protocolFeeZeroWord fee).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.int (Int.ofNat (protocolFeeZeroWord fee).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact protocolFeeZero_lookup) rfl
  exact protocolFeeZeroBody (store_get_self _ _ _) hc

theorem protocolFeeOneCall {f : Frame} {evm : State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "ProtocolFeeLibrary_getOneForZeroFee" [e] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (protocolFeeOneWord fee).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat)])
    (value := some [.int (Int.ofNat (protocolFeeOneWord fee).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact protocolFeeOne_lookup) rfl
  exact protocolFeeOneBody (store_get_self _ _ _) hc

theorem protocolSwapFeeBody {f : Frame} {evm : State} {fee lpFee : UInt256}
    (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat)))
    (hl : f.locals.get? "lpFee" = some (.int (Int.ofNat lpFee.toNat)))
    (hc : fee.toNat < 2^16) (hlc : lpFee.toNat < 2^24) :
    ExecFuncBody config f evm protocolSwapFeeFunction.body
      (.returned (valueLocal f "protocol" (.int (Int.ofNat (protocolFeeZeroWord fee).toNat))) evm
        (some [.int (Int.ofNat (protocolSwapFeeWord fee lpFee).toNat)])) := by
  let f1 := valueLocal f "protocol" (.int (Int.ofNat (protocolFeeZeroWord fee).toNat))
  have hand := evalUintWordAnd (y := UInt256.ofNat 4095) ⟨16, by decide⟩ hc (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 4095) = .ok (.int (Int.ofNat (UInt256.ofNat 4095).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have hinit := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hand
  rw [normalizeInt_uint256_word] at hinit
  have hp := evalLocalValue (cfg := config) (f := f1) (evm := evm) (store_get_self _ _ _)
  have hl' := evalLocalValue (cfg := config) (f := f1) (evm := evm)
    ((store_get_ne _ _ (by decide : ("protocol" == "lpFee") = false)).trans hl)
  have hadd := evalBoundedWordAdd hp hl' (protocolSwapFee_add_bound fee hlc)
  have hmul := evalBoundedWordMul hp hl' (protocolSwapFee_mul_bound fee hlc)
  have hdiv := evalWordDiv (y := UInt256.ofNat 1000000) hmul
    (show evalExpr? config f1 evm (.intLit 1000000) = .ok (.int (Int.ofNat (UInt256.ofNat 1000000).toNat)) by
      simp only [evalExpr?, pure]; rfl) (by decide)
  exact .execBlockRet (ExecBlock.consNormal (ExecStmt.letDecl hinit)
    (ABlock.start.returns (evalUintWordSubWidth ⟨24, by decide⟩ (UInt256.ofNat 16777215) rfl hadd hdiv)))

theorem protocolSwapFeeCall {f : Frame} {evm : State} {ef el : Expr} {fee lpFee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^16) (hlc : lpFee.toNat < 2^24)
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat lpFee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "ProtocolFeeLibrary_calculateSwapFee" [ef, el] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (protocolSwapFeeWord fee lpFee).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat fee.toNat), .int (Int.ofNat lpFee.toNat)])
    (value := some [.int (Int.ofNat (protocolSwapFeeWord fee lpFee).toNat)])
    (by simp only [evalExprs?, he, hl, bind, EvalResult.bind, pure])
    (by rw [hf]; exact protocolSwapFee_lookup) rfl
  exact protocolSwapFeeBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "lpFee") = false)).trans (store_get_self _ _ _)) hc hlc

end Benchmarks.UniswapV4PoolManager
