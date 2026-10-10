import Benchmarks.UniswapV4PoolManager.WordOperationsSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def slot0FeeField (packed : UInt256) (shift : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight packed (UInt256.ofNat shift)) (UInt256.ofNat 16777215)

theorem slot0FeeField_bound (packed : UInt256) (shift : Nat) : (slot0FeeField packed shift).toNat < 2^24 := by
  rw [slot0FeeField, uland_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by decide)

theorem slot0FeeField_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr} {packed : UInt256}
    (shift : Nat) (hs : shift < 256) (he : evalExpr? cfg f evm e = .ok (wordBytes32Value packed)) :
    evalExpr? cfg f evm (.cast (.binary (.shr (.uint ⟨256, by decide⟩))
      (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit shift)) (.elem (.int (.uint ⟨24, by decide⟩)))) =
      .ok (.int (Int.ofNat (slot0FeeField packed shift).toNat)) := by
  have hshift := evalWordShr hs (evalCastValue he (castBytes32ToUint256 packed))
    (show evalExpr? cfg f evm (.intLit shift) = .ok (.int (Int.ofNat shift)) by
      simp only [evalExpr?, pure, Int.ofNat_eq_natCast])
  simpa only [normalizeUintWord ⟨24, by decide⟩ _ (UInt256.ofNat 16777215) rfl, slot0FeeField] using
    evalExpr_cast_int (intType := .uint ⟨24, by decide⟩) hshift

abbrev slot0GetProtocolFunction : FunctionDecl := contract.functions[96]!
abbrev slot0GetLPFeeFunction : FunctionDecl := contract.functions[100]!
theorem slot0GetProtocol_lookup : lookupCallable? contract "Slot0Library_protocolFee" =
    some slot0GetProtocolFunction.toCallable := rfl
theorem slot0GetLPFee_lookup : lookupCallable? contract "Slot0Library_lpFee" =
    some slot0GetLPFeeFunction.toCallable := rfl

theorem slot0GetProtocolBody {f : Frame} {evm : State} {packed : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed)) :
    ExecFuncBody config f evm slot0GetProtocolFunction.body
      (.returned f evm (some [.int (Int.ofNat (slot0FeeField packed 184).toNat)])) :=
  .execBlockRet (ABlock.start.returns (slot0FeeField_eval 184 (by decide) (evalLocalValue hp)))

theorem slot0GetLPFeeBody {f : Frame} {evm : State} {packed : UInt256}
    (hp : f.locals.get? "_packed" = some (wordBytes32Value packed)) :
    ExecFuncBody config f evm slot0GetLPFeeFunction.body
      (.returned f evm (some [.int (Int.ofNat (slot0FeeField packed 208).toNat)])) :=
  .execBlockRet (ABlock.start.returns (slot0FeeField_eval 208 (by decide) (evalLocalValue hp)))

theorem slot0GetProtocolCall {f : Frame} {evm : State} {e : Expr} {packed : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (wordBytes32Value packed)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_protocolFee" [e] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (slot0FeeField packed 184).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed])
    (value := some [.int (Int.ofNat (slot0FeeField packed 184).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact slot0GetProtocol_lookup) rfl
  exact slot0GetProtocolBody (store_get_self _ _ _)

theorem slot0GetLPFeeCall {f : Frame} {evm : State} {e : Expr} {packed : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (wordBytes32Value packed)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Slot0Library_lpFee" [e] ret)
      (.ok (valueLocal f ret (.int (Int.ofNat (slot0FeeField packed 208).toNat))) evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value packed])
    (value := some [.int (Int.ofNat (slot0FeeField packed 208).toNat)]) (evalExprs?_singleton he)
    (by rw [hf]; exact slot0GetLPFee_lookup) rfl
  exact slot0GetLPFeeBody (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
