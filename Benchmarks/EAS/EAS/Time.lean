import Benchmarks.EAS.EAS.Allocate
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: narrowing a natural-valued word to an unsigned ABI width.
theorem evalWordAsUint {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256} (width : ABI.BitWidth)
    (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint width)))) =
      .ok (.int (Int.ofNat (UInt256.land w (UInt256.ofNat (2^width.val-1))).toNat)) := by
  have hbound : 2^width.val - 1 < UInt256.size := by
    have hpow : (2 : Nat)^width.val ≤ 2^256 := Nat.pow_le_pow_right (by decide) width.property.2.1
    have hp : 0 < (2 : Nat)^width.val := by positivity
    change 2^width.val - 1 < 2^256
    omega
  rw [uland_toNat, ulit_toNat' _ hbound]
  change evalExpr? cfg frame evm _ = .ok (.int (Int.ofNat (Nat.land w.toNat (2^width.val-1))))
  rw [nat_land_mask_eq_mod]
  simp only [evalExpr?, he, EvalResult.bind, bind, castValue?, normalizeInt, EvalResult.ofOption,
    Int.ofNat_eq_natCast, Int.natCast_mod, Int.natCast_pow, EVM.twoPow]

def easTimeWord (ee : ExecutionEnv) : UInt256 := UInt256.land (UInt256.ofNat ee.header.timestamp) easUint64Mask

abbrev timeFunction : FunctionDecl := contract.functions[19]!

theorem time_body : timeFunction.body = [
    .return [.cast (.env .timestamp) (.elem (.int (.uint ⟨64, by decide⟩))), .var "$EAS.freeMemory"],
    .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

theorem timeSource {cfg : Config} {frame : Frame} {evm : EVM.State} {heap : Nat}
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg frame evm timeFunction.body
      (.returned frame evm (some [.int (Int.ofNat (easTimeWord evm.executionEnv).toNat), .int (Int.ofNat heap)])) := by
  rw [time_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he := evalWordAsUint (cfg := cfg) (frame := frame) (evm := evm) ⟨64, by decide⟩
    (show evalExpr? cfg frame evm (.env .timestamp) =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) by simp only [evalExpr?, envValue, pure])
  change evalExpr? cfg frame evm (.cast (.env .timestamp) (.elem (.int (.uint ⟨64, by decide⟩)))) =
    .ok (.int (Int.ofNat (easTimeWord evm.executionEnv).toNat)) at he
  simp only [evalExprs?, he, evalExpr?, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem time_lookup : lookupCallable? contract "_time" = some timeFunction.toCallable := by rfl

def timeArgs (heap : Nat) : Store := (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap))

theorem time_bind (heap : Nat) : bindParams? timeFunction.params [.int (Int.ofNat heap)] = some (timeArgs heap) := by rfl

theorem timeCall {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {heapExpr : Expr} {heap : Nat} {retVar : Ident}
    (he : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm heapExpr =
      .ok (.int (Int.ofNat heap))) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_time" [heapExpr] retVar)
      (.ok {
        contract := contract
        locals := locals.insert retVar (.tuple [.int (Int.ofNat (easTimeWord evm.executionEnv).toNat), .int (Int.ofNat heap)])
        immutables := imms} evm) := by
  exact internalCallFunctionReturn (cfg := cfg) (evm := evm)
    (caller := {contract := contract, locals := locals, immutables := imms})
    (args := [heapExpr]) (argVals := [.int (Int.ofNat heap)])
    (by simp only [evalExprs?, he, EvalResult.bind, bind, pure]) time_lookup (time_bind heap)
    (timeSource (store_get_self _ _ _))


end Benchmarks.EAS.EAS
