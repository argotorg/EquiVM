import Benchmarks.EAS.EAS.RefundEVM
import Benchmarks.EAS.EAS.TimestampSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem refundSource_static {cfg : Config} {locals imms : Store} {evm : EVM.State} {value : UInt256}
    (hv : locals.get? "remainingValue" = some (.int (Int.ofNat value.toNat))) (hn : value ≠ ⟨0⟩)
    (hb : value.toNat ≤ (refundBalance evm).toNat) (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork cfg {contract := contract,locals := locals,immutables := imms} evm refundFunction.body .staticViolation := by
  rw [refund_body]
  apply ExecFuncBody.execBlockStatic
  apply ExecBlock.consStatic (ExecStmt.iteTrue ?_ ?_)
  · simpa only [decide_eq_true hn] using refundNonzero_eval (cfg := cfg)
      (frame := {contract := contract,locals := locals,immutables := imms}) (evm := evm) hv
  · apply ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [decide_eq_true hb] using refundBalance_eval (cfg := cfg)
        (frame := {contract := contract,locals := locals,immutables := imms}) (evm := evm) hv))
    apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes ByteArray.empty) (by simp only [evalExpr?,pure]; rfl))
    exact ExecBlock.consStatic (ExecStmt.lowLevelCallStatic
      (by simp only [evalExpr?,envValue,pure]; rfl)
      (by simp only [evalExpr?,store_get_ne _ _ (by decide : ("empty" == "remainingValue") = false),hv,EvalResult.ofOption]; rfl)
      (by simp only [evalExpr?,store_get_self,EvalResult.ofOption]; rfl)
      (by rw [wordOfInt_ofNat_toNat]; exact hn) hp)

theorem refundCall_static {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {value : UInt256} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract,locals := locals,immutables := imms} evm args =
      .ok [.int (Int.ofNat value.toNat),.int (Int.ofNat heap)])
    (hn : value ≠ ⟨0⟩) (hb : value.toNat ≤ (refundBalance evm).toNat) (hp : evm.executionEnv.perm = false) :
    ExecStmt fork cfg {contract := contract,locals := locals,immutables := imms} evm (.internalCall "_refund" args retVar) .staticViolation :=
  internalCallFunctionStatic he refund_lookup (refund_bind value heap)
    (refundSource_static (store_get_self _ _ _) hn hb hp)

theorem refundEVM_static {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hperm : ee.perm = false) (hs : SourceState s0 ee σ evm)
    (hn : value ≠ ⟨0⟩) (hb : value.toNat ≤ (refundBalance evm).toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  obtain ⟨gasArg,a3,k3,C3,r3⟩ := refundCallEntry v hstack hs hn hb rd
  exact RD.callValueStatic r3 hperm hn
    (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16366⟩ : UInt256), UInt8.ofNat 241,
      .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
    (by simp only [List.length_cons]; omega)

end Benchmarks.EAS.EAS
