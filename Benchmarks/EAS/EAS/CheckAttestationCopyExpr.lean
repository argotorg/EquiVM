import Benchmarks.EAS.EAS.CheckAttestationCopySyntax
import Benchmarks.EAS.EAS.CalldataWordSource
import Benchmarks.EAS.EAS.NaturalWordExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem checkAttestationCopySlot_eval {L imms : Store} {evm : EVM.State} {base index : Ident} {ptr : UInt256} {i : Nat}
    (hb : L.get? base=some (.int (Int.ofNat ptr.toNat))) (hi : L.get? index=some (.int (Int.ofNat i))) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm (checkAttestationCopySlot base index)=
      .ok (.int (Int.ofNat (UInt256.ofNat (ptr.toNat+32*i)).toNat)) := by
  have he := evalCastUint256Nat (naturalAddSource
    (evalLocalValue (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hb)
    (naturalMulSource (evalLocalValue hi) (show evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.intLit 32)=.ok (.int (Int.ofNat 32)) from by simp only [evalExpr?,pure];rfl)))
  simpa only [Nat.mul_comm] using he

theorem checkAttestationCopyWordSource {L imms : Store} {evm : EVM.State} {e : Expr} {ptr : UInt256} {heap : Nat}
    (name : Ident) (htc : ((name++"$allocation")=="$EAS.freeMemory")=false)
    (htr : (name==(name++"$allocation"))=false) (hrc : (name=="$EAS.freeMemory")=false)
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm e=.ok (.int (Int.ofNat ptr.toNat)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (checkAttestationCopyWord e name)
      (.ok {contract := contract,locals := (heapResultLocals L (name++"$allocation") name "$EAS.freeMemory"
        (.int (Int.ofNat (calldataWord evm.executionEnv.calldata ptr.toNat).toNat)) heap),immutables := imms} evm) := by
  have hargs : evalExprs? config {contract := contract,locals := L,immutables := imms} evm [e,.var "$EAS.freeMemory"]=
      .ok [.int (Int.ofNat ptr.toNat),.int (Int.ofNat heap)] := by
    simp only [evalExprs?,he,evalExpr?,hh,EvalResult.ofOption,bind,EvalResult.bind,pure]
  exact heapResultBlock_ok (result := name) (cursor := "$EAS.freeMemory")
    (calldataWordCall (retVar := name++"$allocation") hargs) hh htc htr hrc

end Benchmarks.EAS.EAS
