import Benchmarks.EAS.EAS.TimeArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

/-- Unpack a unit-returning callee and advance the shared array loop counter. -/
theorem timeArrayFinish {evm evm' : EVM.State} {locals imms : Store} {stmt : Stmt}
    {words : List UInt256} {time : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length) (hlen : words.length < UInt256.size)
    (hcall : ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm stmt
      (.ok {contract := contract, locals := locals.insert "__c1$allocation" (.tuple [.tuple [], .int (Int.ofNat heap)]), immutables := imms} evm')) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm
      [stmt, .letDecl "__c1" none (.tupleGet (.var "__c1$allocation") 0),
        .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c1$allocation") 1),
        .assign .localVar {base := "i"} (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))]
      (.ok {contract := contract, locals := timeArrayNext locals heap i, immutables := imms} evm') := by
  apply ExecBlock.consNormal hcall
  have hunpack := unpackHeapResult (fork := fork) (cfg := config) (evm := evm')
    (frame := {
      contract := contract
      locals := locals.insert "__c1$allocation" (.tuple [.tuple [], .int (Int.ofNat heap)])
      immutables := imms}) (result := "__c1") (cursor := "$EAS.freeMemory") (old := .int (Int.ofNat heap))
    (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("__c1$allocation" == "$EAS.freeMemory") = false)] using h.heap)
    (by decide) (by decide)
  apply execBlock_append hunpack
  let unpacked := unpackHeapLocals (locals.insert "__c1$allocation" (.tuple [.tuple [], .int (Int.ofNat heap)]))
    "__c1" "$EAS.freeMemory" (.tuple []) heap
  have hiRead : unpacked.get? "i" = some (.int (Int.ofNat i)) := by
    simpa only [unpacked, unpackHeapLocals,
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "i") = false),
      store_get_ne _ _ (by decide : ("__c1" == "i") = false),
      store_get_ne _ _ (by decide : ("__c1$allocation" == "i") = false)] using h.index
  have he := evalCastUint256Add (cfg := config) (evm := evm')
    (frame := {
      contract := contract
      locals := unpacked
      immutables := imms}) (x := i) (y := 1) (a := .var "i") (b := .intLit 1)
    (by simp only [evalExpr?, hiRead, EvalResult.ofOption]) (by simp only [evalExpr?]; rfl)
  rw [Nat.mod_eq_of_lt (by omega : i + 1 < UInt256.size)] at he
  exact ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalBase_ok hiRead)) ExecBlock.nil

end Benchmarks.EAS.EAS
