import Benchmarks.EAS.EAS.CalldataWordBytes
import Benchmarks.EAS.EAS.CopyRequestSource
import Benchmarks.EAS.EAS.CalldataPayload

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev calldataWordFunction : FunctionDecl := contract.functions[7]!
def calldataWordInput : Stmt := .letDecl "input" (some .bytes) (.env .msgData)
def calldataWordGuard : Expr := .binary .ge (.var "offset") (.arrayLength .localVar {base := "input"})
def calldataWordEmpty : Body := [.return [.intLit 0,.var "$EAS.freeMemory"]]
def calldataWordCount : Stmt := .letDecl "count" (some abiUInt256)
  (.binary .sub (.arrayLength .localVar {base := "input"}) (.var "offset"))
def calldataWordLimit : Stmt := .ite (.binary .gt (.var "count") (.intLit 32))
  [.assign .localVar {base := "count"} (.intLit 32)] []
def calldataWordTail : Body := [
  .letDecl "part" (some .bytes) (.bytesSlice (.var "input") (.var "offset") (.binary .add (.var "offset") (.var "count"))),
  .letDecl "padding" (some .bytes) (.newBytes (.binary .sub (.intLit 32) (.var "count"))),
  .letDecl "word" (some .bytes) (.abiEncodePacked [(.bytes,.var "part"),(.bytes,.var "padding")]),
  .return [.abiDecode abiUInt256 (.var "word"),.var "$EAS.freeMemory"],
  .return [.tupleLit [],.var "$EAS.freeMemory"]]

theorem calldataWord_body : calldataWordFunction.body =
    [calldataWordInput,.ite calldataWordGuard calldataWordEmpty [],calldataWordCount,calldataWordLimit]++calldataWordTail := by native_decide

theorem calldataWordTailSource {L imms : Store} {evm : EVM.State} {offset : UInt256} {heap : Nat}
    (ho : L.get? "offset"=some (.int (Int.ofNat offset.toNat)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)))
    (hi : L.get? "input"=some (.bytes evm.executionEnv.calldata))
    (hc : L.get? "count"=some (.int (Int.ofNat (min (evm.executionEnv.calldata.size-offset.toNat) 32))))
    (hb : offset.toNat<evm.executionEnv.calldata.size) :
    ∃ L', ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm calldataWordTail
      (.returned {contract := contract,locals := L',immutables := imms} evm
        (some [.int (Int.ofNat (calldataWord evm.executionEnv.calldata offset.toNat).toNat),.int (Int.ofNat heap)])) := by
  let count := min (evm.executionEnv.calldata.size-offset.toNat) 32
  let part := evm.executionEnv.calldata.extract offset.toNat (offset.toNat+count)
  let padding := ByteArray.mk (Array.replicate (32-count) (0 : UInt8))
  let word := ByteArray.mk ((part.toList++padding.toList).toArray)
  let L1 := L.insert "part" (.bytes part)
  let L2 := L1.insert "padding" (.bytes padding)
  let L3 := L2.insert "word" (.bytes word)
  have hcount : count≤32 := Nat.min_le_right _ _
  have hext : offset.toNat+count≤evm.executionEnv.calldata.size := by have := Nat.min_le_left (evm.executionEnv.calldata.size-offset.toNat) 32;omega
  have hp : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.bytesSlice (.var "input") (.var "offset") (.binary .add (.var "offset") (.var "count")))=.ok (.bytes part) := by
    simp only [evalExpr?,hi,ho,hc,EvalResult.ofOption,bind,EvalResult.bind,evalBinaryOp?]
    exact sliceBytes_nat (by omega) hext
  have hc1 : L1.get? "count"=some (.int (Int.ofNat count)) := (store_get_ne _ _ (by decide)).trans hc
  have hz : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm
      (.newBytes (.binary .sub (.intLit 32) (.var "count")))=.ok (.bytes padding) := by
    simp only [evalExpr?,hc1,EvalResult.ofOption,bind,EvalResult.bind,pure,evalBinaryOp?]
    have he : (32:Int)-Int.ofNat count=Int.ofNat (32-count) := by simp only [Int.ofNat_eq_natCast];omega
    rw [he,if_neg (by simp only [Int.ofNat_eq_natCast];omega)]
    rfl
  have hp2 : L2.get? "part"=some (.bytes part) := (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  have hz2 : L2.get? "padding"=some (.bytes padding) := store_get_self _ _ _
  have hw : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
      (.abiEncodePacked [(.bytes,.var "part"),(.bytes,.var "padding")])=.ok (.bytes word) := by
    simp only [evalExpr?,evalPackedArgs?,hp2,hz2,EvalResult.ofOption,bind,EvalResult.bind,pure,encodePacked_dynamic_bytes,List.append_nil]
    rfl
  have hd : config.externalABI.decodeValue? abiUInt256 word=
      some (.int (Int.ofNat (calldataWord evm.executionEnv.calldata offset.toNat).toNat)) :=
    decodeReturnUint_wordBytes _ (by simpa only [word,byteArray_toList_eq,List.toList_toArray] using calldataWord_paddedSlice evm.executionEnv.calldata offset)
  have hh3 : L3.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by
    simpa (disch := decide) only [L3,L2,L1,store_get_ne] using hh
  refine ⟨L3,ExecBlock.consNormal (ExecStmt.letDecl hp) (ExecBlock.consNormal (ExecStmt.letDecl hz)
    (ExecBlock.consNormal (ExecStmt.letDecl hw) (ExecBlock.consReturn (ExecStmt.return ?_))))⟩
  change evalExprs? config {contract := contract,locals := L3,immutables := imms} evm [.abiDecode abiUInt256 (.var "word"),.var "$EAS.freeMemory"]=_
  have hw3 : L3.get? "word"=some (.bytes word) := store_get_self _ _ _
  simp only [evalExprs?,evalExpr?,hw3,hh3,hd,EvalResult.ofOption,bind,EvalResult.bind,pure]

theorem calldataWordSource {L imms : Store} {evm : EVM.State} {offset : UInt256} {heap : Nat}
    (ho : L.get? "offset"=some (.int (Int.ofNat offset.toNat)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) :
    ∃ L', ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm calldataWordFunction.body
      (.returned {contract := contract,locals := L',immutables := imms} evm
        (some [.int (Int.ofNat (calldataWord evm.executionEnv.calldata offset.toNat).toNat),.int (Int.ofNat heap)])) := by
  let L1 := L.insert "input" (.bytes evm.executionEnv.calldata)
  have hi1 : L1.get? "input"=some (.bytes evm.executionEnv.calldata) := store_get_self _ _ _
  have ho1 : L1.get? "offset"=some (.int (Int.ofNat offset.toNat)) := (store_get_ne _ _ (by decide)).trans ho
  have hh1 : L1.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := (store_get_ne _ _ (by decide)).trans hh
  have hinput : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm calldataWordInput
      (.ok {contract := contract,locals := L1,immutables := imms} evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?,envValue,pure])
  have hguard : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm calldataWordGuard=
      .ok (.bool (decide (evm.executionEnv.calldata.size≤offset.toNat))) := by
    simp only [calldataWordGuard,evalExpr?,ho1,hi1,readLocalPath?,EvalResult.ofOption,bind,EvalResult.bind,pure,evalBinaryOp?,Int.ofNat_eq_natCast,Nat.cast_le]
  by_cases hb : evm.executionEnv.calldata.size≤offset.toNat
  · refine ⟨L1,?_⟩
    rw [calldataWord_body,calldataWord_zero_of_ge _ _ hb]
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal hinput
    apply ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [decide_eq_true hb] using hguard) ?_)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?,evalExpr?,hh1,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  · let n := evm.executionEnv.calldata.size-offset.toNat
    let L2 := L1.insert "count" (.int (Int.ofNat n))
    have hc2 : L2.get? "count"=some (.int (Int.ofNat n)) := store_get_self _ _ _
    have hcount : ExecStmt fork config {contract := contract,locals := L1,immutables := imms} evm calldataWordCount
        (.ok {contract := contract,locals := L2,immutables := imms} evm) := by
      apply ExecStmt.letDecl
      simp only [evalExpr?,hi1,ho1,readLocalPath?,EvalResult.ofOption,bind,EvalResult.bind,pure,evalBinaryOp?]
      congr 2
      change (evm.executionEnv.calldata.size:Int)-offset.toNat=Int.ofNat n
      simp only [n,Int.ofNat_eq_natCast];omega
    have hlimit : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
        (.binary .gt (.var "count") (.intLit 32))=.ok (.bool (decide (32<n))) := by
      simp only [evalExpr?,hc2,EvalResult.ofOption,bind,EvalResult.bind,pure,evalBinaryOp?,Int.ofNat_eq_natCast]
      change EvalResult.ok (Value.bool (decide ((32:Int)<(n:Int))))=EvalResult.ok (Value.bool (decide (32<n)))
      simp only [show ((32:Int)<(n:Int)) ↔ 32<n by omega]
    have hprefix : ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm
        [calldataWordInput,.ite calldataWordGuard calldataWordEmpty [],calldataWordCount]
        (.ok {contract := contract,locals := L2,immutables := imms} evm) :=
      ExecBlock.consNormal hinput (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [decide_eq_false hb] using hguard) ExecBlock.nil)
        (ExecBlock.consNormal hcount ExecBlock.nil))
    have hbounded : ∃ L3, ExecStmt fork config {contract := contract,locals := L2,immutables := imms} evm calldataWordLimit
          (.ok {contract := contract,locals := L3,immutables := imms} evm) ∧
        L3.get? "offset"=some (.int (Int.ofNat offset.toNat)) ∧
        L3.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) ∧
        L3.get? "input"=some (.bytes evm.executionEnv.calldata) ∧
        L3.get? "count"=some (.int (Int.ofNat (min n 32))) := by
      by_cases hn : 32<n
      · refine ⟨L2.insert "count" (.int 32),ExecStmt.iteTrue (by simpa only [decide_eq_true hn] using hlimit)
          (ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (by simp only [evalExpr?,pure]) (assignLocalValue hc2)) ExecBlock.nil),?_,?_,?_,?_⟩
        all_goals simp (disch := decide) only [L2,store_get_ne,store_get_self,Nat.min_eq_right (by omega : 32≤n)]
        all_goals first | exact ho1 | exact hh1 | exact hi1 | rfl
      · refine ⟨L2,ExecStmt.iteFalse (by simpa only [decide_eq_false hn] using hlimit) ExecBlock.nil,?_,?_,?_,?_⟩
        all_goals simp (disch := decide) only [L2,store_get_ne,store_get_self,Nat.min_eq_left (by omega : n≤32)]
        all_goals first | exact ho1 | exact hh1 | exact hi1 | rfl
    obtain ⟨L3,hs3,ho3,hh3,hi3,hc3⟩ := hbounded
    obtain ⟨L4,hs4⟩ := calldataWordTailSource (imms := imms) (evm := evm) ho3 hh3 hi3 hc3 (by omega)
    refine ⟨L4,?_⟩
    rw [calldataWord_body]
    apply ExecFuncBody.execBlockRet
    change ExecBlock fork config _ evm ([calldataWordInput,.ite calldataWordGuard calldataWordEmpty [],calldataWordCount]++(calldataWordLimit::calldataWordTail)) _
    exact execBlock_append hprefix (ExecBlock.consNormal hs3 hs4)

def calldataWordArgs (offset : UInt256) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "offset" (.int (Int.ofNat offset.toNat))
theorem calldataWord_lookup : lookupCallable? contract "_calldataWord"=some calldataWordFunction.toCallable := rfl
theorem calldataWord_bind (offset : UInt256) (heap : Nat) :
    bindParams? calldataWordFunction.params [.int (Int.ofNat offset.toNat),.int (Int.ofNat heap)]=some (calldataWordArgs offset heap) := rfl

theorem calldataWordCall {L imms : Store} {evm : EVM.State} {offset : UInt256} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args=
      .ok [.int (Int.ofNat offset.toNat),.int (Int.ofNat heap)]) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (.internalCall "_calldataWord" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} retVar
        (some [.int (Int.ofNat (calldataWord evm.executionEnv.calldata offset.toNat).toNat),.int (Int.ofNat heap)])) evm) := by
  obtain ⟨L',hs⟩ := calldataWordSource (offset := offset) (heap := heap) (L := calldataWordArgs offset heap) (imms := imms) (evm := evm)
    (store_get_self _ _ _) (by simp (disch := decide) only [calldataWordArgs,store_get_ne,store_get_self])
  exact internalCallFunctionReturn he calldataWord_lookup (calldataWord_bind offset heap) hs

end Benchmarks.EAS.EAS
