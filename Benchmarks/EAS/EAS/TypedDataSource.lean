import Benchmarks.EAS.EAS.TryRecoverExpr
import Benchmarks.EAS.EAS.AllocateBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def typedDataPayload (domain structHash : UInt256) : ByteArray :=
  ⟨((([25,1] : List UInt8) ++ EVM.Word.toBytesBE domain) ++ EVM.Word.toBytesBE structHash).toArray⟩
def typedDataWord (domain structHash : UInt256) : UInt256 := uInt256OfByteArray (KEC (typedDataPayload domain structHash))
def typedDataPackedArgs : List (ABIType × Expr) := [
  (.elem (.bytes 1),.fixedBytesLit 1 [25,1]),(abiBytes32,.var "domainSeparator"),(abiBytes32,.var "structHash")]
def typedDataExpr : Expr := .keccak256 (.abiEncodePacked typedDataPackedArgs)

theorem typedDataExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {domain structHash : UInt256}
    (hd : frame.locals.get? "domainSeparator" = some (wordBytes32Value domain))
    (hs : frame.locals.get? "structHash" = some (wordBytes32Value structHash)) :
    evalExpr? cfg frame evm typedDataExpr = .ok (wordBytes32Value (typedDataWord domain structHash)) := by
  have hp : evalPackedArgs? cfg frame evm typedDataPackedArgs = .ok (typedDataPayload domain structHash).toList := by
    simp only [typedDataPayload,byteArray_toList_eq,List.toList_toArray,List.append_assoc]
    apply evalPackedArgs_cons (v := .fixedBytes 1 [25,1]) (by simp only [evalExpr?,pure]) (by rfl)
    apply evalPackedArgs_cons (by simp only [evalExpr?,hd,EvalResult.ofOption]) (encodePacked_bytes32 _)
    exact evalPackedArgs_single (by simp only [evalExpr?,hs,EvalResult.ofOption]) (encodePacked_bytes32 _)
  simp only [typedDataExpr,evalExpr?,hp,EvalResult.bind,bind,pure]
  simp only [wordBytes32Value,typedDataWord,toBytesBE_keccak_uInt256OfByteArray,byteArray_toList_eq,Array.toArray_toList]
  rfl

abbrev typedDataFunction : FunctionDecl := contract.functions[31]!
theorem typedData_body : typedDataFunction.body = allocateBlock (.intLit 128) ++
    [.return [typedDataExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]] := by native_decide

theorem typedDataSource {L imms : Store} {evm : EVM.State} {domain structHash : UInt256} {heap : Nat}
    (hd : L.get? "domainSeparator" = some (wordBytes32Value domain))
    (hs : L.get? "structHash" = some (wordBytes32Value structHash))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if allocateNext heap 128 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 128 then
      ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm typedDataFunction.body
        (.returned {contract := contract,locals := allocateBlockLocals L (allocateNext heap 128),immutables := imms} evm
          (some [wordBytes32Value (typedDataWord domain structHash),.int (Int.ofNat (allocateNext heap 128))]))
    else ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm typedDataFunction.body .reverted := by
  rw [typedData_body]
  split_ifs with hg
  · apply ExecFuncBody.execBlockRet
    apply execBlock_append (allocateBlock_ok (by simp only [evalExpr?,pure]; rfl) hh hg)
    apply ExecBlock.consReturn
    apply ExecStmt.return
    have hd' : (allocateBlockLocals L (allocateNext heap 128)).get? "domainSeparator" = some (wordBytes32Value domain) := by
      rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
      exact hd
    have hs' : (allocateBlockLocals L (allocateNext heap 128)).get? "structHash" = some (wordBytes32Value structHash) := by
      rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
      exact hs
    have he := typedDataExpr_eval (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := allocateBlockLocals L (allocateNext heap 128),immutables := imms}) hd' hs'
    simp only [allocateBlockLocals,unpackHeapLocals] at he
    simp only [evalExprs?,he,evalExpr?,allocateBlockLocals,unpackHeapLocals,store_get_self,EvalResult.ofOption,
      EvalResult.bind,bind,pure]
  · exact ExecFuncBody.execBlockRevert (execBlock_append_term
      (allocateBlock_revert (by simp only [evalExpr?,pure]; rfl) hh hg) (by intros; exact nofun))

def typedDataArgs (domain structHash : UInt256) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "structHash" (wordBytes32Value structHash)
    |>.insert "domainSeparator" (wordBytes32Value domain)
theorem typedData_lookup : lookupCallable? contract "ECDSA_toTypedDataHash" = some typedDataFunction.toCallable := rfl
theorem typedData_bind (domain structHash : UInt256) (heap : Nat) :
    bindParams? typedDataFunction.params [wordBytes32Value domain,wordBytes32Value structHash,.int (Int.ofNat heap)] =
      some (typedDataArgs domain structHash heap) := rfl

end Benchmarks.EAS.EAS
