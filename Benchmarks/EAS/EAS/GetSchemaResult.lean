import Benchmarks.EAS.EAS.GetSchemaTail

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getSchemaResultSource {locals imms : Store} {evm : EVM.State}
    {heap : Nat} {success : Bool} {out : ByteArray}
    (hok : locals.get? "ok" = some (.bool success))
    (hor : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (hout : out.size < 2^255) :
    if schemaCallValid heap success out then
      ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm getSchemaSuffix
        (.returned {contract := contract, locals := getSchemaFinalLocals locals heap out, immutables := imms}
          evm (some [(decodedSchemaRecord out (schemaReturnOffset out)).value,.int (Int.ofNat (schemaFinalHeap heap out))]))
    else ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm getSchemaSuffix .reverted := by
  have hcheck : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "ok") =
      .ok (.bool success) := by simp only [evalExpr?, hok, EvalResult.ofOption]
  have he1 : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.arrayLength .localVar {base := "result"}) = .ok (.int (Int.ofNat out.size)) := by
    simp only [evalExpr?, readLocalPath?, hor, EvalResult.bind, bind, pure]
  cases success with
  | false =>
    rw [if_neg (by intro h; cases h.1)]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse hcheck))
  | true =>
    by_cases hg1 : schemaCopyHeap heap out ≤ 2^64-1 ∧ heap ≤ schemaCopyHeap heap out
    · have hp1 := allocateBlock_ok (fork := fork) (imms := imms) he1 hh hg1
      have hor1 : (allocateBlockLocals locals (schemaCopyHeap heap out)).get? "result" = some (.bytes out) := by
        rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
        exact hor
      have hh1 : (allocateBlockLocals locals (schemaCopyHeap heap out)).get? "$EAS.freeMemory" =
          some (.int (Int.ofNat (schemaCopyHeap heap out))) := store_get_self _ _ _
      have he2 : evalExpr? config {contract := contract, locals := allocateBlockLocals locals (schemaCopyHeap heap out), immutables := imms}
          evm (.intLit 128) = .ok (.int (Int.ofNat (128 : Nat))) := by simp only [evalExpr?, pure]; rfl
      by_cases hg2 : schemaDecodeHeap heap out ≤ 2^64-1 ∧ schemaCopyHeap heap out ≤ schemaDecodeHeap heap out
      · have hp2 := allocateBlock_ok (fork := fork) he2 hh1 hg2
        have hor2 : (getSchemaAllocatedLocals locals heap out).get? "result" = some (.bytes out) := by
          rw [getSchemaAllocatedLocals, allocateBlockLocals_get (by decide) (by decide) (by decide)]
          exact hor1
        have hh2 : (getSchemaAllocatedLocals locals heap out).get? "$EAS.freeMemory" =
            some (.int (Int.ofNat (schemaDecodeHeap heap out))) := store_get_self _ _ _
        have hp := execBlock_append hp1 hp2
        by_cases hd : schemaReturnValid out
        · have hlength := decodedSchemaRecord_length hd.2.2
          have hlcap : (decodedSchemaRecord out (schemaReturnOffset out)).schema.size ≤ 2^64-1 := by
            rw [hlength]
            exact hd.2.2.2.2.2.2.2.1
          have hp3 := getSchemaDecodeSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hor2
            (by rw [decodeSchemaReturn hout, if_pos hd]) hlcap
          have hh3 : (getSchemaDecodeLocals (getSchemaAllocatedLocals locals heap out)
              (decodedSchemaRecord out (schemaReturnOffset out))).get? "$EAS.freeMemory" =
              some (.int (Int.ofNat (schemaDecodeHeap heap out))) := by
            simpa only [getSchemaDecodeLocals,
              store_get_ne _ _ (by decide : ("text" == "$EAS.freeMemory") = false),
              store_get_ne _ _ (by decide : ("record" == "$EAS.freeMemory") = false)] using hh2
          have he3 : evalExpr? config {contract := contract, locals := getSchemaDecodeLocals (getSchemaAllocatedLocals locals heap out) (decodedSchemaRecord out (schemaReturnOffset out)), immutables := imms} evm (bytesAllocationExpr (.arrayLength .localVar {base := "text"})) =
              .ok (.int (Int.ofNat (bytesAllocation (schemaTextLength out (schemaReturnOffset out))))) := by
            apply bytesAllocationExpr_eval
            simp only [evalExpr?, getSchemaDecodeLocals, readLocalPath?, store_get_self,
              EvalResult.bind, bind, pure, hlength]
          by_cases hg3 : schemaFinalHeap heap out ≤ 2^64-1 ∧ schemaDecodeHeap heap out ≤ schemaFinalHeap heap out
          · rw [if_pos ⟨rfl,hg1,hg2,hd,hg3⟩]
            apply ExecFuncBody.execBlockRet
            apply ExecBlock.consNormal (ExecStmt.requireTrue hcheck)
            apply execBlock_append hp1
            apply execBlock_append hp2
            apply execBlock_append hp3
            apply execBlock_append (allocateBlock_ok he3 hh3 hg3)
            apply getSchemaReturnSource
            · rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
              simp only [getSchemaDecodeLocals, store_get_ne _ _ (by decide : ("text" == "record") = false), store_get_self]
            · exact store_get_self _ _ _
          · rw [if_neg (by intro h; exact hg3 h.2.2.2.2)]
            apply ExecFuncBody.execBlockRevert
            apply ExecBlock.consNormal (ExecStmt.requireTrue hcheck)
            apply execBlock_append hp1
            apply execBlock_append hp2
            apply execBlock_append hp3
            exact execBlock_append_term (allocateBlock_revert he3 hh3 hg3) (by intros; exact nofun)
        · rw [if_neg (by intro h; exact hd h.2.2.2.1)]
          apply ExecFuncBody.execBlockRevert
          apply ExecBlock.consNormal (ExecStmt.requireTrue hcheck)
          apply execBlock_append hp1
          apply execBlock_append hp2
          exact execBlock_append_term (getSchemaDecodeRevert hor2 (by rw [decodeSchemaReturn hout, if_neg hd]))
            (by intros; exact nofun)
      · rw [if_neg (by intro h; exact hg2 h.2.2.1)]
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consNormal (ExecStmt.requireTrue hcheck)
        apply execBlock_append hp1
        exact execBlock_append_term (allocateBlock_revert he2 hh1 hg2) (by intros; exact nofun)
    · rw [if_neg (by intro h; exact hg1 h.2.1)]
      apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consNormal (ExecStmt.requireTrue hcheck)
      change ExecBlock fork config _ evm
        (allocateBlock (.arrayLength .localVar {base := "result"}) ++ allocateBlock (.intLit 128) ++
          getSchemaDecode ++ allocateBlock (bytesAllocationExpr (.arrayLength .localVar {base := "text"})) ++ getSchemaReturn) .reverted
      simp only [List.append_assoc]
      exact execBlock_append_term (allocateBlock_revert he1 hh hg1) (by intros; exact nofun)

end Benchmarks.EAS.EAS
