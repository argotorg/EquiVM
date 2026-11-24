import Benchmarks.EAS.EAS.CheckAttestationCopyPrefix
import Benchmarks.EAS.EAS.CheckAttestationCopyLoop

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def checkAttestationCopyValid (cd : ByteArray) (index len : Nat) : Prop :=
  (UInt256.ofNat ((checkAttestationCopyData cd index).toNat+32*len)).toNat≤(UInt256.ofNat cd.size).toNat ∧
    checkAttestationCopyOffsetsValid cd (checkAttestationCopyData cd index) len
instance (cd : ByteArray) (index len : Nat) : Decidable (checkAttestationCopyValid cd index len) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem checkAttestationCopySource {L imms : Store} {evm : EVM.State} {index len heap : Nat}
    (hi : L.get? "index"=some (.int (Int.ofNat index))) (hl : L.get? "length"=some (.int (Int.ofNat len)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) (hbound : len<UInt256.size) :
    (checkAttestationCopyValid evm.executionEnv.calldata index len →
      ∃ L', ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyFunction.body
        (.returned {contract := contract,locals := L',immutables := imms} evm (some [.tuple [],.int (Int.ofNat heap)]))) ∧
    (¬checkAttestationCopyValid evm.executionEnv.calldata index len →
      ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyFunction.body .reverted) := by
  obtain ⟨L1,hprefix,hd1,hi1,hl1,hh1⟩ := checkAttestationCopyPrefixSource (imms := imms) (evm := evm) hi hl hh
  let data := checkAttestationCopyData evm.executionEnv.calldata index
  have hsize : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm
      (.arrayLength .localVar {base := "input"})=.ok (.int (Int.ofNat evm.executionEnv.calldata.size)) := by
    simp only [evalExpr?,hi1,readLocalPath?,bind,EvalResult.bind,pure]
  have hguard := naturalLeSource (checkAttestationCopySlot_eval (imms := imms) (evm := evm) hd1 hl1) (evalCastUint256Nat hsize)
  by_cases hext : (UInt256.ofNat ((checkAttestationCopyData evm.executionEnv.calldata index).toNat+32*len)).toNat≤(UInt256.ofNat evm.executionEnv.calldata.size).toNat
  · have hg : ExecStmt fork config {contract := contract,locals := L1,immutables := imms} evm checkAttestationCopyExtent
        (.ok {contract := contract,locals := L1,immutables := imms} evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hext] using hguard)
    let L2 := L1.insert "i" (.int 0)
    have hinit : ExecStmt fork config {contract := contract,locals := L1,immutables := imms} evm
        (.letDecl "i" (some abiUInt256) (.intLit 0)) (.ok {contract := contract,locals := L2,immutables := imms} evm) :=
      ExecStmt.letDecl (by simp only [evalExpr?,pure])
    have hf2 : CheckAttestationCopyLocals L2 data len heap 0 := by
      constructor
      · exact (store_get_ne _ _ (by decide)).trans hd1
      · exact (store_get_ne _ _ (by decide)).trans hl1
      · exact (store_get_ne _ _ (by decide)).trans hh1
      · exact store_get_self _ _ _
    rcases checkAttestationCopyLoopSource (imms := imms) (evm := evm) hbound len (by omega) hf2 with ⟨hgood,L3,hloop,hf3⟩ | ⟨hbad,hloop⟩
    · have hv : checkAttestationCopyValid evm.executionEnv.calldata index len :=
        ⟨hext,fun t ht => hgood t (Nat.zero_le _) ht⟩
      refine ⟨fun _ => ⟨L3,?_⟩,fun hn => (hn hv).elim⟩
      rw [checkAttestationCopy_body,List.append_assoc]
      apply ExecFuncBody.execBlockRet
      apply execBlock_append hprefix
      apply ExecBlock.consNormal hg
      apply ExecBlock.consNormal hinit
      apply ExecBlock.consNormal hloop
      apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?,evalExpr?,evalExprList?,hf3.heap,EvalResult.ofOption,bind,EvalResult.bind,pure]
    · have hv : ¬checkAttestationCopyValid evm.executionEnv.calldata index len := fun h => hbad (fun t _ ht => h.2 t ht)
      refine ⟨fun h => (hv h).elim,fun _ => ?_⟩
      rw [checkAttestationCopy_body,List.append_assoc]
      apply ExecFuncBody.execBlockRevert
      apply execBlock_append hprefix
      exact ExecBlock.consNormal hg (ExecBlock.consNormal hinit (ExecBlock.consRevert hloop))
  · have hv : ¬checkAttestationCopyValid evm.executionEnv.calldata index len := fun h => hext h.1
    refine ⟨fun h => (hv h).elim,fun _ => ?_⟩
    rw [checkAttestationCopy_body,List.append_assoc]
    apply ExecFuncBody.execBlockRevert
    apply execBlock_append hprefix
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hext] using hguard))

def checkAttestationCopyArgs (index len heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "length" (.int (Int.ofNat len)) |>.insert "index" (.int (Int.ofNat index))
theorem checkAttestationCopy_lookup : lookupCallable? contract "_checkAttestationArrayCopy"=some checkAttestationCopyFunction.toCallable := rfl
theorem checkAttestationCopy_bind (index len heap : Nat) :
    bindParams? checkAttestationCopyFunction.params [.int (Int.ofNat index),.int (Int.ofNat len),.int (Int.ofNat heap)]=some (checkAttestationCopyArgs index len heap) := rfl

theorem checkAttestationCopyCall {L imms : Store} {evm : EVM.State} {index len heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args=
      .ok [.int (Int.ofNat index),.int (Int.ofNat len),.int (Int.ofNat heap)]) (hbound : len<UInt256.size) :
    (checkAttestationCopyValid evm.executionEnv.calldata index len →
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (.internalCall "_checkAttestationArrayCopy" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} retVar
          (some [.tuple [],.int (Int.ofNat heap)])) evm)) ∧
    (¬checkAttestationCopyValid evm.executionEnv.calldata index len →
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (.internalCall "_checkAttestationArrayCopy" args retVar) .reverted) := by
  have hs := checkAttestationCopySource (fork := fork) (L := checkAttestationCopyArgs index len heap) (imms := imms) (evm := evm)
    (index := index) (len := len) (heap := heap) (store_get_self _ _ _)
    (by simp (disch := decide) only [checkAttestationCopyArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [checkAttestationCopyArgs,store_get_ne,store_get_self]) hbound
  constructor
  · intro hv
    obtain ⟨L',hb⟩ := hs.1 hv
    exact internalCallFunctionReturn he checkAttestationCopy_lookup (checkAttestationCopy_bind index len heap) hb
  · intro hv
    exact internalCallFunctionRevert he checkAttestationCopy_lookup (checkAttestationCopy_bind index len heap) (hs.2 hv)

end Benchmarks.EAS.EAS
