import Benchmarks.EAS.EAS.MultiDelegatedRevokeIteration

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeLoop : Stmt := .while (localArrayGuard "i" "multiDelegatedRequests") multiDelegatedRevokeIteration

theorem multiDelegatedRevokeLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n : Nat} {base tag : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+52 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size)
    (h : MultiDelegatedRevokeAt fork v ee g s0 n base tag R 0 L evm) :
    (∃ L' evm', ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeLoop
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedRevokeAt fork v ee g s0 n base tag R n L' evm') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeLoop .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeLoop .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  apply execWhile_invariant (MultiDelegatedRevokeAt fork v ee g s0 n base tag R)
    (MultiDelegatedRevokeAt fork v ee g s0 n base tag R n) (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    ?_ (fun _ _ h => h) ?_ n 0 L evm (by omega) h
  · rintro i L1 e1 _ ⟨σ,mem,out,aw,k,C,heap,available,_,_,_,hf,_,_,_,_⟩
    simpa only [delegatedBatchValues_length] using evalLocalArrayGuard
      (cfg := config) (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := e1) hf.index hf.requests
  · intro i L1 e1 hi h1
    exact multiDelegatedRevokeIterationRun v hstack hsize hbase hi h1

theorem multiDelegatedRevokePublicRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {tag : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+52 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hvalid : wordArrayValid ee.calldata)
    (hreq : L.get? "multiDelegatedRequests" = some (.array (delegatedBatchValues .revoke ee.calldata
      (UInt256.ofNat (wordArrayOffset ee.calldata+36)) (wordArrayLength ee.calldata))))
    (hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 224)))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1256⟩
      (UInt256.ofNat (wordArrayLength ee.calldata)::UInt256.ofNat (wordArrayOffset ee.calldata+36)::tag::R)
      (Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)) aw out σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeInitial++[multiDelegatedRevokeLoop])
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ RDret fork (deployedRuntime v) g s0 σ' ByteArray.empty) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeInitial++[multiDelegatedRevokeLoop]) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeInitial++[multiDelegatedRevokeLoop]) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let n := wordArrayLength ee.calldata
  let base := UInt256.ofNat (wordArrayOffset ee.calldata+36)
  let initial := Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)
  let L1 := L.insert "availableValue" (.int (Int.ofNat ee.weiValue.toNat)) |>.insert "i" (.int 0)
  have hb : base.toNat=wordArrayOffset ee.calldata+36 := ulit_toNat' _
    (by have := hvalid.2.1; have := hvalid.2.2.1; change _ < 2^256; omega)
  have hbase : base.toNat+32*n < UInt256.size := by
    rw [hb]
    have := hvalid.2.1
    have he : wordArrayOffset ee.calldata+36+32*n ≤ ee.calldata.size := hvalid.2.2.2.2
    change _ < 2^256
    omega
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1256_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd
  have hr1 : RD fork (deployedRuntime v) ee g s0 ⟨1298⟩
      (multiDelegatedRevokeLoopStack n 0 base ee.weiValue (tag::R)) initial a1 out σ k1 C1 := by
    have hm : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = UInt256.lnot ⟨0⟩ := by decide
    simpa only [easBlocks.eas_block_1256_stack,multiDelegatedRevokeLoopStack,hm,u256_add_lnot_zero_eq_sub_one] using r1
  have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeInitial
      (.ok {contract := contract,locals := L1,immutables := immStore v} evm) := by
    exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure,envValue,hstate.env]; rfl))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil)
  have hf1 : MultiDelegatedRevokeLocals L1 (delegatedBatchValues .revoke ee.calldata base n) ee.weiValue 224 0 := by
    constructor <;> simp (disch := decide) only [L1,store_get_ne,store_get_self] <;>
      first | rfl | exact hreq | exact hheap
  have hstart : MultiDelegatedRevokeAt fork v ee g s0 n base tag R 0 L1 evm :=
    ⟨σ,initial,out,a1,k1,C1,UInt256.ofNat 224,ee.weiValue,hstate,by decide,by decide,hf1,
      by native_decide,by native_decide,by native_decide,hr1⟩
  rcases multiDelegatedRevokeLoopRun v hstack hvalid.2.1 hbase hstart with ⟨L2,e2,hsol2,h2⟩ | ⟨hsol2,hrev⟩ | ⟨hsol2,hstatic⟩
  · obtain ⟨σ2,mem2,out2,a2,k2,C2,heap2,av2,hs2,_,_,_,_,_,_,r2⟩ := h2
    exact Or.inl ⟨L2,e2,σ2,execBlock_append hsol1 (ExecBlock.consNormal hsol2 ExecBlock.nil),hs2,
      easMultiDelegatedRevokeDone v (by simp only [List.length_cons]; omega) r2⟩
  · exact Or.inr (Or.inl ⟨execBlock_append hsol1 (ExecBlock.consRevert hsol2),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append hsol1 (ExecBlock.consStatic hsol2),hstatic⟩)

end Benchmarks.EAS.EAS
