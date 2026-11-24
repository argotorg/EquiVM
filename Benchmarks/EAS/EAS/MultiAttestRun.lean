import Benchmarks.EAS.EAS.MultiAttestIteration
import Benchmarks.EAS.EAS.WhileInvariant
import Benchmarks.EAS.EAS.MergeUIDCall
import Benchmarks.EAS.EAS.WordArrayReturn

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestLoop : Stmt := .while (localArrayGuard "i" "multiRequests") multiAttestIteration
def multiAttestTail : Body := [multiAttestLoop]++multiAttestFinish

theorem multiAttestLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n : Nat} {base table : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size)
    (h : MultiAttestAt fork v ee g s0 n base table R 0 L evm) :
    (∃ L' evm', ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestLoop
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiAttestAt fork v ee g s0 n base table R n L' evm') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestLoop .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestLoop .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  apply execWhile_invariant (MultiAttestAt fork v ee g s0 n base table R)
    (MultiAttestAt fork v ee g s0 n base table R n) (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    ?_ (fun _ _ h => h) ?_ n 0 L evm (by omega) h
  · rintro i L1 e1 _ ⟨σ,mem,out,aw,k,C,heap,available,groups,_,_,_,hf,_,_⟩
    simpa only [multiRequestValues_length] using evalLocalArrayGuard
      (cfg := config) (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := e1) hf.index hf.requests
  · intro i L1 e1 hi h1
    exact multiAttestIterationRun v hstack hsize hbase hi h1

theorem multiAttestFinishRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n : Nat} {base table : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+26 ≤ 1024) (hsize : ee.calldata.size < UInt256.size)
    (h : MultiAttestAt fork v ee g s0 n base table R n L evm) :
    (∃ (L' : Store) (σ' : AccountMap) (words : List UInt256),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestFinish
        (.returned {contract := contract,locals := L',immutables := immStore v} evm (some [wordListValue words])) ∧
      SourceState s0 ee σ' evm ∧
      RDret fork (deployedRuntime v) g s0 σ' (wordBytes ([UInt256.ofNat 32,UInt256.ofNat words.length]++words))) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestFinish .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,available,groups,hstate,hh,hg,hf,hm,rd⟩ := h
  have hv : WordArrayArrayMemoryView mem table groups heap.toNat := by
    have hview := hm.view
    rw [← hg] at hview
    exact hview.finish
  have hlo : 96 ≤ heap.toNat := by have := hm.view.span; have := hm.low; omega
  have hfree : memLoad (UInt256.ofNat 64) mem = heap := by simpa only [u256_ofNat_toNat] using hm.free
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm multiAttestMergeArgs =
      .ok [.array (groups.map wordListValue),.int (Int.ofNat groups.flatten.length),.int (Int.ofNat heap.toNat)] := by
    simp only [multiAttestMergeArgs,evalExprs?,evalExpr?,hf.groups,hf.count,hf.heap,EvalResult.ofOption,bind,EvalResult.bind,pure]
  obtain ⟨a1,j1,D1,r1⟩ := easMultiAttestDone v (by omega) rd
  have hmerge := mergeUIDCallRun (retVar := "__c1$allocation") v
    (by simp only [multiAttestLoopStack,List.length_cons]; omega) hh hlo he hv hfree hsize
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  rcases hmerge with ⟨m2,a2,j2,D2,words,_,hcap,hpre,hwords,hfree2,hcall,r2⟩ | ⟨hcall,hrev⟩
  · let next := allocateNext heap.toNat (32+32*groups.flatten.length)
    let L2 := heapResultLocals L "__c1$allocation" "__c1" "$EAS.freeMemory" (wordListValue words) next
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
    have hret := easWordArrayReturn (heap := UInt256.ofNat next) v
      (by simp only [multiAttestLoopStack,List.length_cons]; omega)
      (by rw [hn]; exact hwords) (by rw [hn]; exact hcap) hfree2 r2
    have hsol := heapResultBlock_ok (result := "__c1") hcall hf.heap (by decide) (by decide) (by decide)
    refine Or.inl ⟨L2,σ,words,?_,hstate,hret⟩
    apply execBlock_append hsol
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    have hu : L2.get? "__c1" = some (wordListValue words) := heapResultLocals_result _ _ _ _ _ _ (by decide)
    change evalExprs? config {contract := contract,locals := L2,immutables := immStore v} evm [.var "__c1"] = .ok [wordListValue words]
    simp only [evalExprs?,evalExpr?,hu,EvalResult.ofOption,bind,EvalResult.bind,pure]
  · exact Or.inr ⟨execBlock_append_term (ExecBlock.consRevert hcall) (by intros; exact nofun),hrev⟩

theorem multiAttestRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n : Nat} {base table : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size)
    (h : MultiAttestAt fork v ee g s0 n base table R 0 L evm) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (words : List UInt256),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestTail
        (.returned {contract := contract,locals := L',immutables := immStore v} evm' (some [wordListValue words])) ∧
      SourceState s0 ee σ' evm' ∧
      RDret fork (deployedRuntime v) g s0 σ' (wordBytes ([UInt256.ofNat 32,UInt256.ofNat words.length]++words))) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestTail .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestTail .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  rcases multiAttestLoopRun v hstack hsize hbase h with ⟨L1,e1,hsol1,h1⟩ | ⟨hsol1,hrev⟩ | ⟨hsol1,hstatic⟩
  · rcases multiAttestFinishRun v (by omega) (by change ee.calldata.size < 2^256; omega) h1 with
      ⟨L2,σ2,words,hsol2,hs2,hret⟩ | ⟨hsol2,hrev⟩
    · exact Or.inl ⟨L2,e1,σ2,words,ExecBlock.consNormal hsol1 hsol2,hs2,hret⟩
    · exact Or.inr (Or.inl ⟨ExecBlock.consNormal hsol1 hsol2,hrev⟩)
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert hsol1,hrev⟩)
  · exact Or.inr (Or.inr ⟨ExecBlock.consStatic hsol1,hstatic⟩)

end Benchmarks.EAS.EAS
