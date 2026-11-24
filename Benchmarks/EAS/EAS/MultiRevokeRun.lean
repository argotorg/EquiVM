import Benchmarks.EAS.EAS.MultiRevokeIteration
import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiRevokeLoop : Stmt := .while (localArrayGuard "i" "multiRequests") multiRevokeIteration

theorem multiRevokeLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n : Nat} {base : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size)
    (h : MultiRevokeAt fork v ee g s0 n base R 0 L evm) :
    (∃ L' evm', ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeLoop
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiRevokeAt fork v ee g s0 n base R n L' evm') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeLoop .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeLoop .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  apply execWhile_invariant (MultiRevokeAt fork v ee g s0 n base R)
    (MultiRevokeAt fork v ee g s0 n base R n) (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    ?_ (fun _ _ h => h) ?_ n 0 L evm (by omega) h
  · rintro i L1 e1 _ ⟨σ,mem,out,aw,k,C,heap,available,_,_,_,hf,_,_,_,_⟩
    simpa only [multiRevocationValues_length] using evalLocalArrayGuard
      (cfg := config) (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := e1) hf.index hf.requests
  · intro i L1 e1 hi h1
    exact multiRevokeIterationRun v hstack hsize hbase hi h1

theorem multiRevokePublicRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hvalid : wordArrayValid ee.calldata)
    (hreq : L.get? "multiRequests" = some (.array (multiRevocationValues ee.calldata
      (UInt256.ofNat (wordArrayOffset ee.calldata+36)) (wordArrayLength ee.calldata))))
    (hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat 224)))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3354⟩
      (UInt256.ofNat (wordArrayLength ee.calldata)::UInt256.ofNat (wordArrayOffset ee.calldata+36)::R)
      (Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)) aw out σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap),
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeInitial++[multiRevokeLoop])
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ RDret fork (deployedRuntime v) g s0 σ' ByteArray.empty) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeInitial++[multiRevokeLoop]) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeInitial++[multiRevokeLoop]) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let n := wordArrayLength ee.calldata
  let base := UInt256.ofNat (wordArrayOffset ee.calldata+36)
  let initial := Reasoning.Theory.writeWord ByteArray.empty 64 (UInt256.ofNat 224)
  have hb : base.toNat = wordArrayOffset ee.calldata+36 := ulit_toNat' _
    (by have := hvalid.2.1; have := hvalid.2.2.1; change _ < 2^256; omega)
  have hbase : base.toNat+32*n < UInt256.size := by
    rw [hb]
    have := hvalid.2.1
    have he : wordArrayOffset ee.calldata+36+32*n ≤ ee.calldata.size := hvalid.2.2.2.2
    change _ < 2^256
    omega
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3354_packed (immWords := wordsOf (immStore v)) (by omega) rd
  have hr1 : RD fork (deployedRuntime v) ee g s0 ⟨3396⟩ (multiRevokeLoopStack n 0 base ee.weiValue R) initial a1 out σ k1 C1 := by
    have hm : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = UInt256.lnot ⟨0⟩ := by decide
    simpa only [easBlocks.eas_block_3354_stack,multiRevokeLoopStack,hm,u256_add_lnot_zero_eq_sub_one] using r1
  have hs := multiRevokeInitialSource (fork := fork) (imms := immStore v) (evm := evm) hreq hheap
  rw [hstate.env] at hs
  obtain ⟨hsol1,hf1⟩ := hs
  have hstart : MultiRevokeAt fork v ee g s0 n base R 0 (multiRevokeInitialLocals L ee.weiValue) evm := by
    exact ⟨σ,initial,out,a1,k1,C1,UInt256.ofNat 224,ee.weiValue,hstate,by decide,by decide,hf1,
      by native_decide,by native_decide,by native_decide,hr1⟩
  rcases multiRevokeLoopRun v hstack hvalid.2.1 hbase hstart with ⟨L2,e2,hsol2,h2⟩ | ⟨hsol2,hrev⟩ | ⟨hsol2,hstatic⟩
  · obtain ⟨σ2,mem2,out2,a2,k2,C2,heap2,av2,hs2,_,_,_,_,_,_,r2⟩ := h2
    exact Or.inl ⟨L2,e2,σ2,execBlock_append hsol1 (ExecBlock.consNormal hsol2 ExecBlock.nil),hs2,
      easMultiRevokeDone v (by omega) r2⟩
  · exact Or.inr (Or.inl ⟨execBlock_append hsol1 (ExecBlock.consRevert hsol2),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append hsol1 (ExecBlock.consStatic hsol2),hstatic⟩)

end Benchmarks.EAS.EAS
