import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifySource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiDelegatedRevokeVerifyAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (requests : List Value) (r : DelegatedRevocationBatch) (n i : Nat) (base available row data sig : UInt256)
    (initial : ByteArray) (start : Nat) (R : List UInt256) (j : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat) (heap : UInt256),
    SourceState s0 ee σ evm ∧ start ≤ heap.toNat ∧ heap.toNat ≤ 2^64-1 ∧ MemoryPrefix initial mem start ∧
    MultiDelegatedRevokeVerifyLocals L requests available heap.toNat i j (decide (i=n-1)) r ∧
    DelegatedRevocationBatchMemoryView mem row data sig r heap.toNat ∧
    memLoad (UInt256.ofNat 64) mem = heap ∧
    RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
      (multiDelegatedRevokeVerifyStack j base (UInt256.ofNat n) available (UInt256.ofNat n-⟨1⟩) row data R)
      mem aw out σ k C

theorem multiDelegatedRevokeVerifyIterationRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {requests : List Value} {r : DelegatedRevocationBatch}
    {n i j : Nat} {base available row data sig : UInt256} {initial : ByteArray} {start : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+32 ≤ 1024) (hlen : r.data.length=r.signatures.length)
    (hj : j < r.data.length)
    (h : MultiDelegatedRevokeVerifyAt fork v ee g s0 requests r n i base available row data sig initial start R j L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedRevokeVerifyAt fork v ee g s0 requests r n i base available row data sig initial start R (j+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeVerifyIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,hstate,hstart,hh,hprefix,hf,hv,hfree,rd⟩ := h
  have hjs : j < r.signatures.length := by omega
  have hp := easMultiDelegatedRevokeVerifyPrepare v (by omega) hv hh hfree hj hjs rd
  have hn := allocateNext_128 hh
  have he : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (.intLit 128) =
      .ok (.int (Int.ofNat 128)) := by simp only [evalExpr?,pure]; rfl
  by_cases hg : heap.toNat+128 ≤ 2^64-1
  · rw [if_pos hg] at hp
    obtain ⟨mem1,dp,sp,a1,k1,C1,hp1,hv1,hfree1,r1⟩ := hp
    simp only [List.cons_append,List.nil_append] at r1
    let next := heap.toNat+128
    let L1 := allocateBlockLocals L next
    have hn1 : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256; dsimp only [next]; omega)
    have hsol1 := allocateBlock_ok (fork := fork) he hf.outer.heap (by rw [hn]; exact ⟨hg,by omega⟩)
    rw [hn] at hsol1
    have hf1 : MultiDelegatedRevokeVerifyLocals L1 requests available next i j (decide (i=n-1)) r := hf.allocated next
    have hargs := multiDelegatedRevokeVerifyArgs_eval (imms := immStore v) (evm := evm) hf1 hj hjs
    have hcall := verifyRevokeCallRun (L := L1) (heap := UInt256.ofNat next) (ptr := heap)
      (dataPtr := dp) (sigPtr := sp) (r := r.request j hj hjs) (retVar := "__c0$allocation") v
      (by simpa only [hn1] using hargs) (by simp only [List.length_cons]; omega) hstate
      (by simpa only [hn1] using hv1) hfree1 (by rw [hn1]; exact hg)
      (by rw [easPatchedValidJumps v]; jump_dest) r1
    rcases hcall with (⟨e2,σ2,mem2,out2,a2,k2,C2,heap2,hs2,hlo2,hh2,hp2,hfree2,hsol2,r2⟩ | ⟨hbad,hrev⟩) | ⟨hbad,hstatic⟩
    · simp only [hn1] at hlo2 hp2
      let L2 := multiDelegatedRevokeVerifyCallLocals L1 heap2
      have hf2 : MultiDelegatedRevokeVerifyLocals L2 requests available heap2 i j (decide (i=n-1)) r := hf1.called heap2
      have hsol2b : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm multiDelegatedRevokeVerify
          (.ok {contract := contract,locals := L2,immutables := immStore v} e2) :=
        heapResultBlock_ok (result := "__c0") (cursor := "$EAS.freeMemory") hsol2 hf1.outer.heap (by decide) (by decide) (by decide)
      have hjb : j+1<UInt256.size := by have := hv.data.span; change _ < 2^256; omega
      have hsol3 := execLocalCastIncrement (fork := fork) (cfg := config) (frame := {contract := contract,locals := L2,immutables := immStore v})
        (evm := e2) hf2.index hjb
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_1652_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      have hn2 : (UInt256.ofNat heap2).toNat=heap2 := ulit_toNat' _ (by change heap2<2^256; omega)
      have hinc : UInt256.ofNat j+UInt256.ofNat 1=UInt256.ofNat (j+1) :=
        (u256_add_comm _ _).trans (u256_one_add_ofNat j)
      have hp12 : MemoryPrefix mem mem2 heap.toNat := hp1.trans (hp2.mono (by dsimp only [next]; omega))
      refine Or.inl ⟨L2.insert "j" (.int (Int.ofNat (j+1))),e2,?_,σ2,mem2,out2,a3,k3,C3,UInt256.ofNat heap2,
        hs2,by rw [hn2]; dsimp only [next] at hlo2; omega,by rw [hn2]; exact hh2,
        hprefix.trans (hp12.mono hstart),?_,?_,hfree2,?_⟩
      · simpa only [multiDelegatedRevokeVerifyIteration,List.append_assoc] using
          execBlock_append hsol1 (execBlock_append hsol2b (ExecBlock.consNormal hsol3 ExecBlock.nil))
      · rw [hn2]; exact hf2.increment
      · rw [hn2]; exact hv.preserve hp12 (by dsimp only [next] at hlo2; omega) (by change heap2<2^256; omega)
      · simpa only [easBlocks.eas_block_1652_stack,hinc,multiDelegatedRevokeVerifyStack] using r3
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [multiDelegatedRevokeVerifyIteration,multiDelegatedRevokeVerify,heapResultBlock,List.append_assoc] using
        execBlock_append hsol1 (execBlock_append_term (s2 := [localCastIncrement "j"])
          (ExecBlock.consRevert (stmts := (multiDelegatedRevokeVerify.tail)) hbad) (by intros; exact nofun))
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      simpa only [multiDelegatedRevokeVerifyIteration,multiDelegatedRevokeVerify,heapResultBlock,List.append_assoc] using
        execBlock_append hsol1 (execBlock_append_term (s2 := [localCastIncrement "j"])
          (ExecBlock.consStatic (stmts := (multiDelegatedRevokeVerify.tail)) hbad) (by intros; exact nofun))
  · rw [if_neg hg] at hp
    refine Or.inr (Or.inl ⟨?_,hp⟩)
    have hbad := allocateBlock_revert (fork := fork) he hf.outer.heap (by rw [hn]; exact fun h => hg h.1)
    simpa only [multiDelegatedRevokeVerifyIteration,List.append_assoc] using
      execBlock_append_term (s2 := multiDelegatedRevokeVerify++[localCastIncrement "j"]) hbad (by intros; exact nofun)

end Benchmarks.EAS.EAS
