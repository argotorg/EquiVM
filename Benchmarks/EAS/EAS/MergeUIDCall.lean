import Benchmarks.EAS.EAS.MergeUIDRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem mergeUIDCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists heap ret : UInt256} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024) (hh : heap.toNat ≤ 2^64-1) (hlo : 96 ≤ heap.toNat)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [.array (groups.map wordListValue),.int (Int.ofNat groups.flatten.length),.int (Int.ofNat heap.toNat)])
    (hm : WordArrayArrayMemoryView mem lists groups heap.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hsize : ee.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11975⟩
      (lists::UInt256.ofNat groups.flatten.length::ret::R) mem aw rdata σ k C) :
    let next := allocateNext heap.toNat (32+32*groups.flatten.length)
    (∃ mem' aw' k' C' words, words.length = groups.flatten.length ∧ next ≤ 2^64-1 ∧
      MemoryPrefix mem mem' heap.toNat ∧ WordArrayMemoryView mem' heap words next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (.internalCall "_mergeUIDs" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := immStore v} retVar
          (some [wordListValue words,.int (Int.ofNat next)])) evm) ∧
      RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (.internalCall "_mergeUIDs" args retVar) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  have hd : (mergeUIDArgs groups groups.flatten.length heap.toNat).get? "uidLists" = some (.array (groups.map wordListValue)) := store_get_self _ _ _
  have hn : (mergeUIDArgs groups groups.flatten.length heap.toNat).get? "uidsCount" = some (.int (Int.ofNat groups.flatten.length)) := by
    simp (disch := decide) only [mergeUIDArgs,store_get_ne,store_get_self]
  have hf : (mergeUIDArgs groups groups.flatten.length heap.toNat).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)) := by
    simp (disch := decide) only [mergeUIDArgs,store_get_ne,store_get_self]
  rcases mergeUIDRun (evm := evm) v hstack hh hlo hd hn hf hm hfree hsize hret rd with
    ⟨L',m,a,j,D,words,hw,hheap,hpre,hmem,hfree',hsol,hr⟩ | ⟨hsol,hrev⟩
  · exact Or.inl ⟨m,a,j,D,words,hw,hheap,hpre,hmem,hfree',
      internalCallFunctionReturn he mergeUID_lookup (mergeUID_bind groups groups.flatten.length heap.toNat) hsol,hr⟩
  · exact Or.inr ⟨internalCallFunctionRevert he mergeUID_lookup (mergeUID_bind groups groups.flatten.length heap.toNat) hsol,hrev⟩

end Benchmarks.EAS.EAS
