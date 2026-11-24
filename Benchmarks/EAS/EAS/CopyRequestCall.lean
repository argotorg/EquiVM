import Benchmarks.EAS.EAS.CopyRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem requestCopyRunValid_data {cd : ByteArray} {src heap : UInt256}
    (h : requestCopyRunValid cd src (UInt256.ofNat cd.size) heap) : requestDataValid cd src :=
  ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem easCopyRequest_branches {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap stop ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+14 ≤ 1024) (hlo : 96 ≤ heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5344⟩ (src::stop::ret::R) mem aw rdata σ k C) :
    (requestCopyRunValid ee.calldata src stop heap →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
        (requestCopyMemory mem ee.calldata src heap) aw' rdata σ k' C') ∧
    (¬ requestCopyRunValid ee.calldata src stop heap → RDrev fork (deployedRuntime v) g s0) := by
  have h := easCopyRequest v hstack hlo hh hfree hret rd
  constructor
  · intro hv
    rw [if_pos hv] at h
    exact h
  · intro hv
    rw [if_neg hv] at h
    exact h

theorem copyRequestCall_branches {locals imms : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (he : evalExprs? config {contract := contract,locals := locals,immutables := imms} evm args = .ok [r.tuple,.int (Int.ofNat heap)]) :
    (copyRequestValid heap r.data.size →
      ExecStmt fork config {contract := contract,locals := locals,immutables := imms} evm (.internalCall "_copyAttestationData" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := imms} retVar
          (some [.tuple [],.int (Int.ofNat (copyRequestNext heap r.data.size))])) evm)) ∧
    (¬ copyRequestValid heap r.data.size →
      ExecStmt fork config {contract := contract,locals := locals,immutables := imms} evm (.internalCall "_copyAttestationData" args retVar) .reverted) := by
  have h := copyRequestCall (fork := fork) (retVar := retVar) he
  constructor
  · intro hv
    rw [if_pos hv] at h
    exact h
  · intro hv
    rw [if_neg hv] at h
    exact h

theorem copyRequestCallRun {locals : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw src heap ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := locals,immutables := immStore v} evm args =
      .ok [(requestDataRecord ee.calldata src).tuple,.int (Int.ofNat heap.toNat)])
    (hstack : R.length+14 ≤ 1024) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hsize : ee.calldata.size < 2^255+4)
    (hd : requestDataValid ee.calldata src) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5344⟩ (src::UInt256.ofNat ee.calldata.size::ret::R) mem aw rdata σ k C) :
    let next := UInt256.ofNat (allocateNext heap.toNat 192)
    let final := requestCopyMemory mem ee.calldata src heap
    let finalHeap := copyRequestNext heap.toNat (requestDataRecord ee.calldata src).data.size
    (ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
      (.internalCall "_copyAttestationData" args retVar)
      (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := immStore v} retVar
        (some [.tuple [],.int (Int.ofNat finalHeap)])) evm) ∧
      finalHeap ≤ 2^64-1 ∧ MemoryPrefix mem final heap.toNat ∧
      AttestationRequestMemoryView final heap next (requestDataRecord ee.calldata src) ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat finalHeap ∧ heap.toNat+192 ≤ finalHeap ∧
      next.toNat+32+32*(((requestDataRecord ee.calldata src).data.size+31)/32) = finalHeap ∧
      finalHeap ≤ final.size ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R) final aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
      (.internalCall "_copyAttestationData" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  have hsrc := copyRequestCall_branches (fork := fork) (retVar := retVar) he
  have hrun := easCopyRequest_branches v hstack hlo hh hfree hret rd
  have hguard := requestCopyRunValid_iff (heap := heap) hd
  by_cases hv : copyRequestValid heap.toNat (requestDataRecord ee.calldata src).data.size
  · have hm := requestCopyMemory_views mem ee.calldata src heap hlo hh hsize hd hv
    exact Or.inl ⟨hsrc.1 hv,hv.2.2.1,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.1,
      hm.2.2.2.2.2,hrun.1 (hguard.mpr hv)⟩
  · exact Or.inr ⟨hsrc.2 hv,hrun.2 (fun h => hv (hguard.mp h))⟩

end Benchmarks.EAS.EAS
