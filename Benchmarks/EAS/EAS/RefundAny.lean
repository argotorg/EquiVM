import Benchmarks.EAS.EAS.RefundRun
import Benchmarks.EAS.EAS.RefundStatic
import Benchmarks.EAS.EAS.HeapStatic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem refundRunAny {cfg : Config} {locals imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (he : evalExprs? cfg {contract := contract,locals := locals,immutables := imms} evm args =
      .ok [.int (Int.ofNat value.toNat),.int (Int.ofNat ptr.toNat)])
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    HeapCallOrStatic fork cfg (deployedRuntime v) ee g s0 {contract := contract,locals := locals,immutables := imms}
      evm "_refund" args retVar (.tuple []) ret R mem ptr.toNat := by
  by_cases hp : ee.perm = true
  · exact Or.inl (refundRun v hstack hp hs hheap hlo hh he hret rd)
  · have hp' : ee.perm = false := Bool.eq_false_iff.mpr hp
    by_cases hz : value = ⟨0⟩
    · subst value
      obtain ⟨a,j,D,hr⟩ := refundEVM_zero v (by omega) hret rd
      exact Or.inl (Or.inl ⟨evm,σ,mem,rdata,a,j,D,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
        by simpa only [u256_ofNat_toNat] using hh,refundCall_zero he,hr⟩)
    · by_cases hb : value.toNat ≤ (refundBalance evm).toNat
      · exact Or.inr ⟨refundCall_static he hz hb (by rw [hs.env]; exact hp'),
          refundEVM_static v hstack hp' hs hz hb rd⟩
      · exact Or.inl (Or.inr ⟨refundCall_insufficient he hz hb,
          refundEVM_insufficient v (by omega) hs hz hb rd⟩)

end Benchmarks.EAS.EAS
