import Benchmarks.EAS.EAS.TypedDataEVM
import Benchmarks.EAS.EAS.HeapCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem typedDataCallRun {L imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap domain structHash ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args =
      .ok [wordBytes32Value domain,wordBytes32Value structHash,.int (Int.ofNat heap.toNat)])
    (hstack : R.length+9 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15654⟩ (domain::structHash::ret::R) mem aw rdata σ k C) :
    HeapCallRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := imms}
      evm "ECDSA_toTypedDataHash" args retVar (wordBytes32Value (typedDataWord domain structHash))
      ret (typedDataWord domain structHash::R) mem heap.toNat := by
  have hsrc := typedDataSource (fork := fork) (L := typedDataArgs domain structHash heap.toNat) (imms := imms) (evm := evm)
    (domain := domain) (structHash := structHash) (heap := heap.toNat)
    (by simp only [typedDataArgs,store_get_self])
    (by simp (disch := decide) only [typedDataArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [typedDataArgs,store_get_ne,store_get_self])
  have hevm := typedDataEVM v hstack hh hlo hheap hret rd
  by_cases hg : allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128
  · rw [if_pos hg] at hsrc hevm
    obtain ⟨aw1,k1,C1,r1⟩ := hevm
    refine Or.inl ⟨evm,σ,typedDataMemory mem heap.toNat domain structHash,rdata,aw1,k1,C1,
      allocateNext heap.toNat 128,hs,hg.2,hg.1,typedDataMemory_prefix _ _ _ _,typedDataMemory_free _ _ _ _,?_,r1⟩
    exact internalCallFunctionReturn he typedData_lookup (typedData_bind domain structHash heap.toNat) hsrc
  · rw [if_neg hg] at hsrc hevm
    exact Or.inr ⟨internalCallFunctionRevert he typedData_lookup (typedData_bind domain structHash heap.toNat) hsrc,hevm⟩

end Benchmarks.EAS.EAS
