import Benchmarks.EAS.EAS.TryRecoverEVM
import Benchmarks.EAS.EAS.TryRecoverCallSource
import Benchmarks.EAS.EAS.HeapCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem recoveryError_bound (a : AccountAddress) :
    recoveryError a < 4 ∧ (recoveryError a = 0 → a ≠ 0) := by
  by_cases hz : a = 0
  · simp only [recoveryError,if_pos hz]
    exact ⟨by decide,by intro h; contradiction⟩
  · simp only [recoveryError,if_neg hz]
    exact ⟨by decide,fun _ => hz⟩

theorem tryRecoverRun {L imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hhash : L.get? "hash" = some (wordBytes32Value hash))
    (hsigV : L.get? "v" = some (.int (Int.ofNat sigV.toNat)))
    (hr : L.get? "r" = some (wordBytes32Value r)) (hsigS : L.get? "s" = some (wordBytes32Value s))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hstack : R.length+11 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hv : sigV.toNat < 2^8) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩ (hash::sigV::r::s::ret::R) mem aw rdata σ k C) :
    ∃ (a : AccountAddress) (error : Nat), error < 4 ∧ (error = 0 → a ≠ 0) ∧
      HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := imms}
        evm tryRecoverFunction.body (.tuple [.address a,.int (Int.ofNat error)])
        ret (UInt256.ofNat error::UInt256.ofNat a.val::R) mem heap.toNat := by
  by_cases hi : ecdsaHalfOrder < s.toNat
  · obtain ⟨k',C',rd'⟩ := tryRecoverHighEVM v hstack hi hret rd
    refine ⟨0,3,by decide,by intro he; contradiction,Or.inl ?_⟩
    refine ⟨{contract := contract,locals := L,immutables := imms},evm,σ,mem,rdata,aw,k',C',heap.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,?_,?_,rd'⟩
    · simpa only [u256_ofNat_toNat] using hh
    · exact tryRecoverHighSource hsigS hf hi
  · obtain ⟨evm',σ',success,out,a,hcall,hs',hout,hprefix,hfree,hfinish⟩ :=
      tryRecoverLowEVM v hstack hi hs hh hmem hv hlo (by change heap.toNat+128 < 2^256; omega) hret rd
    have hsrc := tryRecoverLowSource (imms := imms) hhash hsigV hr hsigS hf hi hcall hout
    refine ⟨a,recoveryError a,(recoveryError_bound a).1,(recoveryError_bound a).2,?_⟩
    cases success with
    | false => exact Or.inr ⟨hsrc,hfinish⟩
    | true =>
      obtain ⟨L',hsrc⟩ := hsrc
      obtain ⟨aw',k',C',rd'⟩ := hfinish
      refine Or.inl ⟨_,evm',σ',_,out,aw',k',C',heap.toNat,hs',le_refl _,hheap,hprefix,?_,hsrc,rd'⟩
      simpa only [u256_ofNat_toNat] using hfree

theorem tryRecoverCallRun {L imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := imms} evm args =
      .ok [wordBytes32Value hash,.int (Int.ofNat sigV.toNat),wordBytes32Value r,wordBytes32Value s,
        .int (Int.ofNat heap.toNat)])
    (hstack : R.length+11 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hmem : 96 ≤ mem.size)
    (hv : sigV.toNat < 2^8) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩ (hash::sigV::r::s::ret::R) mem aw rdata σ k C) :
    ∃ (a : AccountAddress) (error : Nat), error < 4 ∧ (error = 0 → a ≠ 0) ∧
      HeapCallRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := imms}
        evm "ECDSA_tryRecover" args retVar (.tuple [.address a,.int (Int.ofNat error)])
        ret (UInt256.ofNat error::UInt256.ofNat a.val::R) mem heap.toNat := by
  obtain ⟨a,error,herr,hzero,h⟩ := tryRecoverRun (L := tryRecoverArgs hash sigV r s heap.toNat) (imms := imms) v
    (by simp (disch := decide) only [tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [tryRecoverArgs,store_get_ne,store_get_self])
    (by simp (disch := decide) only [tryRecoverArgs,store_get_ne,store_get_self])
    hstack hs hh hmem hv hlo hheap hret rd
  exact ⟨a,error,herr,hzero,h.call he tryRecover_lookup (tryRecover_bind hash sigV r s heap.toNat)⟩

end Benchmarks.EAS.EAS
