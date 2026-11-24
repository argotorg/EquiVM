import Benchmarks.EAS.EAS.ResolveOneResolver
import Benchmarks.EAS.EAS.HeapPost

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOneAmountRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr available value ptr ret : UInt256} {R : List UInt256} {a : AttestationRecord} {target : AccountAddress}
    {rev last : Bool} (v : EASImmutables)
    (hf : ResolveOneLocals locals a target value available rev last ptr.toNat)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ ptr.toNat) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15777⟩
      (src::rev.toUInt256::UInt256.ofNat target.val::last.toUInt256::available::value::ret::R) mem aw rdata σ k C) :
    HeapReturnPost fork (value.toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm (resolveOneAmountBlock ++ [resolveOneResolver,resolveOneRefund] ++ resolveOneReturn)
      (.int (Int.ofNat value.toNat)) ret (value::R) mem ptr.toNat := by
  have hr := resolveOneAmount v (by simp only [List.length_cons]; omega) rd
  have hsource := resolveOneAmountSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hf.value hf.available
  by_cases hb : value.toNat ≤ available.toNat
  · rw [if_pos hb] at hr hsource
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hfinish := resolveOneResolverRun (imms := imms) v hf.subtract hstack hperm hs hview hsrc hdata hheap hh hret rd1
    exact (hfinish.prepend hsource (MemoryPrefix.refl _ _) (le_refl _)).withPost hb
  · rw [if_neg hb] at hr hsource
    exact HeapReturnPost.of_revert_prefix (front := resolveOneAmountBlock)
      (suffix := [resolveOneResolver,resolveOneRefund] ++ resolveOneReturn) hsource hr

end Benchmarks.EAS.EAS
