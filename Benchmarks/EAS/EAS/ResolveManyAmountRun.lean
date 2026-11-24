import Benchmarks.EAS.EAS.ResolveManyPayableEVM
import Benchmarks.EAS.EAS.ResolveManyLocals
import Benchmarks.EAS.EAS.HeapBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyAmountRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {array values available total value ptr : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hf : ResolveManyLocals locals ats words target available total rev last ptr.toNat i)
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hi : i < words.length) (hlen : words.length < UInt256.size) (hstack : R.length+14 ≤ 1024)
    (hs : SourceState s0 ee σ evm) (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableCheckedPC (resolveManyPayableSite rev))
      (resolveManyCheckedStack rev i array (UInt256.ofNat target.val) values available last.toUInt256 total value words.length R)
      mem aw rdata σ k C) :
    HeapBlockRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm (resolveOneAmountBlock ++ [resolveManyTotalUpdate,resolveManyIncrement])
      (fun L heap => ResolveManyLocals L ats words target (UInt256.sub available value) (total+value) rev last heap (i+1) ∧ value.toNat ≤ available.toNat)
      (resolveManyLoopPC rev)
      (resolveManyLoopStack rev (i+1) array (UInt256.ofNat target.val) values (UInt256.sub available value)
        last.toUInt256 (total+value) words.length R) mem ptr.toNat := by
  have hsource := resolveOneAmountSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hvalue hf.available
  have hstep := resolveManyAmount v rev hstack rd
  by_cases hb : value.toNat ≤ available.toNat
  · rw [if_pos hb] at hsource hstep
    obtain ⟨a,j,D,hr⟩ := hstep
    have hnext := resolveManyAccumulateSource (fork := fork) (value := value) (cfg := config) (imms := imms) (evm := evm)
      (hf.subtract value).total
      (by simpa (disch := decide) only [store_get_ne] using hvalue) (hf.subtract value).index (by omega)
    exact Or.inl ⟨_,evm,σ,mem,rdata,a,j,D,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
      by simpa only [u256_ofNat_toNat] using hh,⟨((hf.subtract value).add value).advance,hb⟩,
      execBlock_append hsource hnext,hr⟩
  · rw [if_neg hb] at hsource hstep
    exact HeapBlockRun.of_revert_prefix hsource hstep

end Benchmarks.EAS.EAS
