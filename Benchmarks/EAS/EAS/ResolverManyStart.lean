import Benchmarks.EAS.EAS.ResolverManyData
import Benchmarks.EAS.EAS.ResolverCallSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverManyEntryPC (rev : Bool) : UInt256 := if rev then ⟨15120⟩ else ⟨14497⟩

def resolverManyEntryStack (rev : Bool) (junk0 junk1 junk2 array target valuesPtr last available value : UInt256)
    (R : List UInt256) : List UInt256 :=
  if rev then junk0::junk1::array::target::valuesPtr::last::available::value::R
  else junk0::junk1::junk2::array::target::valuesPtr::last::available::value::R

theorem resolverManyStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {junk0 junk1 junk2 array target valuesPtr last available value ptr : UInt256} {R : List UInt256}
    (v : EASImmutables) (rev : Bool) (hstack : R.length+15 ≤ 1024)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverManyEntryPC rev)
      (resolverManyEntryStack rev junk0 junk1 junk2 array target valuesPtr last available value R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14256⟩
      ((ptr+UInt256.ofNat 4)::array::valuesPtr::resolverPreparePC true rev::
        ptr::value::ptr::target::ptr::⟨32⟩::ptr::last::available::value::R)
      (resolverManyHeaderMemory mem ptr rev) aw' rdata σ k' C' := by
  cases rev with
  | false =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14497_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1,k1,C1,?_⟩
    simpa only [easBlocks.eas_block_14497_stack, easBlocks.eas_block_14497_memory, hh,
      resolverPreparePC, resolverManyHeaderMemory, resolverManySelectorWord, Reasoning.Theory.writeWord,
      Bool.false_eq_true, if_false, if_true] using rd1
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15120_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1,k1,C1,?_⟩
    simpa only [easBlocks.eas_block_15120_stack, easBlocks.eas_block_15120_memory, hh,
      resolverPreparePC, resolverManyHeaderMemory, resolverManySelectorWord, Reasoning.Theory.writeWord, if_true] using rd1

end Benchmarks.EAS.EAS
