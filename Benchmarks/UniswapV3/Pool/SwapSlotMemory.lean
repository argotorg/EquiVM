import Benchmarks.UniswapV3.Pool.BoundedActiveWords
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapSlotHeadMem (mem : ByteArray) (p : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (slot0ReadHeadMem mem p σ I) (p + UInt256.ofNat 96).toNat
    (slot0FieldWord 25 2 σ I)

theorem swapSlotHeadMem_eq {mem : ByteArray} {aw p : UInt256}
    (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_2358_memory (ee := I) (σ := σ) (mem := mem) =
      swapSlotHeadMem mem p σ I := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  unfold swapSlotHeadMem
  rw [← slot0ReadHeadMem_eq σ I hm hb]
  rw [slot0FieldShift 25 2
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200)) (UInt256.ofNat 65535)
    σ I (by native_decide) (by native_decide)]
  simp only [uniswapV3Pool_block_2358_memory, uniswapV3Pool_block_10148_memory, hload,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide),
    Reasoning.Theory.writeWord]
  rfl

theorem swapSlotTailMem_eq (mem : ByteArray) (p : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_2440_taken_memory (mem := swapSlotHeadMem mem p σ I)
      (x0 := UInt256.ofNat 1) (x1 := solcSlotWordAt ⟨0⟩ σ I)
      (x2 := p) (x3 := UInt256.ofNat 65535) =
      wordArrayAllocMem mem p (slot0StructWords σ I) := by
  exact slot0ReadTailMem_eq mem p σ I hb

theorem swapSlotReadHeadBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2358⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (ha : BoundedActiveWords aw limit)
    (hb : p.toNat + 224 ≤ limit) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2440⟩
      (UInt256.ofNat 1 :: solcSlotWordAt ⟨0⟩ σ ee :: p :: UInt256.ofNat 65535 :: R)
      (swapSlotHeadMem mem p σ ee) aw' rdata σ k' C' ∧ BoundedActiveWords aw' limit := by
  have hsmall := ha.small
  have hb200 : p.toNat + 224 ≤ 2 ^ 200 := hb.trans hsmall
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hp32 := uadd_word_ofNat_toNat p 32
    (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  have hp64 := uadd_word_ofNat_toNat p 64
    (show p.toNat + 64 < UInt256.size by change _ < 2 ^ 256; omega)
  have hp96 := uadd_word_ofNat_toNat p 96
    (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2358 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_2358_stack, hload, h64,
    swapSlotHeadMem_eq σ ee hm hb200] at rr
  have hout := BoundedActiveWords.expand32
    (BoundedActiveWords.expand32
      (BoundedActiveWords.expand32
        (BoundedActiveWords.expand32 ha (show p.toNat + 32 ≤ limit by omega))
        (show (p + UInt256.ofNat 32).toNat + 32 ≤ limit by rw [hp32]; omega))
      (show (p + UInt256.ofNat 64).toNat + 32 ≤ limit by rw [hp64]; omega))
    (show (p + UInt256.ofNat 96).toNat + 32 ≤ limit by rw [hp96]; omega)
  exact ⟨_, kr, Cr, rr, hout⟩

theorem swapSlotReadHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2358⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2440⟩
      (UInt256.ofNat 1 :: solcSlotWordAt ⟨0⟩ σ ee :: p :: UInt256.ofNat 65535 :: R)
      (swapSlotHeadMem mem p σ ee) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', rd', ha'⟩ := swapSlotReadHeadBoundedX (v := v)
    rd hm (BoundedActiveWords.of_active hm.active) hb hov
  exact ⟨aw', k', C', rd', ha'.active⟩

end Benchmarks.UniswapV3.Pool
