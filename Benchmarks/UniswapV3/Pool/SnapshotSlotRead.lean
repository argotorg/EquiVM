import Benchmarks.UniswapV3.Pool.SnapshotTickChecks
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.SnapshotInside
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotReadyStack (lower upper : Int) (σ : AccountMap) (I : ExecutionEnv)
    (p lowerRaw upperRaw ret : UInt256) (R : List UInt256) : List UInt256 :=
  [p, (tickOutside upper σ I).seconds, (tickOutside lower σ I).seconds,
   (tickOutside upper σ I).secondsPerLiquidity, (tickOutside lower σ I).secondsPerLiquidity,
   EVM.wordOfInt (tickOutside upper σ I).cumulative, EVM.wordOfInt (tickOutside lower σ I).cumulative,
   ⟨0⟩, ⟨0⟩, ⟨0⟩, upperRaw, lowerRaw, ret] ++ R

theorem snapshotSlotReadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret lowerRaw upperRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (lower upper : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨10148⟩
      (snapshotTickStack lower upper σ ee (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: upperRaw :: lowerRaw :: ret :: R))
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hticks : validTicks lower upper)
    (hl : UInt256.signextend (UInt256.ofNat 2) lowerRaw = EVM.wordOfInt lower)
    (hov : R.length + 25 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if slot0TickValue σ ee < lower then ⟨10298⟩ else ⟨10317⟩)
      (snapshotReadyStack lower upper σ ee p lowerRaw upperRaw ret R)
      (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' (p + ⟨224⟩) ∧
      Slot0Memory (wordArrayAllocMem mem p (slot0StructWords σ ee)) p σ ee := by
  simp only [snapshotTickStack, List.cons_append, List.nil_append] at rd
  obtain ⟨ar, kr, Cr, rdRead, ha⟩ := slot0ReadX (v := v) rd hm hb (by evm_ov)
  have htick := slot0TickValue_bounds σ ee
  have hc : UInt256.isZero (UInt256.slt
      (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (slot0TickValue σ ee)))
      (UInt256.signextend (UInt256.ofNat 2) lowerRaw)) =
      if slot0TickValue σ ee < lower then (⟨0⟩ : UInt256) else ⟨1⟩ := by
    rw [slot0TickWord_idem, hl, slt_wordOfInt (slot0TickValue σ ee) lower
      (by omega) (by omega) (by obtain ⟨_, hmin, _⟩ := hticks; omega)
      (by obtain ⟨hord, _, hmax⟩ := hticks; omega)]
    split <;> rfl
  have h96 := uadd_word_ofNat_toNat p 96 (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have h128 := uadd_word_ofNat_toNat p 128 (show p.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have h160 := uadd_word_ofNat_toNat p 160 (show p.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
  have h192 := uadd_word_ofNat_toNat p 192 (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  have ha' := activeWords_expand32
    (activeWords_expand32 (activeWords_expand32 (activeWords_expand32 ha
      (show (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 by rw [h96]; omega))
      (show (p + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 by rw [h128]; omega))
      (show (p + UInt256.ofNat 160).toNat + 32 ≤ 2 ^ 200 by rw [h160]; omega))
      (show (p + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 by rw [h192]; omega)
  have hheap := wordArrayAllocMem_heap mem p _ (slot0StructWords σ ee) hm.lower
    (by simp [slot0StructWords]) hb ha'
  have hregion := wordArrayAllocMem_region mem p (slot0StructWords σ ee) hm.lower
    (by simp [slot0StructWords])
  have hmem := slot0ReadTailMem_eq mem p σ ee hb
  by_cases hbelow : slot0TickValue σ ee < lower
  · have hr := uniswapV3Pool_block_10229_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hc, if_pos hbelow]; rfl) rdRead
    have hmem' : uniswapV3Pool_block_10229_fallthrough_memory
        (mem := slot0ReadHeadMem mem p σ ee) (x0 := UInt256.ofNat 96) (x1 := slot0FieldWord 25 2 σ ee)
        (x4 := solcSlotWordAt ⟨0⟩ σ ee) (x5 := p) (x6 := UInt256.ofNat 65535) =
        wordArrayAllocMem mem p (slot0StructWords σ ee) := hmem
    simp only [uniswapV3Pool_block_10229_fallthrough_stack, hmem'] at hr
    exact ⟨_, _, _, by simpa only [if_pos hbelow, snapshotReadyStack, List.cons_append, List.nil_append] using hr,
      hheap, hregion⟩
  · have hr := uniswapV3Pool_block_10229_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hc, if_neg hbelow]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRead
    simp only [uniswapV3Pool_block_10229_taken_stack, hmem] at hr
    exact ⟨_, _, _, by simpa only [if_neg hbelow, snapshotReadyStack, List.cons_append, List.nil_append] using hr,
      hheap, hregion⟩

end Benchmarks.UniswapV3.Pool
