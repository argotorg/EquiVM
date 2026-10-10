import Benchmarks.UniswapV3.Pool.OracleReadMemory
import Benchmarks.UniswapV3.Pool.OracleSearchSource
import Benchmarks.UniswapV3.Pool.OracleLteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSearchStack
    (i left right beforePtr afterPtr cardRaw indexRaw targetRaw timeRaw ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  i :: right :: left :: afterPtr :: beforePtr :: cardRaw :: indexRaw :: targetRaw ::
    timeRaw :: ⟨8⟩ :: ret :: R

def oracleReadFullAw (mem : ByteArray) (aw p : UInt256) : UInt256 :=
  M (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩

theorem oracleSearchBeforeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p i left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret card : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20441⟩
      (oracleSearchStack i left right beforePtr afterPtr cardRaw indexRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hcard : UInt256.land cardRaw (UInt256.ofNat 65535) = card)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 26 ≤ 1024) :
    let before := oracleSearchBefore left right card σ ee
    let mid := oracleSearchMiddle left right
    ∃ k' C', C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if before.initialized then ⟨20581⟩ else ⟨20441⟩)
        (oracleSearchStack mid (if before.initialized then left else mid + ⟨1⟩) right p afterPtr
          cardRaw indexRaw targetRaw timeRaw ret R)
        (wordArrayAllocMem mem p before.words) (oracleReadFullAw mem aw p) rdata σ k' C' := by
  dsimp only
  have hne : card ≠ UInt256.ofNat 0 := by intro hz; apply hn; rw [hz]; rfl
  have rdMod := uniswapV3Pool_block_20441_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by simpa only [hcard] using hne)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_20441_taken_stack, hcard] at rdMod
  have hbound := oracleSearchRemainder_lt (oracleSearchMiddle left right) card hn hc
  have rdRead := uniswapV3Pool_block_20462_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [ult_one hbound]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdMod
  obtain ⟨kh, Ch, hCh, rdHead⟩ := oracleReadHeadX (v := v) false rdRead hm hb (by evm_ov)
  change RD _ _ _ _ ⟨20560⟩
    (p :: ⟨96⟩ :: (if (oracleSearchBefore left right card σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
      p :: oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
        cardRaw indexRaw targetRaw timeRaw ret R)
    (observationReadHeadMem mem p (oracleSearchBefore left right card σ ee))
    (oracleReadHeadAw mem aw) rdata σ kh Ch at rdHead
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  by_cases hi : (oracleSearchBefore left right card σ ee).initialized = true
  · have r := uniswapV3Pool_block_20560_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by simp only [hi, ↓reduceIte]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdHead
    refine ⟨kh + 9,
      Ch + (33 + memExpansionCost (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩),
      ?_, ?_⟩
    · change C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤
        Ch + (33 + memExpansionCost (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩)
      simp only [memExpansionCost, oracleReadFullAw]
      omega
    · simp only [uniswapV3Pool_block_20560_taken_memory] at r
      rw [show (p + (⟨96⟩ : UInt256)).toNat = p.toNat + 96 from hp96] at r
      change RD _ _ _ _ _ _
        (writeWord (observationReadHeadMem mem p _) (p.toNat + 96) _) _ _ _ _ _ at r
      rw [observationReadHeadMem_write] at r
      simpa only [oracleSearchStack, uniswapV3Pool_block_20560_taken_stack,
        hi, ↓reduceIte] using r
  · have hiz : (oracleSearchBefore left right card σ ee).initialized = false := by
      exact Bool.eq_false_of_not_eq_true hi
    have r := uniswapV3Pool_block_20560_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by simp only [hiz, Bool.false_eq_true, ↓reduceIte]; rfl) rdHead
    have r' := uniswapV3Pool_block_20571 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r
    refine ⟨kh + 9 + 7,
      Ch + (33 + memExpansionCost (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩) + 25,
      ?_, ?_⟩
    · change C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤
        Ch + (33 + memExpansionCost (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩) + 25
      simp only [memExpansionCost, oracleReadFullAw]
      omega
    · simp only [uniswapV3Pool_block_20560_fallthrough_memory] at r'
      rw [show (p + (⟨96⟩ : UInt256)).toNat = p.toNat + 96 from hp96] at r'
      change RD _ _ _ _ _ _
        (writeWord (observationReadHeadMem mem p _) (p.toNat + 96) _) _ _ _ _ _ at r'
      rw [observationReadHeadMem_write] at r'
      simpa only [oracleSearchStack, uniswapV3Pool_block_20571_stack,
        uniswapV3Pool_block_20560_fallthrough_stack, hiz, Bool.false_eq_true, ↓reduceIte,
        u256_add_comm (UInt256.ofNat 1)] using r'

end Benchmarks.UniswapV3.Pool
