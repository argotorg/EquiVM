import Benchmarks.UniswapV3.Pool.SwapProtocolMemory
import Benchmarks.UniswapV3.Pool.SwapAccountingFirstLoad
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapProtocolUpdateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free tmp : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3536⟩
      ([d.feeAmount, c.feeProtocol, tmp, q, p] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 8 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3574⟩ (q :: p :: R)
        (swapProtocolUpdateMem mem p q c s d) aw' rdata σ k' C' ∧
      HeapMemory (swapProtocolUpdateMem mem p q c s d) aw' free ∧
      SwapStateMemory (swapProtocolUpdateMem mem p q c s d) p (swapProtocolUpdatedState c s d) ∧
      SwapIterationMemory (swapProtocolUpdateMem mem p q c s d) q (swapProtocolUpdatedData c d) ∧
      MemoryPrefix mem (swapProtocolUpdateMem mem p q c s d) p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  have hpword : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hqword : q.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq192 := uadd_word_ofNat_toNat q 192 (show q.toNat + 192 < UInt256.size by omega)
  have hp160 := uadd_word_ofNat_toNat p 160 (show p.toNat + 160 < UInt256.size by omega)
  have hfee := SwapIterationMemory.load_fee hd hqword
  have hs1 : SwapStateMemory
      (writeWord mem (q.toNat + 192) (swapProtocolUpdatedData c d).feeAmount) p s :=
    WordArrayMemory.write_disjoint hs _ _ (Or.inr (by change p.toNat + 224 ≤ _; omega))
  have hprotocol := SwapStateMemory.load_protocolFee hs1 hpword
  dsimp only [Reasoning.Theory.writeWord, swapProtocolUpdatedData, swapProtocolDelta] at hprotocol
  have hsum : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (UInt256.div d.feeAmount c.feeProtocol + s.protocolFee) =
        (swapProtocolUpdatedState c s d).protocolFee := by
    change uint128Word (swapProtocolDelta c d + s.protocolFee) =
      uint128Word (s.protocolFee + swapProtocolDelta c d)
    rw [u256_add_comm]
  have rr := uniswapV3Pool_block_3536 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_3536_stack, uniswapV3Pool_block_3536_memory,
    solcMask128, hfee, hq192, hp160, hprotocol, hsum] at rr
  have rr' : RD (deployedRuntime v) ee g s0 ⟨3574⟩ (q :: p :: R)
      (swapProtocolUpdateMem mem p q c s d)
      (M (M (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 192) ⟨32⟩)
        (p + UInt256.ofNat 160) ⟨32⟩) (p + UInt256.ofNat 160) ⟨32⟩) rdata σ
      (k + 33) (C + (98 + memExpansionCost aw (q + UInt256.ofNat 192) ⟨32⟩ +
        memExpansionCost (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 192) ⟨32⟩ +
        memExpansionCost (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 192) ⟨32⟩)
          (p + UInt256.ofNat 160) ⟨32⟩ +
        memExpansionCost
          (M (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 192) ⟨32⟩)
            (p + UInt256.ofNat 160) ⟨32⟩) (p + UInt256.ofNat 160) ⟨32⟩)) := by
    exact rr
  obtain ⟨hm0, hs0, hd0, hpre⟩ := swapProtocolUpdateMemory c s d hm hs hd hp hdisj
  have h192 : (q + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 := by rw [hq192]; omega
  have h160 : (p + UInt256.ofNat 160).toNat + 32 ≤ 2 ^ 200 := by rw [hp160]; omega
  have hm1 := hm0.expand32 (q + UInt256.ofNat 192) h192
  have hm2 := hm1.expand32 (q + UInt256.ofNat 192) h192
  have hm3 := hm2.expand32 (p + UInt256.ofNat 160) h160
  have hm4 := hm3.expand32 (p + UInt256.ofNat 160) h160
  refine ⟨_, _, _, ?_, rr', hm4, hs0, hd0, hpre, ?_⟩
  · dsimp only [memExpansionCost, M, expandedWords]; omega
  · exact (expandedWords_mono (off := q + UInt256.ofNat 192) (size := ⟨32⟩) hm.active h192).trans
      ((expandedWords_mono (off := q + UInt256.ofNat 192) (size := ⟨32⟩) hm1.active h192).trans
        ((expandedWords_mono (off := p + UInt256.ofNat 160) (size := ⟨32⟩) hm2.active h160).trans
          (expandedWords_mono hm3.active h160)))

end Benchmarks.UniswapV3.Pool
