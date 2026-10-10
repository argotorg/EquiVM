import Benchmarks.UniswapV3.Pool.OracleSearchBefore
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_070

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchAfterX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret card : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20581⟩
      (oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
        cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k C)
    (hcard : UInt256.land cardRaw (UInt256.ofNat 65535) = card)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr (oracleSearchBefore left right card σ ee))
    (hp : 128 ≤ beforePtr.toNat) (hsep : beforePtr.toNat + 128 ≤ p.toNat)
    (hov : R.length + 26 ≤ 1024) :
    let before := oracleSearchBefore left right card σ ee
    let after := oracleSearchAfter left right card σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨20184⟩
        (targetRaw :: before.timestamp :: timeRaw :: ⟨20717⟩ :: ⟨0⟩ ::
          oracleSearchStack (oracleSearchMiddle left right) left right beforePtr p
            cardRaw indexRaw targetRaw timeRaw ret R)
        (wordArrayAllocMem mem p after.words) (oracleReadFullAw mem aw p) rdata σ k' C' ∧
      ObservationMemory (wordArrayAllocMem mem p after.words) beforePtr before := by
  dsimp only
  have hne : card ≠ UInt256.ofNat 0 := by intro hz; apply hn; rw [hz]; rfl
  have hcard' : UInt256.land (UInt256.ofNat 65535) cardRaw = card := by
    rw [u256_land_comm]; exact hcard
  have rdMod := uniswapV3Pool_block_20581_taken (immWords := wordsOf (immStore v))
    (by evm_ov)
    (by simpa only [hcard'] using hne)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_20581_taken_stack, hcard',
    u256_add_comm (UInt256.ofNat 1)] at rdMod
  have hbound := oracleSearchRemainder_lt (oracleSearchMiddle left right + ⟨1⟩) card hn hc
  have rdRead := uniswapV3Pool_block_20598_taken (immWords := wordsOf (immStore v))
    (by evm_ov)
    (by rw [ult_one hbound]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdMod
  obtain ⟨kh, Ch, hCh, rdHead⟩ := oracleReadHeadX (v := v) true rdRead hm hb
    (by evm_ov)
  change RD _ _ _ _ ⟨20696⟩
    (p :: UInt256.ofNat 96 ::
      (if (oracleSearchAfter left right card σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
      p :: oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
        cardRaw indexRaw targetRaw timeRaw ret R)
    (observationReadHeadMem mem p (oracleSearchAfter left right card σ ee))
    (oracleReadHeadAw mem aw) rdata σ kh Ch at rdHead
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_20696_memory
      (mem := observationReadHeadMem mem p (oracleSearchAfter left right card σ ee))
      (x0 := p) (x1 := UInt256.ofNat 96)
      (x2 := if (oracleSearchAfter left right card σ ee).initialized then ⟨1⟩ else ⟨0⟩) =
      wordArrayAllocMem mem p (oracleSearchAfter left right card σ ee).words := by
    simp only [uniswapV3Pool_block_20696_memory, hp96]
    exact observationReadHeadMem_write mem p _
  obtain ⟨hheap, _, hpre, hcover⟩ := oracleReadCompletedMemory
    (oracleSearchAfter left right card σ ee) hm hb
  have hbefore' := MemoryPrefix.wordArray hpre hbefore (by omega)
    (by simpa only [OracleObservation.words, List.length_cons, List.length_nil] using hsep)
  have hload : memLoad beforePtr (wordArrayAllocMem mem p
      (oracleSearchAfter left right card σ ee).words) =
      (oracleSearchBefore left right card σ ee).timestamp := by
    simpa only [OracleObservation.words, Nat.mul_zero,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero,
      List.getElem_cons_zero] using hbefore'.load 0 (by simp [OracleObservation.words])
        (by simp only [OracleObservation.words, List.length_cons, List.length_nil]
            change _ < 2 ^ 256
            omega)
  have hloadAw : M (oracleReadFullAw mem aw p) beforePtr ⟨32⟩ =
      oracleReadFullAw mem aw p := by
    apply expandedWords32_eq_of_cover hheap.active (by omega)
    rw [hp128] at hcover
    omega
  have r := uniswapV3Pool_block_20696 (immWords := wordsOf (immStore v))
    (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdHead
  have hloadMem : memLoad beforePtr
      ((if (oracleSearchAfter left right card σ ee).initialized then
        (⟨1⟩ : UInt256) else ⟨0⟩).toByteArray.write
        0 (observationReadHeadMem mem p (oracleSearchAfter left right card σ ee))
        (p + UInt256.ofNat 96).toNat 32) =
      (oracleSearchBefore left right card σ ee).timestamp := by
    change memLoad beforePtr (uniswapV3Pool_block_20696_memory (mem := _) (x0 := _)
      (x1 := _) (x2 := _)) = _
    rw [hmem, hload]
  dsimp only [oracleReadFullAw] at hloadAw
  simp only [uniswapV3Pool_block_20696_stack, hmem, hloadMem,
    hloadAw] at r
  refine ⟨kh + 16, _, ?_, r, hbefore'⟩
  simp only [memExpansionCost, hloadAw, Nat.sub_self, Nat.add_zero, oracleReadFullAw]
  omega

end Benchmarks.UniswapV3.Pool
