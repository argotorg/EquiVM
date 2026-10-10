import Benchmarks.UniswapV3.Pool.OracleSurroundingFirst
import Benchmarks.UniswapV3.Pool.OracleSurroundingOldest

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingCandidateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18832⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 26 ≤ 1024) :
    let candidate := oracleSurroundingCandidate index card σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if candidate.initialized then ⟨19052⟩ else ⟨18966⟩)
        (oracleSurroundingStack afterPtr p card liquidity index tickRaw targetRaw timeRaw ret R)
        (wordArrayAllocMem mem p candidate.words) (oracleReadFullAw mem aw p) rdata σ k' C' := by
  dsimp only
  have hcard : UInt256.land (UInt256.ofNat 65535) card = card := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hc
  have hne : card ≠ UInt256.ofNat 0 := by intro hz; apply hn; rw [hz]; rfl
  have r1 := uniswapV3Pool_block_18832_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hcard]; exact hne)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_18832_taken_stack, hcard,
    u256_add_comm (UInt256.ofNat 1), u256_land_comm (UInt256.ofNat 65535)] at r1
  have hbound := oracleSearchRemainder_lt
    (UInt256.land (index + ⟨1⟩) (UInt256.ofNat 65535)) card hn hc
  change (oracleSearchLeft index card).toNat < 65535 at hbound
  have hleft : UInt256.land (UInt256.ofNat 65535) (oracleSearchLeft index card) =
      oracleSearchLeft index card := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) (by change _ < 65536; omega)
  have r2 := uniswapV3Pool_block_18853_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by change UInt256.lt (UInt256.land (UInt256.ofNat 65535)
          (oracleSearchLeft index card)) (UInt256.ofNat 65535) ≠ UInt256.ofNat 0
        rw [hleft, ult_one hbound]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_18853_taken_stack] at r2
  change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 65535) (oracleSearchLeft index card) :: _) _ _ _ _ _ _ at r2
  rw [hleft] at r2
  obtain ⟨k3, C3, hC3, r3⟩ := oracleReadHeadAtX (v := v) 18869 (Or.inr (Or.inr rfl))
    r2 hm hb (by evm_ov)
  change RD _ _ _ _ ⟨18955⟩
    (p :: UInt256.ofNat 96 ::
      (if (oracleSurroundingCandidate index card σ ee).initialized then ⟨1⟩ else ⟨0⟩) ::
      p :: oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
    (observationReadHeadMem mem p (oracleSurroundingCandidate index card σ ee))
    (oracleReadHeadAw mem aw) rdata σ k3 C3 at r3
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_18955_taken_memory
      (mem := observationReadHeadMem mem p (oracleSurroundingCandidate index card σ ee))
      (x0 := p) (x1 := UInt256.ofNat 96)
      (x2 := if (oracleSurroundingCandidate index card σ ee).initialized then ⟨1⟩ else ⟨0⟩) =
      wordArrayAllocMem mem p (oracleSurroundingCandidate index card σ ee).words := by
    simp only [uniswapV3Pool_block_18955_taken_memory, hp96]
    exact observationReadHeadMem_write mem p _
  have hmemf : uniswapV3Pool_block_18955_fallthrough_memory
      (mem := observationReadHeadMem mem p (oracleSurroundingCandidate index card σ ee))
      (x0 := p) (x1 := UInt256.ofNat 96)
      (x2 := if (oracleSurroundingCandidate index card σ ee).initialized then ⟨1⟩ else ⟨0⟩) =
      wordArrayAllocMem mem p (oracleSurroundingCandidate index card σ ee).words := hmem
  refine ⟨k3 + 9,
    C3 + (33 + memExpansionCost (oracleReadHeadAw mem aw) (p + UInt256.ofNat 96) ⟨32⟩), ?_, ?_⟩
  · simp only [memExpansionCost, oracleReadFullAw]
    omega
  · cases hi : (oracleSurroundingCandidate index card σ ee).initialized with
    | false =>
      have r4 := uniswapV3Pool_block_18955_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by simp only [hi, Bool.false_eq_true, ↓reduceIte]; rfl) r3
      rw [hmemf] at r4
      simpa only [uniswapV3Pool_block_18955_fallthrough_stack,
        oracleSurroundingStack, hi, Bool.false_eq_true, ↓reduceIte] using r4
    | true =>
      have r4 := uniswapV3Pool_block_18955_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by simp only [hi, ↓reduceIte]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      rw [hmem] at r4
      simpa only [uniswapV3Pool_block_18955_taken_stack,
        oracleSurroundingStack, hi, ↓reduceIte] using r4

end Benchmarks.UniswapV3.Pool
