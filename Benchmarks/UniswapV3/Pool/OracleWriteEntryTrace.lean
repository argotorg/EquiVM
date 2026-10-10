import Benchmarks.UniswapV3.Pool.OracleWriteReadMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleWriteEntryWords (a : OracleWriteArgs) : List UInt256 :=
  [a.cardinalityNext, a.cardinality, a.liquidity, EVM.wordOfInt a.tick, a.time, a.index, ⟨8⟩]

theorem oracleWriteReadInvalidRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords {a with time := timeRaw} ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hin : ¬ a.index.toNat < 65535) (hov : R.length + 15 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  have hi : UInt256.land (UInt256.ofNat 65535) a.index = a.index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hfit.1
  simp only [oracleWriteEntryWords, List.cons_append, List.nil_append] at rd
  have rr := uniswapV3Pool_block_14801_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by
      rw [hi]
      apply ult_zero
      change 65535 ≤ a.index.toNat
      omega) rd
  exact uniswapV3Pool_block_14822 (immWords := wordsOf (immStore v)) rr

theorem oracleWriteReadInvalidX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hin : ¬ a.index.toNat < 65535) (hov : R.length + 15 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  exact oracleWriteReadInvalidRawX (v := v) (timeRaw := a.time) a rd hfit hin hov

theorem oracleWriteReadRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords {a with time := timeRaw} ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (htime : UInt256.land timeRaw (UInt256.ofNat 4294967295) = a.time)
    (hin : a.index.toNat < 65535)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    let last := oracleStoredObservation a.index σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if last.timestamp = a.time then ⟨14924⟩ else ⟨14935⟩)
      (oracleWriteReadWords {a with time := timeRaw} p ++ ret :: R) (wordArrayAllocMem mem p last.words) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p last.words) aw' (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last := by
  have hi : UInt256.land (UInt256.ofNat 65535) a.index = a.index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hfit.1
  simp only [oracleWriteEntryWords, List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_14801_taken (immWords := wordsOf (immStore v))
    (by evm_ov)
    (by rw [hi, ult_one (show a.index.toNat < (UInt256.ofNat 65535).toNat from hin)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_14801_taken_stack, hi] at r1
  obtain ⟨_, _, r2⟩ := oracleWriteReadHeadX (v := v) r1 hm hb (by evm_ov)
  exact oracleWriteReadFinishRawX (v := v) a r2 hm hb htime (by evm_ov)

theorem oracleWriteReadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hin : a.index.toNat < 65535)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    let last := oracleStoredObservation a.index σ ee
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if last.timestamp = a.time then ⟨14924⟩ else ⟨14935⟩)
      (oracleWriteReadWords a p ++ ret :: R) (wordArrayAllocMem mem p last.words) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p last.words) aw' (p + ⟨128⟩) ∧
      ObservationMemory (wordArrayAllocMem mem p last.words) p last := by
  exact oracleWriteReadRawX (v := v) (timeRaw := a.time) a rd hfit
    (u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hfit.2.1) hin hm hb hov

theorem oracleWriteSameRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14924⟩
      (oracleWriteReadWords {a with time := timeRaw} p ++ ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (a.cardinality :: a.index :: R) mem aw rdata σ k' C' := by
  simp only [oracleWriteReadWords, List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_14924 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret r1
  exact ⟨_, _, r2⟩

theorem oracleWriteSameX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14924⟩
      (oracleWriteReadWords a p ++ ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (a.cardinality :: a.index :: R) mem aw rdata σ k' C' := by
  exact oracleWriteSameRawX (v := v) (timeRaw := a.time) a rd hret hov

end Benchmarks.UniswapV3.Pool
