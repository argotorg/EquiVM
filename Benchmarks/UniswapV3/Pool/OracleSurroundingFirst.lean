import Benchmarks.UniswapV3.Pool.OracleSurroundingRead
import Benchmarks.UniswapV3.Pool.OracleSurroundingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSurroundingStack (afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  afterPtr :: beforePtr :: card :: liquidity :: index :: tickRaw :: targetRaw :: timeRaw ::
    ⟨8⟩ :: ret :: R

theorem oracleSurroundingFirstX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18658⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hin : index.toNat < 65535)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadFullAw mem aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨18776⟩
        ((if oracleSurroundingFirst time target index σ ee then ⟨1⟩ else ⟨0⟩) ::
          oracleSurroundingStack afterPtr p card liquidity index tickRaw targetRaw timeRaw ret R)
        (wordArrayAllocMem mem p (oracleStoredObservation index σ ee).words)
        (oracleReadFullAw mem aw p) rdata σ k' C' := by
  have hindex : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) (by change _ < 65536; omega)
  have r1 := uniswapV3Pool_block_18658_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [hindex, ult_one (a := index) (b := UInt256.ofNat 65535) hin]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_18658_taken_stack, hindex] at r1
  obtain ⟨k2, C2, hC2, r2⟩ := oracleSurroundingHeadX (v := v) r1 hm hb (by evm_ov)
  have r3 := uniswapV3Pool_block_18761 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_18761_memory
      (mem := observationReadHeadMem mem p (oracleStoredObservation index σ ee))
      (x0 := p) (x1 := UInt256.ofNat 96)
      (x2 := if (oracleStoredObservation index σ ee).initialized then ⟨1⟩ else ⟨0⟩) =
      wordArrayAllocMem mem p (oracleStoredObservation index σ ee).words := by
    simp only [uniswapV3Pool_block_18761_memory, hp96]
    exact observationReadHeadMem_write mem p _
  simp only [uniswapV3Pool_block_18761_stack, hmem] at r3
  have hmask : UInt256.land (UInt256.ofNat 4294967295)
      (oracleStoredObservation index σ ee).timestamp =
      (oracleStoredObservation index σ ee).timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide)
      (oracleStoredTimestamp_lt index σ ee)
  obtain ⟨k4, C4, hC4, r4⟩ := oracleLteMonoX (v := v) time
    (oracleStoredObservation index σ ee).timestamp target r3 htime hmask htarget
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by first | omega | (dsimp only [oracleSurroundingStack, List.length]; omega))
  refine ⟨k4, C4, ?_, r4⟩
  simp only [memExpansionCost] at hC4
  dsimp only [oracleReadFullAw]
  omega

end Benchmarks.UniswapV3.Pool
