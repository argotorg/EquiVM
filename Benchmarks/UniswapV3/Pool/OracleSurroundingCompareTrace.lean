import Benchmarks.UniswapV3.Pool.OracleSurroundingFirst
import Benchmarks.UniswapV3.Pool.OracleSurroundingCompare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingOldCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19052⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr (oracleSurroundingOldest index card σ ee))
    (hend : beforePtr.toNat + 128 ≤ p.toNat) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨19067⟩
      ((if oracleSurroundingOldEnough time target index card σ ee then ⟨1⟩ else ⟨0⟩) ::
        oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k' C' := by
  have hload : memLoad beforePtr mem = (oracleSurroundingOldest index card σ ee).timestamp := by
    simpa only [OracleObservation.words, Nat.mul_zero,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero,
      List.getElem_cons_zero] using hbefore.load 0 (by simp [OracleObservation.words])
        (by simp only [OracleObservation.words, List.length_cons, List.length_nil]
            change _ < 2 ^ 256
            omega)
  have hloadAw : M aw beforePtr ⟨32⟩ = aw :=
    expandedWords32_eq_of_cover hm.active (by omega) (by omega)
  have r1 := uniswapV3Pool_block_19052 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_19052_stack,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_zero_add, hload, hloadAw] at r1
  have hmask : UInt256.land (UInt256.ofNat 4294967295)
      (oracleSurroundingOldest index card σ ee).timestamp =
      (oracleSurroundingOldest index card σ ee).timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide)
      (oracleSurroundingOldestTimestamp_lt index card σ ee)
  obtain ⟨k2, C2, hC2, r2⟩ := oracleLteMonoX (v := v) time
    (oracleSurroundingOldest index card σ ee).timestamp target r1 htime hmask htarget
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by first | omega | (dsimp only [oracleSurroundingStack, List.length]; omega))
  exact ⟨k2, C2, by omega, r2⟩

theorem oracleSurroundingOldRevertX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19067⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev (deployedRuntime v) g s0 := by
  have r1 := uniswapV3Pool_block_19067_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) rfl rd
  simp only [uniswapV3Pool_block_19067_fallthrough_stack] at r1
  exact uniswapV3Pool_block_19072 (immWords := wordsOf (immStore v)) (by evm_ov) r1

theorem oracleSurroundingZeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw afterPtr beforePtr liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18832⟩
      (oracleSurroundingStack afterPtr beforePtr ⟨0⟩ liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C) (hov : R.length + 26 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  have r1 := uniswapV3Pool_block_18832_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by decide) rd
  exact uniswapV3Pool_block_18852 (immWords := wordsOf (immStore v)) r1

theorem oracleSurroundingIndexX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18658⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C) (hidx : index.toNat < 2 ^ 16) (hin : ¬ index.toNat < 65535)
    (hov : R.length + 26 ≤ 1024) : RDinvalid (deployedRuntime v) g s0 := by
  have hindex : UInt256.land (UInt256.ofNat 65535) index = index := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide) hidx
  have r1 := uniswapV3Pool_block_18658_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hindex]; exact ult_zero (by change 65535 ≤ index.toNat; omega)) rd
  exact uniswapV3Pool_block_18674 (immWords := wordsOf (immStore v)) r1

end Benchmarks.UniswapV3.Pool
