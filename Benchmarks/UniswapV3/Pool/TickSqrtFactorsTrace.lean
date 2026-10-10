import Benchmarks.UniswapV3.Pool.TickSqrtModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_036
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_037
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_038
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickSqrtFactor4X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11812⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11843⟩
      (tickSqrtStep absTick ratio (4, 340214320654664324051920982716015181260) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 4) = ⟨0⟩
  · have out := uniswapV3Pool_block_11812_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11812_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11822 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11822_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor8X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11843⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11874⟩
      (tickSqrtStep absTick ratio (8, 340146287995602323631171512101879684304) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 8) = ⟨0⟩
  · have out := uniswapV3Pool_block_11843_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11843_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11853 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11853_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor16X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11874⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11905⟩
      (tickSqrtStep absTick ratio (16, 340010263488231146823593991679159461444) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 16) = ⟨0⟩
  · have out := uniswapV3Pool_block_11874_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11874_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11884 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11884_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor32X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11905⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11936⟩
      (tickSqrtStep absTick ratio (32, 339738377640345403697157401104375502016) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 32) = ⟨0⟩
  · have out := uniswapV3Pool_block_11905_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11905_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11915 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11915_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor64X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11936⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11967⟩
      (tickSqrtStep absTick ratio (64, 339195258003219555707034227454543997025) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 64) = ⟨0⟩
  · have out := uniswapV3Pool_block_11936_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11936_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11946 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11946_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor128X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11967⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11998⟩
      (tickSqrtStep absTick ratio (128, 338111622100601834656805679988414885971) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 128) = ⟨0⟩
  · have out := uniswapV3Pool_block_11967_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11967_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_11977 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_11977_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor256X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11998⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12030⟩
      (tickSqrtStep absTick ratio (256, 335954724994790223023589805789778977700) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 256) = ⟨0⟩
  · have out := uniswapV3Pool_block_11998_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_11998_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12009 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12009_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor512X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12030⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12062⟩
      (tickSqrtStep absTick ratio (512, 331682121138379247127172139078559817300) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 512) = ⟨0⟩
  · have out := uniswapV3Pool_block_12030_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12030_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12041 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12041_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor1024X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12062⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12094⟩
      (tickSqrtStep absTick ratio (1024, 323299236684853023288211250268160618739) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 1024) = ⟨0⟩
  · have out := uniswapV3Pool_block_12062_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12062_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12073 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12073_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor2048X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12094⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12126⟩
      (tickSqrtStep absTick ratio (2048, 307163716377032989948697243942600083929) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 2048) = ⟨0⟩
  · have out := uniswapV3Pool_block_12094_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12094_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12105 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12105_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor4096X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12126⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12158⟩
      (tickSqrtStep absTick ratio (4096, 277268403626896220162999269216087595045) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 4096) = ⟨0⟩
  · have out := uniswapV3Pool_block_12126_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12126_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12137 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12137_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor8192X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12158⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12190⟩
      (tickSqrtStep absTick ratio (8192, 225923453940442621947126027127485391333) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 8192) = ⟨0⟩
  · have out := uniswapV3Pool_block_12158_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12158_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12169 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12169_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor16384X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12190⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12222⟩
      (tickSqrtStep absTick ratio (16384, 149997214084966997727330242082538205943) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 16384) = ⟨0⟩
  · have out := uniswapV3Pool_block_12190_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12190_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12201 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12201_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor32768X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12222⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12254⟩
      (tickSqrtStep absTick ratio (32768, 66119101136024775622716233608466517926) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 32768) = ⟨0⟩
  · have out := uniswapV3Pool_block_12222_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12222_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12233 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12233_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor65536X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12254⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12287⟩
      (tickSqrtStep absTick ratio (65536, 12847376061809297530290974190478138313) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 65536) = ⟨0⟩
  · have out := uniswapV3Pool_block_12254_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12254_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12266 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12266_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor131072X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12287⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12319⟩
      (tickSqrtStep absTick ratio (131072, 485053260817066172746253684029974020) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 131072) = ⟨0⟩
  · have out := uniswapV3Pool_block_12287_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12287_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12299 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12299_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor262144X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12319⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12350⟩
      (tickSqrtStep absTick ratio (262144, 691415978906521570653435304214168) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 262144) = ⟨0⟩
  · have out := uniswapV3Pool_block_12319_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12319_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12331 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12331_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactor524288X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨12350⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12379⟩
      (tickSqrtStep absTick ratio (524288, 1404880482679654955896180642) :: absTick :: R) mem aw rdata σ k' C' := by
  by_cases hz : UInt256.land absTick (UInt256.ofNat 524288) = ⟨0⟩
  · have out := uniswapV3Pool_block_12350_taken (immWords := wordsOf (immStore v))
      hov (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_, _, by simpa only [tickSqrtStep, if_pos hz] using out⟩
  · have rdCalc := uniswapV3Pool_block_12350_fallthrough (immWords := wordsOf (immStore v))
      hov (isZero_eq_zero_of_ne hz) rd
    have out := uniswapV3Pool_block_12362 (immWords := wordsOf (immStore v)) (by evm_ov) rdCalc
    exact ⟨_, _, by simpa only [uniswapV3Pool_block_12362_stack,
      tickSqrtStep, if_neg hz] using out⟩

theorem tickSqrtFactorsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw absTick ratio : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11812⟩ (ratio :: absTick :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12379⟩
      (tickSqrtFactors.tail.foldl (tickSqrtStep absTick) ratio :: absTick :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨k0, C0, r0⟩ := tickSqrtFactor4X rd hov
  obtain ⟨k1, C1, r1⟩ := tickSqrtFactor8X r0 hov
  obtain ⟨k2, C2, r2⟩ := tickSqrtFactor16X r1 hov
  obtain ⟨k3, C3, r3⟩ := tickSqrtFactor32X r2 hov
  obtain ⟨k4, C4, r4⟩ := tickSqrtFactor64X r3 hov
  obtain ⟨k5, C5, r5⟩ := tickSqrtFactor128X r4 hov
  obtain ⟨k6, C6, r6⟩ := tickSqrtFactor256X r5 hov
  obtain ⟨k7, C7, r7⟩ := tickSqrtFactor512X r6 hov
  obtain ⟨k8, C8, r8⟩ := tickSqrtFactor1024X r7 hov
  obtain ⟨k9, C9, r9⟩ := tickSqrtFactor2048X r8 hov
  obtain ⟨k10, C10, r10⟩ := tickSqrtFactor4096X r9 hov
  obtain ⟨k11, C11, r11⟩ := tickSqrtFactor8192X r10 hov
  obtain ⟨k12, C12, r12⟩ := tickSqrtFactor16384X r11 hov
  obtain ⟨k13, C13, r13⟩ := tickSqrtFactor32768X r12 hov
  obtain ⟨k14, C14, r14⟩ := tickSqrtFactor65536X r13 hov
  obtain ⟨k15, C15, r15⟩ := tickSqrtFactor131072X r14 hov
  obtain ⟨k16, C16, r16⟩ := tickSqrtFactor262144X r15 hov
  obtain ⟨k17, C17, r17⟩ := tickSqrtFactor524288X r16 hov
  exact ⟨_, _, by simpa only [tickSqrtFactors, List.tail_cons, List.foldl_cons, List.foldl_nil] using r17⟩

end Benchmarks.UniswapV3.Pool
