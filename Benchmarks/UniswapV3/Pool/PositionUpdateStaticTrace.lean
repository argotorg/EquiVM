import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_073

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

local macro "pool_position_update_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem positionUpdateLiquidityStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21821⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 12 ≤ 1024) : RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw dup8 (by pool_position_update_decode(v, 21821, 135, .DUP8, none)) (by evm_ov)]
  obtain ⟨_, _, r1⟩ := RD.sload r0
    (by pool_position_update_decode(v, 21822, 84, .SLOAD, none)) (by evm_ov)
  have r2 := evm_run r1 with [
    raw push1 (UInt256.ofNat 1)
      (by pool_position_update_decode(v, 21823, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_position_update_decode(v, 21825, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_position_update_decode(v, 21827, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw shl (by pool_position_update_decode(v, 21829, 27, .SHL, none)) (by evm_ov),
    raw sub (by pool_position_update_decode(v, 21830, 3, .SUB, none)) (by evm_ov),
    raw not (by pool_position_update_decode(v, 21831, 25, .NOT, none)) (by evm_ov)]
  have r3 := evm_run r2 with [
    raw and (by pool_position_update_decode(v, 21832, 22, .AND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_position_update_decode(v, 21833, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_position_update_decode(v, 21835, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_position_update_decode(v, 21837, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw shl (by pool_position_update_decode(v, 21839, 27, .SHL, none)) (by evm_ov),
    raw sub (by pool_position_update_decode(v, 21840, 3, .SUB, none)) (by evm_ov)]
  have r4 := evm_run r3 with [
    raw dup5 (by pool_position_update_decode(v, 21841, 132, .DUP5, none)) (by evm_ov),
    raw and (by pool_position_update_decode(v, 21842, 22, .AND, none)) (by evm_ov),
    raw or (by pool_position_update_decode(v, 21843, 23, .OR, none)) (by evm_ov),
    raw dup9 (by pool_position_update_decode(v, 21844, 136, .DUP9, none)) (by evm_ov)]
  exact r4.sstoreStatic hp (by pool_position_update_decode(v, 21845, 85, .SSTORE, none)) (by evm_ov)

theorem positionUpdateGrowthStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21846⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 10 ≤ 1024) : RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest (by pool_position_update_decode(v, 21846, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_position_update_decode(v, 21847, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw dup9 (by pool_position_update_decode(v, 21849, 136, .DUP9, none)) (by evm_ov),
    raw add (by pool_position_update_decode(v, 21850, 1, .ADD, none)) (by evm_ov),
    raw dup7 (by pool_position_update_decode(v, 21851, 134, .DUP7, none)) (by evm_ov),
    raw swap1 (by pool_position_update_decode(v, 21852, 144, .SWAP1, none)) (by evm_ov)]
  exact r0.sstoreStatic hp (by pool_position_update_decode(v, 21853, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
