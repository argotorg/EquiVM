import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

local macro "pool_cross_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem tickCrossStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13596⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 12 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest
      (by pool_cross_decode(v, 13596, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 2)
      (by pool_cross_decode(v, 13597, 96, .Push .PUSH1, some (UInt256.ofNat 2, 1))) (by evm_ov),
    raw swap6
      (by pool_cross_decode(v, 13599, 149, .SWAP6, none)) (by evm_ov),
    raw dup7
      (by pool_cross_decode(v, 13600, 134, .DUP7, none)) (by evm_ov),
    raw signextend
      (by pool_cross_decode(v, 13601, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup7
      (by pool_cross_decode(v, 13602, 134, .DUP7, none)) (by evm_ov),
    raw signextend
      (by pool_cross_decode(v, 13603, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 0)
      (by pool_cross_decode(v, 13604, 96, .Push .PUSH1, some (UInt256.ofNat 0, 1))) (by evm_ov),
    raw swap1
      (by pool_cross_decode(v, 13606, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_cross_decode(v, 13607, 129, .DUP2, none)) (by evm_ov)]
  have r1 := evm_run r0 with [
    raw mstoreSymbolic
      (by pool_cross_decode(v, 13608, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by pool_cross_decode(v, 13609, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw swap8
      (by pool_cross_decode(v, 13611, 151, .SWAP8, none)) (by evm_ov),
    raw swap1
      (by pool_cross_decode(v, 13612, 144, .SWAP1, none)) (by evm_ov),
    raw swap8
      (by pool_cross_decode(v, 13613, 151, .SWAP8, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_cross_decode(v, 13614, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 64)
      (by pool_cross_decode(v, 13615, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw swap1
      (by pool_cross_decode(v, 13617, 144, .SWAP1, none)) (by evm_ov),
    raw swap7
      (by pool_cross_decode(v, 13618, 150, .SWAP7, none)) (by evm_ov)]
  have r2 := RD.keccak256 _ _ _ r1
    (by pool_cross_decode(v, 13619, 32, .KECCAK256, none)) rfl rfl rfl (by evm_ov)
  have r3 := evm_run r2 with [
    raw push1 (UInt256.ofNat 1)
      (by pool_cross_decode(v, 13620, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw dup2
      (by pool_cross_decode(v, 13622, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by pool_cross_decode(v, 13623, 1, .ADD, none)) (by evm_ov),
    raw dup1
      (by pool_cross_decode(v, 13624, 128, .DUP1, none)) (by evm_ov)]
  obtain ⟨_, _, r4⟩ := RD.sload r3
    (by pool_cross_decode(v, 13625, 84, .SLOAD, none)) (by evm_ov)
  have r5 := evm_run r4 with [
    raw swap1
      (by pool_cross_decode(v, 13626, 144, .SWAP1, none)) (by evm_ov),
    raw swap6
      (by pool_cross_decode(v, 13627, 149, .SWAP6, none)) (by evm_ov),
    raw sub
      (by pool_cross_decode(v, 13628, 3, .SUB, none)) (by evm_ov),
    raw swap1
      (by pool_cross_decode(v, 13629, 144, .SWAP1, none)) (by evm_ov),
    raw swap5
      (by pool_cross_decode(v, 13630, 148, .SWAP5, none)) (by evm_ov)]
  exact r5.sstoreStatic hp (by pool_cross_decode(v, 13631, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
