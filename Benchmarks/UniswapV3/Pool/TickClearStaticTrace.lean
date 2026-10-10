import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_073

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

local macro "pool_clear_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem tickClearStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw tick base ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21964⟩ (tick :: base :: ret :: R)
      mem aw rdata σ k C) (hp : ee.perm = false) (hov : R.length + 6 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest
      (by pool_clear_decode(v, 21964, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 2)
      (by pool_clear_decode(v, 21965, 96, .Push .PUSH1, some (UInt256.ofNat 2, 1))) (by evm_ov),
    raw swap1
      (by pool_clear_decode(v, 21967, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_clear_decode(v, 21968, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_clear_decode(v, 21969, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup2
      (by pool_clear_decode(v, 21970, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_clear_decode(v, 21971, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 0)
      (by pool_clear_decode(v, 21972, 96, .Push .PUSH1, some (UInt256.ofNat 0, 1))) (by evm_ov)]
  have r1 := evm_run r0 with [
    raw swap1
      (by pool_clear_decode(v, 21974, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_clear_decode(v, 21975, 129, .DUP2, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_clear_decode(v, 21976, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by pool_clear_decode(v, 21977, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw swap3
      (by pool_clear_decode(v, 21979, 146, .SWAP3, none)) (by evm_ov),
    raw swap1
      (by pool_clear_decode(v, 21980, 144, .SWAP1, none)) (by evm_ov),
    raw swap3
      (by pool_clear_decode(v, 21981, 146, .SWAP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_clear_decode(v, 21982, 82, .MSTORE, none)) (by evm_ov)]
  have r2 := evm_run r1 with [
    raw push1 (UInt256.ofNat 64)
      (by pool_clear_decode(v, 21983, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup3
      (by pool_clear_decode(v, 21985, 130, .DUP3, none)) (by evm_ov)]
  have r3 := RD.keccak256 _ _ _ r2
    (by pool_clear_decode(v, 21986, 32, .KECCAK256, none)) rfl rfl rfl (by evm_ov)
  have r4 := evm_run r3 with [
    raw dup3
      (by pool_clear_decode(v, 21987, 130, .DUP3, none)) (by evm_ov),
    raw dup2
      (by pool_clear_decode(v, 21988, 129, .DUP2, none)) (by evm_ov)]
  exact r4.sstoreStatic hp (by pool_clear_decode(v, 21989, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
