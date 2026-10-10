import Benchmarks.UniswapV3.Pool.RuntimeBlocks_049
import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

local macro "pool_oracle_write_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem oracleWriteStoreStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15206⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 8 ≤ 1024) : RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw swap6 (by pool_oracle_write_decode(v, 15206, 149, .SWAP6, none)) (by evm_ov),
    raw swap1 (by pool_oracle_write_decode(v, 15207, 144, .SWAP1, none)) (by evm_ov),
    raw swap6 (by pool_oracle_write_decode(v, 15208, 149, .SWAP6, none)) (by evm_ov),
    raw and (by pool_oracle_write_decode(v, 15209, 22, .AND, none)) (by evm_ov),
    raw swap3 (by pool_oracle_write_decode(v, 15210, 146, .SWAP3, none)) (by evm_ov),
    raw swap1 (by pool_oracle_write_decode(v, 15211, 144, .SWAP1, none)) (by evm_ov),
    raw swap3 (by pool_oracle_write_decode(v, 15212, 146, .SWAP3, none)) (by evm_ov)]
  have r1 := evm_run r0 with [
    raw or (by pool_oracle_write_decode(v, 15213, 23, .OR, none)) (by evm_ov),
    raw and (by pool_oracle_write_decode(v, 15214, 22, .AND, none)) (by evm_ov),
    raw swap3 (by pool_oracle_write_decode(v, 15215, 146, .SWAP3, none)) (by evm_ov),
    raw swap1 (by pool_oracle_write_decode(v, 15216, 144, .SWAP1, none)) (by evm_ov),
    raw swap3 (by pool_oracle_write_decode(v, 15217, 146, .SWAP3, none)) (by evm_ov),
    raw or (by pool_oracle_write_decode(v, 15218, 23, .OR, none)) (by evm_ov)]
  have r2 := evm_run r1 with [
    raw swap3 (by pool_oracle_write_decode(v, 15219, 146, .SWAP3, none)) (by evm_ov),
    raw swap1 (by pool_oracle_write_decode(v, 15220, 144, .SWAP1, none)) (by evm_ov),
    raw swap3 (by pool_oracle_write_decode(v, 15221, 146, .SWAP3, none)) (by evm_ov),
    raw and (by pool_oracle_write_decode(v, 15222, 22, .AND, none)) (by evm_ov),
    raw or (by pool_oracle_write_decode(v, 15223, 23, .OR, none)) (by evm_ov),
    raw swap1 (by pool_oracle_write_decode(v, 15224, 144, .SWAP1, none)) (by evm_ov)]
  exact r2.sstoreStatic hp (by pool_oracle_write_decode(v, 15225, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
