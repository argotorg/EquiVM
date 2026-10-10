import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

macro "pool_initialize_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem oracleInitializeStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw time slot ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17514⟩ (time :: slot :: ret :: R) mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 9 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rpre0 := evm_run rd with [
    raw jumpdest
      (by pool_initialize_decode(v, 17514, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 64)
      (by pool_initialize_decode(v, 17515, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup1
      (by pool_initialize_decode(v, 17517, 128, .DUP1, none)) (by evm_ov),
    raw mloadSymbolic
      (by pool_initialize_decode(v, 17518, 81, .MLOAD, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_initialize_decode(v, 17519, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw dup2
      (by pool_initialize_decode(v, 17521, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by pool_initialize_decode(v, 17522, 1, .ADD, none)) (by evm_ov),
    raw dup3
      (by pool_initialize_decode(v, 17523, 130, .DUP3, none)) (by evm_ov)]
  have rpre1 := evm_run rpre0 with [
    raw mstoreSymbolic
      (by pool_initialize_decode(v, 17524, 82, .MSTORE, none)) (by evm_ov),
    raw push4 (UInt256.ofNat 4294967295)
      (by pool_initialize_decode(v, 17525, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw swap3
      (by pool_initialize_decode(v, 17530, 146, .SWAP3, none)) (by evm_ov),
    raw dup4
      (by pool_initialize_decode(v, 17531, 131, .DUP4, none)) (by evm_ov),
    raw and
      (by pool_initialize_decode(v, 17532, 22, .AND, none)) (by evm_ov),
    raw dup1
      (by pool_initialize_decode(v, 17533, 128, .DUP1, none)) (by evm_ov),
    raw dup3
      (by pool_initialize_decode(v, 17534, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_initialize_decode(v, 17535, 82, .MSTORE, none)) (by evm_ov)]
  have rpre2 := evm_run rpre1 with [
    raw push1 (UInt256.ofNat 0)
      (by pool_initialize_decode(v, 17536, 96, .Push .PUSH1, some (UInt256.ofNat 0, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by pool_initialize_decode(v, 17538, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw dup4
      (by pool_initialize_decode(v, 17540, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by pool_initialize_decode(v, 17541, 1, .ADD, none)) (by evm_ov),
    raw dup2
      (by pool_initialize_decode(v, 17542, 129, .DUP2, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17543, 144, .SWAP1, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_initialize_decode(v, 17544, 82, .MSTORE, none)) (by evm_ov),
    raw swap3
      (by pool_initialize_decode(v, 17545, 146, .SWAP3, none)) (by evm_ov)]
  have rpre3 := evm_run rpre2 with [
    raw dup3
      (by pool_initialize_decode(v, 17546, 130, .DUP3, none)) (by evm_ov),
    raw add
      (by pool_initialize_decode(v, 17547, 1, .ADD, none)) (by evm_ov),
    raw swap3
      (by pool_initialize_decode(v, 17548, 146, .SWAP3, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17549, 144, .SWAP1, none)) (by evm_ov),
    raw swap3
      (by pool_initialize_decode(v, 17550, 146, .SWAP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_initialize_decode(v, 17551, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_initialize_decode(v, 17552, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 96)
      (by pool_initialize_decode(v, 17554, 96, .Push .PUSH1, some (UInt256.ofNat 96, 1))) (by evm_ov)]
  have rpre4 := evm_run rpre3 with [
    raw swap1
      (by pool_initialize_decode(v, 17556, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_initialize_decode(v, 17557, 145, .SWAP2, none)) (by evm_ov),
    raw add
      (by pool_initialize_decode(v, 17558, 1, .ADD, none)) (by evm_ov),
    raw dup2
      (by pool_initialize_decode(v, 17559, 129, .DUP2, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17560, 144, .SWAP1, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_initialize_decode(v, 17561, 82, .MSTORE, none)) (by evm_ov),
    raw dup4
      (by pool_initialize_decode(v, 17562, 131, .DUP4, none)) (by evm_ov)]
  obtain ⟨kL, CL, rloaded⟩ := RD.sload rpre4
    (by pool_initialize_decode(v, 17563, 84, .SLOAD, none)) (by evm_ov)
  have rpost0 := evm_run rloaded with [
    raw push4 (UInt256.ofNat 4294967295)
      (by pool_initialize_decode(v, 17564, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw not
      (by pool_initialize_decode(v, 17569, 25, .NOT, none)) (by evm_ov),
    raw and
      (by pool_initialize_decode(v, 17570, 22, .AND, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17571, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_initialize_decode(v, 17572, 145, .SWAP2, none)) (by evm_ov),
    raw or
      (by pool_initialize_decode(v, 17573, 23, .OR, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17574, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_initialize_decode(v, 17575, 145, .SWAP2, none)) (by evm_ov)]
  have rpost1 := evm_run rpost0 with [
    raw and
      (by pool_initialize_decode(v, 17576, 22, .AND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_initialize_decode(v, 17577, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by pool_initialize_decode(v, 17579, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by pool_initialize_decode(v, 17581, 27, .SHL, none)) (by evm_ov),
    raw or
      (by pool_initialize_decode(v, 17582, 23, .OR, none)) (by evm_ov),
    raw swap1
      (by pool_initialize_decode(v, 17583, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_initialize_decode(v, 17584, 145, .SWAP2, none)) (by evm_ov)]
  exact rpost1.sstoreStatic hperm
    (by pool_initialize_decode(v, 17585, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
