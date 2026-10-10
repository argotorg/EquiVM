import Benchmarks.UniswapV3.Pool.OracleSurroundingReadCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- The observeSingle read retains an extra timestamp mask on its stack.
-- Its SLOAD summary hides the expansion cost needed by the caller's loop invariant.
theorem observationReadHeadMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw index base : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13226⟩
      (index :: base :: R) mem aw rdata σ k C) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13311⟩
        (uniswapV3Pool_block_13226_stack (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base) (R := R))
        (uniswapV3Pool_block_13226_memory (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base))
        (oracleReadHeadAw mem aw) rdata σ k' C' := by
  have rdPre := evm_run rd with [
    raw jumpdest
      (by pool_oracle_decode(v, 13226, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 64)
      (by pool_oracle_decode(v, 13227, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 13229, 128, .DUP1, none)) (by evm_ov),
    raw mloadSymbolic
      (by pool_oracle_decode(v, 13230, 81, .MLOAD, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_oracle_decode(v, 13231, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 13233, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 13234, 1, .ADD, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 13235, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 13236, 82, .MSTORE, none)) (by evm_ov),
    raw swap2
      (by pool_oracle_decode(v, 13237, 145, .SWAP2, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 13238, 144, .SWAP1, none)) (by evm_ov),
    raw swap3
      (by pool_oracle_decode(v, 13239, 146, .SWAP3, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 13240, 1, .ADD, none)) (by evm_ov)]
  obtain ⟨kL, CL, hmono, rdLoaded⟩ := RD.sloadMono rdPre
    (by pool_oracle_decode(v, 13241, 84, .SLOAD, none)) (by evm_ov)
  have rdPart0 := evm_run rdLoaded with [
    raw push4 (UInt256.ofNat 4294967295)
      (by pool_oracle_decode(v, 13242, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 13247, 128, .DUP1, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 13248, 130, .DUP3, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 13249, 22, .AND, none)) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 13250, 128, .DUP1, none)) (by evm_ov),
    raw dup5
      (by pool_oracle_decode(v, 13251, 132, .DUP5, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 13252, 82, .MSTORE, none)) (by evm_ov),
    raw pushConst (UInt256.ofNat 4294967296) (by decide : Operation.POp.PUSH5 ≠ .PUSH0)
      (by pool_oracle_decode(v, 13253, 100, .Push .PUSH5, some (UInt256.ofNat 4294967296, 5))) (by evm_ov),
    raw dup4
      (by pool_oracle_decode(v, 13259, 131, .DUP4, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 13260, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 6)
      (by pool_oracle_decode(v, 13261, 96, .Push .PUSH1, some (UInt256.ofNat 6, 1))) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 13263, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 13264, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 13265, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 13266, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 13267, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 13268, 144, .SWAP1, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 13269, 11, .SIGNEXTEND, none)) (by evm_ov)]
  have rdPart1 := evm_run rdPart0 with [
    raw push1 (UInt256.ofNat 32)
      (by pool_oracle_decode(v, 13270, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw dup6
      (by pool_oracle_decode(v, 13272, 133, .DUP6, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 13273, 1, .ADD, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 13274, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 13275, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 88)
      (by pool_oracle_decode(v, 13277, 96, .Push .PUSH1, some (UInt256.ofNat 88, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 13279, 27, .SHL, none)) (by evm_ov),
    raw dup4
      (by pool_oracle_decode(v, 13280, 131, .DUP4, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 13281, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 13282, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 13284, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 160)
      (by pool_oracle_decode(v, 13286, 96, .Push .PUSH1, some (UInt256.ofNat 160, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 13288, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by pool_oracle_decode(v, 13289, 3, .SUB, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 13290, 22, .AND, none)) (by evm_ov),
    raw swap5
      (by pool_oracle_decode(v, 13291, 148, .SWAP5, none)) (by evm_ov),
    raw dup5
      (by pool_oracle_decode(v, 13292, 132, .DUP5, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 13293, 1, .ADD, none)) (by evm_ov),
    raw swap5
      (by pool_oracle_decode(v, 13294, 148, .SWAP5, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 13295, 144, .SWAP1, none)) (by evm_ov),
    raw swap5
      (by pool_oracle_decode(v, 13296, 148, .SWAP5, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 13297, 82, .MSTORE, none)) (by evm_ov)]
  have rdPart2 := evm_run rdPart1 with [
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 13298, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by pool_oracle_decode(v, 13300, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 13302, 27, .SHL, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 13303, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_oracle_decode(v, 13304, 145, .SWAP2, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 13305, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 255)
      (by pool_oracle_decode(v, 13306, 96, .Push .PUSH1, some (UInt256.ofNat 255, 1))) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 13308, 22, .AND, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 13309, 21, .ISZERO, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 13310, 21, .ISZERO, none)) (by evm_ov)]
  refine ⟨_, _, ?_, rdPart2⟩
  dsimp only [oracleReadHeadAw, M, expandedWords, expansionCost] at hmono ⊢
  omega

end Benchmarks.UniswapV3.Pool
