import Benchmarks.UniswapV3.Pool.OracleReadCost
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_062
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

macro "pool_oracle_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

-- These SLOAD summaries expose the gas needed for memory expansion.
theorem oracleSurroundingHeadMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw index base : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18675⟩
      (index :: base :: R) mem aw rdata σ k C) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨18761⟩
        (uniswapV3Pool_block_18675_stack (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base) (R := R))
        (uniswapV3Pool_block_18675_memory (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base))
        (oracleReadHeadAw mem aw) rdata σ k' C' := by
  have rdPre := evm_run rd with [
    raw jumpdest
      (by pool_oracle_decode(v, 18675, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 64)
      (by pool_oracle_decode(v, 18676, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 18678, 128, .DUP1, none)) (by evm_ov),
    raw mloadSymbolic
      (by pool_oracle_decode(v, 18679, 81, .MLOAD, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_oracle_decode(v, 18680, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18682, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 18683, 1, .ADD, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18684, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18685, 82, .MSTORE, none)) (by evm_ov),
    raw swap2
      (by pool_oracle_decode(v, 18686, 145, .SWAP2, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18687, 144, .SWAP1, none)) (by evm_ov),
    raw swap3
      (by pool_oracle_decode(v, 18688, 146, .SWAP3, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 18689, 1, .ADD, none)) (by evm_ov)]
  obtain ⟨kL, CL, hmono, rdLoaded⟩ := RD.sloadMono rdPre
    (by pool_oracle_decode(v, 18690, 84, .SLOAD, none)) (by evm_ov)
  have rdPart0 := evm_run rdLoaded with [
    raw push4 (UInt256.ofNat 4294967295)
      (by pool_oracle_decode(v, 18691, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18696, 129, .DUP2, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 18697, 22, .AND, none)) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 18698, 128, .DUP1, none)) (by evm_ov),
    raw dup4
      (by pool_oracle_decode(v, 18699, 131, .DUP4, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18700, 82, .MSTORE, none)) (by evm_ov),
    raw pushConst (UInt256.ofNat 4294967296) (by decide : Operation.POp.PUSH5 ≠ .PUSH0)
      (by pool_oracle_decode(v, 18701, 100, .Push .PUSH5, some (UInt256.ofNat 4294967296, 5))) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18707, 130, .DUP3, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 18708, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 6)
      (by pool_oracle_decode(v, 18709, 96, .Push .PUSH1, some (UInt256.ofNat 6, 1))) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18711, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18712, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 18713, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18714, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 18715, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18716, 144, .SWAP1, none)) (by evm_ov)]
  have rdPart1 := evm_run rdPart0 with [
    raw signextend
      (by pool_oracle_decode(v, 18717, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by pool_oracle_decode(v, 18718, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw dup5
      (by pool_oracle_decode(v, 18720, 132, .DUP5, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 18721, 1, .ADD, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18722, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 18723, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 88)
      (by pool_oracle_decode(v, 18725, 96, .Push .PUSH1, some (UInt256.ofNat 88, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 18727, 27, .SHL, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18728, 130, .DUP3, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 18729, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 18730, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 18732, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 160)
      (by pool_oracle_decode(v, 18734, 96, .Push .PUSH1, some (UInt256.ofNat 160, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 18736, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by pool_oracle_decode(v, 18737, 3, .SUB, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 18738, 22, .AND, none)) (by evm_ov)]
  have rdPart2 := evm_run rdPart1 with [
    raw swap4
      (by pool_oracle_decode(v, 18739, 147, .SWAP4, none)) (by evm_ov),
    raw dup4
      (by pool_oracle_decode(v, 18740, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 18741, 1, .ADD, none)) (by evm_ov),
    raw swap4
      (by pool_oracle_decode(v, 18742, 147, .SWAP4, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18743, 144, .SWAP1, none)) (by evm_ov),
    raw swap4
      (by pool_oracle_decode(v, 18744, 147, .SWAP4, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18745, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 18746, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by pool_oracle_decode(v, 18748, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 18750, 27, .SHL, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18751, 144, .SWAP1, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 18752, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 255)
      (by pool_oracle_decode(v, 18753, 96, .Push .PUSH1, some (UInt256.ofNat 255, 1))) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 18755, 22, .AND, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 18756, 21, .ISZERO, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 18757, 21, .ISZERO, none)) (by evm_ov)]
  have rdPart3 := evm_run rdPart2 with [
    raw push1 (UInt256.ofNat 96)
      (by pool_oracle_decode(v, 18758, 96, .Push .PUSH1, some (UInt256.ofNat 96, 1))) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18760, 130, .DUP3, none)) (by evm_ov)]
  refine ⟨_, _, ?_, rdPart3⟩
  dsimp only [oracleReadHeadAw, M, expandedWords, expansionCost] at hmono ⊢
  omega

theorem oracleSurroundingFallbackMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18966⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) :
    let aw' := M (oracleReadHeadAw mem aw) (loadedWord mem (UInt256.ofNat 64) + UInt256.ofNat 96) ⟨32⟩
    ∃ k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨19052⟩
        (uniswapV3Pool_block_18966_stack (mem := mem) (x0 := x0) (x2 := x2)
          (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R))
        (uniswapV3Pool_block_18966_memory (ee := ee) (mem := mem) (σ := σ) (x8 := x8))
        aw' rdata σ k' C' := by
  dsimp only
  have rdPre := evm_run rd with [
    raw push1 (UInt256.ofNat 64)
      (by pool_oracle_decode(v, 18966, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup1
      (by pool_oracle_decode(v, 18968, 128, .DUP1, none)) (by evm_ov),
    raw mloadSymbolic
      (by pool_oracle_decode(v, 18969, 81, .MLOAD, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_oracle_decode(v, 18970, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18972, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 18973, 1, .ADD, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18974, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18975, 82, .MSTORE, none)) (by evm_ov),
    raw dup11
      (by pool_oracle_decode(v, 18976, 138, .DUP11, none)) (by evm_ov)]
  obtain ⟨kL, CL, hmono, rdLoaded⟩ := RD.sloadMono rdPre
    (by pool_oracle_decode(v, 18977, 84, .SLOAD, none)) (by evm_ov)
  have rdPart0 := evm_run rdLoaded with [
    raw push4 (UInt256.ofNat 4294967295)
      (by pool_oracle_decode(v, 18978, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18983, 129, .DUP2, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 18984, 22, .AND, none)) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 18985, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 18986, 82, .MSTORE, none)) (by evm_ov),
    raw pushConst (UInt256.ofNat 4294967296) (by decide : Operation.POp.PUSH5 ≠ .PUSH0)
      (by pool_oracle_decode(v, 18987, 100, .Push .PUSH5, some (UInt256.ofNat 4294967296, 5))) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18993, 129, .DUP2, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 18994, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 6)
      (by pool_oracle_decode(v, 18995, 96, .Push .PUSH1, some (UInt256.ofNat 6, 1))) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 18997, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 18998, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 18999, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 19000, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 19001, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 19002, 144, .SWAP1, none)) (by evm_ov),
    raw signextend
      (by pool_oracle_decode(v, 19003, 11, .SIGNEXTEND, none)) (by evm_ov)]
  have rdPart1 := evm_run rdPart0 with [
    raw push1 (UInt256.ofNat 32)
      (by pool_oracle_decode(v, 19004, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw dup4
      (by pool_oracle_decode(v, 19006, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 19007, 1, .ADD, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 19008, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 19009, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 88)
      (by pool_oracle_decode(v, 19011, 96, .Push .PUSH1, some (UInt256.ofNat 88, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 19013, 27, .SHL, none)) (by evm_ov),
    raw dup2
      (by pool_oracle_decode(v, 19014, 129, .DUP2, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 19015, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 19016, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 19018, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 160)
      (by pool_oracle_decode(v, 19020, 96, .Push .PUSH1, some (UInt256.ofNat 160, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 19022, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by pool_oracle_decode(v, 19023, 3, .SUB, none)) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 19024, 22, .AND, none)) (by evm_ov),
    raw swap3
      (by pool_oracle_decode(v, 19025, 146, .SWAP3, none)) (by evm_ov)]
  have rdPart2 := evm_run rdPart1 with [
    raw dup3
      (by pool_oracle_decode(v, 19026, 130, .DUP3, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 19027, 1, .ADD, none)) (by evm_ov),
    raw swap3
      (by pool_oracle_decode(v, 19028, 146, .SWAP3, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 19029, 144, .SWAP1, none)) (by evm_ov),
    raw swap3
      (by pool_oracle_decode(v, 19030, 146, .SWAP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 19031, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_oracle_decode(v, 19032, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by pool_oracle_decode(v, 19034, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by pool_oracle_decode(v, 19036, 27, .SHL, none)) (by evm_ov),
    raw swap1
      (by pool_oracle_decode(v, 19037, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_oracle_decode(v, 19038, 145, .SWAP2, none)) (by evm_ov),
    raw div
      (by pool_oracle_decode(v, 19039, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 255)
      (by pool_oracle_decode(v, 19040, 96, .Push .PUSH1, some (UInt256.ofNat 255, 1))) (by evm_ov),
    raw and
      (by pool_oracle_decode(v, 19042, 22, .AND, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 19043, 21, .ISZERO, none)) (by evm_ov),
    raw iszero
      (by pool_oracle_decode(v, 19044, 21, .ISZERO, none)) (by evm_ov)]
  have rdPart3 := evm_run rdPart2 with [
    raw push1 (UInt256.ofNat 96)
      (by pool_oracle_decode(v, 19045, 96, .Push .PUSH1, some (UInt256.ofNat 96, 1))) (by evm_ov),
    raw dup3
      (by pool_oracle_decode(v, 19047, 130, .DUP3, none)) (by evm_ov),
    raw add
      (by pool_oracle_decode(v, 19048, 1, .ADD, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_oracle_decode(v, 19049, 82, .MSTORE, none)) (by evm_ov),
    raw swap2
      (by pool_oracle_decode(v, 19050, 145, .SWAP2, none)) (by evm_ov),
    raw pop
      (by pool_oracle_decode(v, 19051, 80, .POP, none)) (by evm_ov)]
  refine ⟨_, _, ?_, rdPart3⟩
  dsimp only [oracleReadHeadAw, M, expandedWords, expansionCost] at hmono ⊢
  omega

end Benchmarks.UniswapV3.Pool
