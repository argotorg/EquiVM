import Benchmarks.UniswapV3.Pool.OracleObservationRead
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_069
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_070

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleReadStart (second : Bool) : Nat := if second then 20610 else 20474

macro "oracle_read_at_decode" "(" v:term "," siteProof:ident "," off:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic|
    (rcases ($siteProof) with hsite | hsite | hsite <;>
      (conv_lhs => arg 2; rw [hsite]) <;> first
      | immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
          (UInt256.ofNat (20474 + $off)), (UInt8.ofNat $byte), $instr, $arg,
          immutableLayout_inBounds, immutableTemplate_size64)
      | immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
          (UInt256.ofNat (20610 + $off)), (UInt8.ofNat $byte), $instr, $arg,
          immutableLayout_inBounds, immutableTemplate_size64)
      | immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
          (UInt256.ofNat (18869 + $off)), (UInt8.ofNat $byte), $instr, $arg,
          immutableLayout_inBounds, immutableTemplate_size64)))

def oracleReadHeadAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  expandedWords (expandedWords (expandedWords (expandedWords (expandedWords aw (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
    (loadedWord mem (UInt256.ofNat 64)) ⟨32⟩)
    (loadedWord mem (UInt256.ofNat 64) + UInt256.ofNat 32) ⟨32⟩)
    (loadedWord mem (UInt256.ofNat 64) + UInt256.ofNat 64) ⟨32⟩

-- The three identical observation reads retain their memory expansion and positive gas cost.
-- The existing block summaries hide the cost across SLOAD, so this shared helper uses sloadMono.
set_option maxHeartbeats 400000 in
theorem oracleReadHeadAtMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw index base : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (start : Nat)
    (hstart : start = 20474 ∨ start = 20610 ∨ start = 18869)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat start)
      (index :: base :: R) mem aw rdata σ k C) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat (start + 86))
        (uniswapV3Pool_block_20474_stack (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base) (R := R))
        (uniswapV3Pool_block_20474_memory (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base))
        (oracleReadHeadAw mem aw) rdata σ k' C' := by
  have rdPre := evm_run rd with [
    raw jumpdest
      (by oracle_read_at_decode(v, hstart, 0, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 64)
      (by oracle_read_at_decode(v, hstart, 1, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw dup1
      (by oracle_read_at_decode(v, hstart, 3, 128, .DUP1, none)) (by evm_ov),
    raw mloadSymbolic
      (by oracle_read_at_decode(v, hstart, 4, 81, .MLOAD, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by oracle_read_at_decode(v, hstart, 5, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw dup2
      (by oracle_read_at_decode(v, hstart, 7, 129, .DUP2, none)) (by evm_ov),
    raw add
      (by oracle_read_at_decode(v, hstart, 8, 1, .ADD, none)) (by evm_ov),
    raw dup3
      (by oracle_read_at_decode(v, hstart, 9, 130, .DUP3, none)) (by evm_ov),
    raw mstoreSymbolic
      (by oracle_read_at_decode(v, hstart, 10, 82, .MSTORE, none)) (by evm_ov),
    raw swap3
      (by oracle_read_at_decode(v, hstart, 11, 146, .SWAP3, none)) (by evm_ov),
    raw swap1
      (by oracle_read_at_decode(v, hstart, 12, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by oracle_read_at_decode(v, hstart, 13, 145, .SWAP2, none)) (by evm_ov),
    raw add
      (by oracle_read_at_decode(v, hstart, 14, 1, .ADD, none)) (by evm_ov)]
  obtain ⟨kL, CL, hmono, rdLoaded⟩ := RD.sloadMono rdPre
    (by oracle_read_at_decode(v, hstart, 15, 84, .SLOAD, none)) (by evm_ov)
  have rdPart0 := evm_run rdLoaded with [
    raw push4 (UInt256.ofNat 4294967295)
      (by oracle_read_at_decode(v, hstart, 16, 99, .Push .PUSH4, some (UInt256.ofNat 4294967295, 4))) (by evm_ov),
    raw dup2
      (by oracle_read_at_decode(v, hstart, 21, 129, .DUP2, none)) (by evm_ov),
    raw and
      (by oracle_read_at_decode(v, hstart, 22, 22, .AND, none)) (by evm_ov),
    raw dup4
      (by oracle_read_at_decode(v, hstart, 23, 131, .DUP4, none)) (by evm_ov),
    raw mstoreSymbolic
      (by oracle_read_at_decode(v, hstart, 24, 82, .MSTORE, none)) (by evm_ov)]
  have rdPart1 := evm_run rdPart0 with [
    raw pushConst (UInt256.ofNat 4294967296) (by decide : Operation.POp.PUSH5 ≠ .PUSH0)
      (by oracle_read_at_decode(v, hstart, 25, 100, .Push .PUSH5, some (UInt256.ofNat 4294967296, 5))) (by evm_ov),
    raw dup2
      (by oracle_read_at_decode(v, hstart, 31, 129, .DUP2, none)) (by evm_ov),
    raw div
      (by oracle_read_at_decode(v, hstart, 32, 4, .DIV, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 6)
      (by oracle_read_at_decode(v, hstart, 33, 96, .Push .PUSH1, some (UInt256.ofNat 6, 1))) (by evm_ov),
    raw swap1
      (by oracle_read_at_decode(v, hstart, 35, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by oracle_read_at_decode(v, hstart, 36, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by oracle_read_at_decode(v, hstart, 37, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup2
      (by oracle_read_at_decode(v, hstart, 38, 129, .DUP2, none)) (by evm_ov),
    raw signextend
      (by oracle_read_at_decode(v, hstart, 39, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw swap1
      (by oracle_read_at_decode(v, hstart, 40, 144, .SWAP1, none)) (by evm_ov),
    raw signextend
      (by oracle_read_at_decode(v, hstart, 41, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by oracle_read_at_decode(v, hstart, 42, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw dup5
      (by oracle_read_at_decode(v, hstart, 44, 132, .DUP5, none)) (by evm_ov),
    raw add
      (by oracle_read_at_decode(v, hstart, 45, 1, .ADD, none)) (by evm_ov),
    raw mstoreSymbolic
      (by oracle_read_at_decode(v, hstart, 46, 82, .MSTORE, none)) (by evm_ov)]
  have rdPart2 := evm_run rdPart1 with [
    raw push1 (UInt256.ofNat 1)
      (by oracle_read_at_decode(v, hstart, 47, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by oracle_read_at_decode(v, hstart, 49, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 160)
      (by oracle_read_at_decode(v, hstart, 51, 96, .Push .PUSH1, some (UInt256.ofNat 160, 1))) (by evm_ov),
    raw shl
      (by oracle_read_at_decode(v, hstart, 53, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by oracle_read_at_decode(v, hstart, 54, 3, .SUB, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by oracle_read_at_decode(v, hstart, 55, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 88)
      (by oracle_read_at_decode(v, hstart, 57, 96, .Push .PUSH1, some (UInt256.ofNat 88, 1))) (by evm_ov),
    raw shl
      (by oracle_read_at_decode(v, hstart, 59, 27, .SHL, none)) (by evm_ov),
    raw dup3
      (by oracle_read_at_decode(v, hstart, 60, 130, .DUP3, none)) (by evm_ov),
    raw div
      (by oracle_read_at_decode(v, hstart, 61, 4, .DIV, none)) (by evm_ov),
    raw and
      (by oracle_read_at_decode(v, hstart, 62, 22, .AND, none)) (by evm_ov),
    raw swap2
      (by oracle_read_at_decode(v, hstart, 63, 145, .SWAP2, none)) (by evm_ov),
    raw dup4
      (by oracle_read_at_decode(v, hstart, 64, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by oracle_read_at_decode(v, hstart, 65, 1, .ADD, none)) (by evm_ov),
    raw swap2
      (by oracle_read_at_decode(v, hstart, 66, 145, .SWAP2, none)) (by evm_ov),
    raw swap1
      (by oracle_read_at_decode(v, hstart, 67, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by oracle_read_at_decode(v, hstart, 68, 145, .SWAP2, none)) (by evm_ov),
    raw mstoreSymbolic
      (by oracle_read_at_decode(v, hstart, 69, 82, .MSTORE, none)) (by evm_ov)]
  have rdPart3 := evm_run rdPart2 with [
    raw push1 (UInt256.ofNat 255)
      (by oracle_read_at_decode(v, hstart, 70, 96, .Push .PUSH1, some (UInt256.ofNat 255, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by oracle_read_at_decode(v, hstart, 72, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by oracle_read_at_decode(v, hstart, 74, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by oracle_read_at_decode(v, hstart, 76, 27, .SHL, none)) (by evm_ov),
    raw swap1
      (by oracle_read_at_decode(v, hstart, 77, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by oracle_read_at_decode(v, hstart, 78, 145, .SWAP2, none)) (by evm_ov),
    raw div
      (by oracle_read_at_decode(v, hstart, 79, 4, .DIV, none)) (by evm_ov),
    raw and
      (by oracle_read_at_decode(v, hstart, 80, 22, .AND, none)) (by evm_ov),
    raw iszero
      (by oracle_read_at_decode(v, hstart, 81, 21, .ISZERO, none)) (by evm_ov),
    raw iszero
      (by oracle_read_at_decode(v, hstart, 82, 21, .ISZERO, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 96)
      (by oracle_read_at_decode(v, hstart, 83, 96, .Push .PUSH1, some (UInt256.ofNat 96, 1))) (by evm_ov),
    raw dup3
      (by oracle_read_at_decode(v, hstart, 85, 130, .DUP3, none)) (by evm_ov)]
  rcases hstart with rfl | rfl | rfl <;> refine ⟨_, _, ?_, rdPart3⟩ <;>
    dsimp only [oracleReadHeadAw, expansionCost] at hmono ⊢ <;> omega

theorem oracleReadHeadMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw index base : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (oracleReadStart second))
      (index :: base :: R) mem aw rdata σ k C) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat (oracleReadStart second + 86))
        (uniswapV3Pool_block_20474_stack (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base) (R := R))
        (uniswapV3Pool_block_20474_memory (ee := ee) (mem := mem) (σ := σ)
          (x0 := index) (x1 := base))
        (oracleReadHeadAw mem aw) rdata σ k' C' := by
  exact oracleReadHeadAtMonoX (v := v) (oracleReadStart second)
    (by cases second <;> simp [oracleReadStart]) rd hov

end Benchmarks.UniswapV3.Pool
