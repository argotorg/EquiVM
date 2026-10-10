import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_072

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "pool_bitmap_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem bitmapFlipStoreStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21341⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 11 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest
      (by pool_bitmap_decode(v, 21341, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_bitmap_decode(v, 21342, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw swap2
      (by pool_bitmap_decode(v, 21344, 145, .SWAP2, none)) (by evm_ov),
    raw dup3
      (by pool_bitmap_decode(v, 21345, 130, .DUP3, none)) (by evm_ov),
    raw signextend
      (by pool_bitmap_decode(v, 21346, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw dup3
      (by pool_bitmap_decode(v, 21347, 130, .DUP3, none)) (by evm_ov),
    raw signextend
      (by pool_bitmap_decode(v, 21348, 11, .SIGNEXTEND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 0)
      (by pool_bitmap_decode(v, 21349, 96, .Push .PUSH1, some (UInt256.ofNat 0, 1))) (by evm_ov)]
  have r1 := evm_run r0 with [
    raw swap1
      (by pool_bitmap_decode(v, 21351, 144, .SWAP1, none)) (by evm_ov),
    raw dup2
      (by pool_bitmap_decode(v, 21352, 129, .DUP2, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_bitmap_decode(v, 21353, 82, .MSTORE, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 32)
      (by pool_bitmap_decode(v, 21354, 96, .Push .PUSH1, some (UInt256.ofNat 32, 1))) (by evm_ov),
    raw swap8
      (by pool_bitmap_decode(v, 21356, 151, .SWAP8, none)) (by evm_ov),
    raw swap1
      (by pool_bitmap_decode(v, 21357, 144, .SWAP1, none)) (by evm_ov),
    raw swap8
      (by pool_bitmap_decode(v, 21358, 151, .SWAP8, none)) (by evm_ov),
    raw mstoreSymbolic
      (by pool_bitmap_decode(v, 21359, 82, .MSTORE, none)) (by evm_ov)]
  have r2 := evm_run r1 with [
    raw push1 (UInt256.ofNat 64)
      (by pool_bitmap_decode(v, 21360, 96, .Push .PUSH1, some (UInt256.ofNat 64, 1))) (by evm_ov),
    raw swap1
      (by pool_bitmap_decode(v, 21362, 144, .SWAP1, none)) (by evm_ov),
    raw swap7
      (by pool_bitmap_decode(v, 21363, 150, .SWAP7, none)) (by evm_ov)]
  have r3 := RD.keccak256 _ _ _ r2
    (by pool_bitmap_decode(v, 21364, 32, .KECCAK256, none)) rfl rfl rfl (by evm_ov)
  have r4 := evm_run r3 with [
    raw dup1
      (by pool_bitmap_decode(v, 21365, 128, .DUP1, none)) (by evm_ov)]
  obtain ⟨kL, CL, r5⟩ := RD.sload r4
    (by pool_bitmap_decode(v, 21366, 84, .SLOAD, none)) (by evm_ov)
  have r6 := evm_run r5 with [
    raw push1 (UInt256.ofNat 255)
      (by pool_bitmap_decode(v, 21367, 96, .Push .PUSH1, some (UInt256.ofNat 255, 1))) (by evm_ov),
    raw swap1
      (by pool_bitmap_decode(v, 21369, 144, .SWAP1, none)) (by evm_ov),
    raw swap8
      (by pool_bitmap_decode(v, 21370, 151, .SWAP8, none)) (by evm_ov),
    raw and
      (by pool_bitmap_decode(v, 21371, 22, .AND, none)) (by evm_ov),
    raw swap2
      (by pool_bitmap_decode(v, 21372, 145, .SWAP2, none)) (by evm_ov),
    raw swap1
      (by pool_bitmap_decode(v, 21373, 144, .SWAP1, none)) (by evm_ov),
    raw swap2
      (by pool_bitmap_decode(v, 21374, 145, .SWAP2, none)) (by evm_ov),
    raw shl
      (by pool_bitmap_decode(v, 21375, 27, .SHL, none)) (by evm_ov)]
  have r7 := evm_run r6 with [
    raw swap1
      (by pool_bitmap_decode(v, 21376, 144, .SWAP1, none)) (by evm_ov),
    raw swap6
      (by pool_bitmap_decode(v, 21377, 149, .SWAP6, none)) (by evm_ov),
    raw xor
      (by pool_bitmap_decode(v, 21378, 24, .XOR, none)) (by evm_ov),
    raw swap1
      (by pool_bitmap_decode(v, 21379, 144, .SWAP1, none)) (by evm_ov),
    raw swap5
      (by pool_bitmap_decode(v, 21380, 148, .SWAP5, none)) (by evm_ov)]
  exact r7.sstoreStatic hperm (by pool_bitmap_decode(v, 21381, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool
