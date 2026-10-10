import Benchmarks.UniswapV3.Pool.Common
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

local macro "pool_tick_update_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem tickUpdateOutsideStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20956⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 13 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 20956, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw dup4
      (by pool_tick_update_decode(v, 20958, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by pool_tick_update_decode(v, 20959, 1, .ADD, none)) (by evm_ov),
    raw dup12
      (by pool_tick_update_decode(v, 20960, 139, .DUP12, none)) (by evm_ov),
    raw swap1
      (by pool_tick_update_decode(v, 20961, 144, .SWAP1, none)) (by evm_ov)]
  exact r0.sstoreStatic hp (by pool_tick_update_decode(v, 20962, 85, .SSTORE, none)) (by evm_ov)

theorem tickUpdateInitializedStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21082⟩
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 7 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest
      (by pool_tick_update_decode(v, 21082, 91, .JUMPDEST, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 3)
      (by pool_tick_update_decode(v, 21083, 96, .Push .PUSH1, some (UInt256.ofNat 3, 1))) (by evm_ov),
    raw dup4
      (by pool_tick_update_decode(v, 21085, 131, .DUP4, none)) (by evm_ov),
    raw add
      (by pool_tick_update_decode(v, 21086, 1, .ADD, none)) (by evm_ov),
    raw dup1
      (by pool_tick_update_decode(v, 21087, 128, .DUP1, none)) (by evm_ov)]
  obtain ⟨_, _, r1⟩ := RD.sload r0
    (by pool_tick_update_decode(v, 21088, 84, .SLOAD, none)) (by evm_ov)
  have r2 := evm_run r1 with [
    raw pushConst (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655) (by decide : Operation.POp.PUSH31 ≠ .PUSH0)
      (by pool_tick_update_decode(v, 21089, 126, .Push .PUSH31, some (UInt256.ofNat 452312848583266388373324160190187140051835877600158453279131187530910662655, 31))) (by evm_ov),
    raw and
      (by pool_tick_update_decode(v, 21121, 22, .AND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 21122, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 248)
      (by pool_tick_update_decode(v, 21124, 96, .Push .PUSH1, some (UInt256.ofNat 248, 1))) (by evm_ov),
    raw shl
      (by pool_tick_update_decode(v, 21126, 27, .SHL, none)) (by evm_ov),
    raw or
      (by pool_tick_update_decode(v, 21127, 23, .OR, none)) (by evm_ov)]
  have r3 := evm_run r2 with [
    raw swap1
      (by pool_tick_update_decode(v, 21128, 144, .SWAP1, none)) (by evm_ov)]
  exact r3.sstoreStatic hp (by pool_tick_update_decode(v, 21129, 85, .SSTORE, none)) (by evm_ov)

theorem tickUpdateGrossStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21130⟩
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    (hp : ee.perm = false) (hov : R.length + 7 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have r0 := evm_run rd with [
    raw jumpdest
      (by pool_tick_update_decode(v, 21130, 91, .JUMPDEST, none)) (by evm_ov),
    raw dup3
      (by pool_tick_update_decode(v, 21131, 130, .DUP3, none)) (by evm_ov)]
  obtain ⟨_, _, r1⟩ := RD.sload r0
    (by pool_tick_update_decode(v, 21132, 84, .SLOAD, none)) (by evm_ov)
  have r2 := evm_run r1 with [
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 21133, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 21135, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_tick_update_decode(v, 21137, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw shl
      (by pool_tick_update_decode(v, 21139, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by pool_tick_update_decode(v, 21140, 3, .SUB, none)) (by evm_ov),
    raw not
      (by pool_tick_update_decode(v, 21141, 25, .NOT, none)) (by evm_ov)]
  have r3 := evm_run r2 with [
    raw and
      (by pool_tick_update_decode(v, 21142, 22, .AND, none)) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 21143, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 1)
      (by pool_tick_update_decode(v, 21145, 96, .Push .PUSH1, some (UInt256.ofNat 1, 1))) (by evm_ov),
    raw push1 (UInt256.ofNat 128)
      (by pool_tick_update_decode(v, 21147, 96, .Push .PUSH1, some (UInt256.ofNat 128, 1))) (by evm_ov),
    raw shl
      (by pool_tick_update_decode(v, 21149, 27, .SHL, none)) (by evm_ov),
    raw sub
      (by pool_tick_update_decode(v, 21150, 3, .SUB, none)) (by evm_ov)]
  have r4 := evm_run r3 with [
    raw dup3
      (by pool_tick_update_decode(v, 21151, 130, .DUP3, none)) (by evm_ov),
    raw and
      (by pool_tick_update_decode(v, 21152, 22, .AND, none)) (by evm_ov),
    raw or
      (by pool_tick_update_decode(v, 21153, 23, .OR, none)) (by evm_ov),
    raw dup4
      (by pool_tick_update_decode(v, 21154, 131, .DUP4, none)) (by evm_ov)]
  exact r4.sstoreStatic hp (by pool_tick_update_decode(v, 21155, 85, .SSTORE, none)) (by evm_ov)

end Benchmarks.UniswapV3.Pool

