import Benchmarks.UniswapV4PoolManager.Common
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 4000

/-- The terminal block summary hides its counters. Retain the 23 operation gas spent
before its REVERT, so a capacity panic beyond the gas bound implies out of gas. -/
theorem allocationPanicGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+2 ≤ 1024) (hgas : g.toNat < C+23)
    (h : RD (deployedRuntime v) I g s0 ⟨7857⟩ R mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have r1 := h.jumpdest
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7857⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ (width := 32) (op := .PUSH32) (by decide)
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7858⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ : UInt256), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7891⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7892⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 ⟨65⟩
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7893⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨65⟩ : UInt256), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 ⟨4⟩
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7895⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨4⟩ : UInt256), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7897⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 ⟨36⟩
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7898⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨36⟩ : UInt256), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨7900⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.oog_of_cost_gt r9 (by omega)

end Benchmarks.UniswapV4PoolManager
