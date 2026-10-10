import Benchmarks.UniswapV4PoolManager.CurrencyReservesSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

open poolManagerBlocks in
theorem settleResetStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length+7 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 ⟨13502⟩ (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C) :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨13502⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨13503⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨13504⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨13505⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact tstoreStatic (h := r4) hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨13538⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.UniswapV4PoolManager
