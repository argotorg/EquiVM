import Benchmarks.UniswapV4PoolManager.CurrencyReservesSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem syncZeroStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length+3 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 ⟨2747⟩ (x0 :: x1 :: R) mem aw rdata σ k C) :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2747⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2748⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2749⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2750⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact tstoreStatic (h := r4) hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2783⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

open poolManagerBlocks in
theorem syncReservesStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length+3 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 ⟨2794⟩ (x0 :: x1 :: R) mem aw rdata σ k C) :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2794⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2795⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2796⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 18037029214425852597980496522548842536420057720408124260691716999909707453369), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact tstoreStatic (h := r3) hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2829⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem syncZeroStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+3 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨2747⟩ (x0 :: x1 :: R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0
    else RDret (deployedRuntime v) g s0 (resetCurrencyPost evm).accountMap .empty := by
  cases hp : I.perm with
  | false => exact syncZeroStaticTrace hstack hp h
  | true =>
    simp only [hp, Bool.true_eq_false, if_false]
    simpa only [resetCurrencyPost, transientStore_accountMap, hI] using
      poolManagerBlocks.poolManager_block_2747 (by omega) hp h

theorem syncReservesStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw value : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+3 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨2794⟩ (value :: accountWord currency :: R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0
    else RDret (deployedRuntime v) g s0 (syncReservesPost evm currency value).accountMap .empty := by
  cases hp : I.perm with
  | false => exact syncReservesStaticTrace hstack hp h
  | true =>
    simp only [hp, Bool.true_eq_false, if_false]
    simpa only [syncReservesPost, syncReservesCurrencyPost, transientStore_accountMap, hI] using
      poolManagerBlocks.poolManager_block_2794 hstack hp h

end Benchmarks.UniswapV4PoolManager
