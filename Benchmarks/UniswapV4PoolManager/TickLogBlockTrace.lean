import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_051
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickLogBlock18089 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18089⟩ (r0 :: R) mem aw rdata σ k C) :
    let r1 := tickLogNext r0 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18108⟩
      ((UInt256.mul r1 r1) :: (tickLogSquare r1) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: R) mem aw rdata σ k' C' := by
  let r1 := tickLogNext r0 true
  have rd := poolManagerBlocks.poolManager_block_18089 hstack h
  simp only [poolManagerBlocks.poolManager_block_18089_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18108⟩
    ((UInt256.mul r1 r1) :: (tickLogSquare r1) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18108 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r1 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18108⟩ ((UInt256.mul r1 r1) :: (tickLogSquare r1) :: R) mem aw rdata σ k C) :
    let r2 := tickLogNext r1 true
    let r3 := tickLogNext r2 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18128⟩
      ((UInt256.ofNat 127) :: (UInt256.mul r3 r3) :: (UInt256.mul r3 r3) :: (UInt256.mul r2 r2) :: R) mem aw rdata σ k' C' := by
  let r2 := tickLogNext r1 true
  let r3 := tickLogNext r2 true
  have rd := poolManagerBlocks.poolManager_block_18108 hstack h
  simp only [poolManagerBlocks.poolManager_block_18108_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18128⟩
    ((UInt256.ofNat 127) :: (UInt256.mul r3 r3) :: (UInt256.mul r3 r3) :: (UInt256.mul r2 r2) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r3 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18128⟩ ((UInt256.ofNat 127) :: (UInt256.mul r3 r3) :: (UInt256.mul r3 r3) :: R) mem aw rdata σ k C) :
    let r4 := tickLogNext r3 true
    let r5 := tickLogNext r4 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18147⟩
      ((UInt256.mul r5 r5) :: (UInt256.mul r4 r4) :: (UInt256.mul r3 r3) :: R) mem aw rdata σ k' C' := by
  let r4 := tickLogNext r3 true
  let r5 := tickLogNext r4 true
  have rd := poolManagerBlocks.poolManager_block_18128 hstack h
  simp only [poolManagerBlocks.poolManager_block_18128_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18147⟩
    ((UInt256.mul r5 r5) :: (UInt256.mul r4 r4) :: (UInt256.mul r3 r3) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18147 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r5 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18147⟩ ((UInt256.mul r5 r5) :: R) mem aw rdata σ k C) :
    let r6 := tickLogNext r5 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18167⟩
      ((tickLogFlag r6) :: (tickLogSquare r6) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: R) mem aw rdata σ k' C' := by
  let r6 := tickLogNext r5 true
  have rd := poolManagerBlocks.poolManager_block_18147 hstack h
  simp only [poolManagerBlocks.poolManager_block_18147_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18167⟩
    ((tickLogFlag r6) :: (tickLogSquare r6) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18167 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r3 r4 r5 r6 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18167⟩ ((tickLogFlag r6) :: (tickLogSquare r6) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r4 r4) :: (UInt256.mul r3 r3) :: R) mem aw rdata σ k C) :
    let r7 := tickLogNext r6 true
    let r8 := tickLogNext r7 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18186⟩
      ((UInt256.ofNat 127) :: (UInt256.mul r8 r8) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: R) mem aw rdata σ k' C' := by
  let r7 := tickLogNext r6 true
  let r8 := tickLogNext r7 true
  have rd := poolManagerBlocks.poolManager_block_18167 hstack h
  simp only [poolManagerBlocks.poolManager_block_18167_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18186⟩
    ((UInt256.ofNat 127) :: (UInt256.mul r8 r8) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18186 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r2 r3 r4 r5 r6 r7 r8 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 11 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18186⟩ ((UInt256.ofNat 127) :: (UInt256.mul r8 r8) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r2 r2) :: R) mem aw rdata σ k C) :
    let r9 := tickLogNext r8 true
    let r10 := tickLogNext r9 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18205⟩
      (r10 :: r10 :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: R) mem aw rdata σ k' C' := by
  let r9 := tickLogNext r8 true
  let r10 := tickLogNext r9 true
  have rd := poolManagerBlocks.poolManager_block_18186 hstack h
  simp only [poolManagerBlocks.poolManager_block_18186_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18205⟩
    (r10 :: r10 :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18205 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 14 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18205⟩ (r10 :: r10 :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: R) mem aw rdata σ k C) :
    let r11 := tickLogNext r10 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18224⟩
      ((UInt256.mul r11 r11) :: (tickLogSquare r11) :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: R) mem aw rdata σ k' C' := by
  let r11 := tickLogNext r10 true
  have rd := poolManagerBlocks.poolManager_block_18205 hstack h
  simp only [poolManagerBlocks.poolManager_block_18205_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18224⟩
    ((UInt256.mul r11 r11) :: (tickLogSquare r11) :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18224 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 17 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18224⟩ ((UInt256.mul r11 r11) :: (tickLogSquare r11) :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: msb :: R) mem aw rdata σ k C) :
    let r12 := tickLogNext r11 true
    let r13 := tickLogNext r12 true
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18243⟩
      ((UInt256.mul r13 r13) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: (UInt256.mul r12 r12) :: R) mem aw rdata σ k' C' := by
  let r12 := tickLogNext r11 true
  let r13 := tickLogNext r12 true
  have rd := poolManagerBlocks.poolManager_block_18224 hstack h
  simp only [poolManagerBlocks.poolManager_block_18224_stack, ← tickLogFlag_compiled] at rd
  change RD (deployedRuntime v) I g s0 ⟨18243⟩
    ((UInt256.mul r13 r13) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: (UInt256.mul r12 r12) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18243 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 16 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18243⟩ ((UInt256.mul r13 r13) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: (UInt256.mul r12 r12) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18284⟩
      ((UInt256.ofNat 202) :: (UInt256.mul r10 r10) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18243 hstack h
  simp only [poolManagerBlocks.poolManager_block_18243_stack] at rd
  have hb52 := tickLogBit_compiled (bit := 52) (by decide) r11
  change UInt256.land (UInt256.ofNat 4503599627370496) (UInt256.shiftRight (UInt256.mul r11 r11) (UInt256.ofNat 203)) = _ at hb52
  rw [hb52] at rd
  have hb51 := tickLogBit_compiled (bit := 51) (by decide) r12
  change UInt256.land (UInt256.ofNat 2251799813685248) (UInt256.shiftRight (UInt256.mul r12 r12) (UInt256.ofNat 204)) = _ at hb51
  rw [hb51] at rd
  have hb50 := tickLogBit_compiled (bit := 50) (by decide) r13
  change UInt256.land (UInt256.ofNat 1125899906842624) (UInt256.shiftRight (UInt256.mul r13 r13) (UInt256.ofNat 205)) = _ at hb50
  rw [hb50] at rd
  change RD (deployedRuntime v) I g s0 ⟨18284⟩
    ((UInt256.ofNat 202) :: (UInt256.mul r10 r10) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18284 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 13 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18284⟩ ((UInt256.ofNat 202) :: (UInt256.mul r10 r10) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18324⟩
      ((UInt256.shiftRight (UInt256.mul r7 r7) (UInt256.ofNat 199)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18284 hstack h
  simp only [poolManagerBlocks.poolManager_block_18284_stack] at rd
  have hb55 := tickLogBit_compiled (bit := 55) (by decide) r8
  change UInt256.land (UInt256.ofNat 36028797018963968) (UInt256.shiftRight (UInt256.mul r8 r8) (UInt256.ofNat 200)) = _ at hb55
  rw [hb55] at rd
  have hb54 := tickLogBit_compiled (bit := 54) (by decide) r9
  change UInt256.land (UInt256.ofNat 18014398509481984) (UInt256.shiftRight (UInt256.mul r9 r9) (UInt256.ofNat 201)) = _ at hb54
  rw [hb54] at rd
  have hb53 := tickLogBit_compiled (bit := 53) (by decide) r10
  change UInt256.land (UInt256.ofNat 9007199254740992) (UInt256.shiftRight (UInt256.mul r10 r10) (UInt256.ofNat 202)) = _ at hb53
  rw [hb53] at rd
  change RD (deployedRuntime v) I g s0 ⟨18324⟩
    ((UInt256.shiftRight (UInt256.mul r7 r7) (UInt256.ofNat 199)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18324 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 10 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18324⟩ ((UInt256.shiftRight (UInt256.mul r7 r7) (UInt256.ofNat 199)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18375⟩
      ((UInt256.ofNat 576460752303423488) :: (UInt256.shiftRight (UInt256.mul r4 r4) (UInt256.ofNat 196)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58)) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18324 hstack h
  simp only [poolManagerBlocks.poolManager_block_18324_stack] at rd
  have hb58 := tickLogBit_compiled (bit := 58) (by decide) r5
  change UInt256.land (UInt256.ofNat 288230376151711744) (UInt256.shiftRight (UInt256.mul r5 r5) (UInt256.ofNat 197)) = _ at hb58
  rw [hb58] at rd
  have hb57 := tickLogBit_compiled (bit := 57) (by decide) r6
  change UInt256.land (UInt256.ofNat 144115188075855872) (UInt256.shiftRight (UInt256.mul r6 r6) (UInt256.ofNat 198)) = _ at hb57
  rw [hb57] at rd
  have hb56 := tickLogBit_compiled (bit := 56) (by decide) r7
  change UInt256.land (UInt256.ofNat 72057594037927936) (UInt256.shiftRight (UInt256.mul r7 r7) (UInt256.ofNat 199)) = _ at hb56
  rw [hb56] at rd
  change RD (deployedRuntime v) I g s0 ⟨18375⟩
    ((UInt256.ofNat 576460752303423488) :: (UInt256.shiftRight (UInt256.mul r4 r4) (UInt256.ofNat 196)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58)) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18375 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18375⟩ ((UInt256.ofNat 576460752303423488) :: (UInt256.shiftRight (UInt256.mul r4 r4) (UInt256.ofNat 196)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18418⟩
      ((UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61)) :: (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60)) :: (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59)) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18375 hstack h
  simp only [poolManagerBlocks.poolManager_block_18375_stack] at rd
  have hb62 := tickLogBit_compiled (bit := 62) (by decide) r1
  change UInt256.land (UInt256.ofNat 4611686018427387904) (UInt256.shiftRight (UInt256.mul r1 r1) (UInt256.ofNat 193)) = _ at hb62
  rw [hb62] at rd
  have hb61 := tickLogBit_compiled (bit := 61) (by decide) r2
  change UInt256.land (UInt256.ofNat 2305843009213693952) (UInt256.shiftRight (UInt256.mul r2 r2) (UInt256.ofNat 194)) = _ at hb61
  rw [hb61] at rd
  have hb60 := tickLogBit_compiled (bit := 60) (by decide) r3
  change UInt256.land (UInt256.ofNat 1152921504606846976) (UInt256.shiftRight (UInt256.mul r3 r3) (UInt256.ofNat 195)) = _ at hb60
  rw [hb60] at rd
  have hb59 := tickLogBit_compiled (bit := 59) (by decide) r4
  change UInt256.land (UInt256.ofNat 576460752303423488) (UInt256.shiftRight (UInt256.mul r4 r4) (UInt256.ofNat 196)) = _ at hb59
  rw [hb59] at rd
  change RD (deployedRuntime v) I g s0 ⟨18418⟩
    ((UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61)) :: (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60)) :: (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59)) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18418 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18418⟩ ((UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61)) :: (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60)) :: (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59)) :: (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58)) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18476⟩
      ((UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18418 hstack h
  simp only [poolManagerBlocks.poolManager_block_18418_stack] at rd
  have hb63 := tickLogBit_compiled (bit := 63) (by decide) r0
  change UInt256.land (UInt256.ofNat 9223372036854775808) (UInt256.shiftRight (UInt256.mul r0 r0) (UInt256.ofNat 192)) = _ at hb63
  rw [hb63] at rd
  have hm := tickPriceLogStart_compiled msb
  change UInt256.shiftLeft (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639808 + msb) (UInt256.ofNat 64) = _ at hm
  rw [hm] at rd
  change RD (deployedRuntime v) I g s0 ⟨18476⟩
    ((UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

theorem tickLogBlock18476 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18476⟩ ((UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18536⟩
      ((UInt256.ofNat 2) :: (UInt256.sar (UInt256.ofNat 128) ((UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) + (UInt256.ofNat 115792089237316195423570985008687907853266581672683754907038987867812469392726))) :: (UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) :: R) mem aw rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_18476 hstack h
  simp only [poolManagerBlocks.poolManager_block_18476_stack] at rd
  change RD (deployedRuntime v) I g s0 ⟨18536⟩
    ((UInt256.ofNat 2) :: (UInt256.sar (UInt256.ofNat 128) ((UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) + (UInt256.ofNat 115792089237316195423570985008687907853266581672683754907038987867812469392726))) :: (UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) :: R) mem aw rdata σ _ _ at rd
  exact ⟨_, _, rd⟩

end Benchmarks.UniswapV4PoolManager
