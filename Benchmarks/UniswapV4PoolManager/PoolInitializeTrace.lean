import Benchmarks.UniswapV4PoolManager.PoolInitializePacking
import Benchmarks.UniswapV4PoolManager.TickPriceTrace
import Benchmarks.UniswapV4PoolManager.TickPriceCanonical
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_014
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem poolInitializeStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 ⟨4418⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)
      mem aw rdata σ k C) : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4418⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4419⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4420⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4422⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4423⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup11 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4424⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 24519927192352584402830634230720114221616806299005091840) (width := 23) (op := .PUSH23) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4425⟩ : UInt256), UInt8.ofNat 118, .Push .PUSH23, some ((UInt256.ofNat 24519927192352584402830634230720114221616806299005091840), 23), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4449⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4450⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4451⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4452⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4453⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4454⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4455⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r14 hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨4456⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

def poolInitializeTickTail (slot fee id currency1Ptr feePtr hooksPtr keyPtr price spacingPtr : UInt256)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040 :: slot :: fee ::
    UInt256.ofNat 160 :: UInt256.ofNat 100085580808691389569162032148122597711910207533909161009197301988533323260984 ::
    id :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr :: price :: spacingPtr :: UInt256.ofNat 32 :: R

theorem poolInitializeTickTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price slot id currency1Ptr feePtr hooksPtr keyPtr spacingPtr fee : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 35 ≤ 1024) (hp : price.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨4341⟩
      (price :: slot :: id :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr :: price :: spacingPtr :: fee :: R)
      mem aw rdata σ k C) :
    (tickPriceResult price = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ tick k' C', tickPriceResult price = some tick ∧ int24Canonical tick ∧
      RD (deployedRuntime v) I g s0 ⟨4418⟩
        (tick :: poolInitializeTickTail slot fee id currency1Ptr feePtr hooksPtr keyPtr price spacingPtr R)
        mem aw rdata σ k' C') := by
  have rd1 := poolManagerBlocks.poolManager_block_4341 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_4341_stack] at rd1
  rcases tickPriceTrace v (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) hp rd1 with
    ⟨hr, hrev⟩ | ⟨tick, k2, C2, hr, rd2⟩
  · exact .inl ⟨hr, hrev⟩
  · exact .inr ⟨tick, k2, C2, hr, tickPriceResult_canonical hr, rd2⟩

def initializeEventMemory (mem : ByteArray) (feePtr hooksPtr spacingPtr price tick : UInt256) : ByteArray :=
  poolManagerBlocks.poolManager_block_4418_memory (mem := mem) (x0 := tick) (x8 := feePtr)
    (x9 := hooksPtr) (x11 := price) (x12 := spacingPtr) (x13 := UInt256.ofNat 32)

theorem poolInitializeStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw price tick id currency1Ptr feePtr hooksPtr keyPtr spacingPtr fee : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 17 ≤ 1024) (hI : evm.executionEnv = I)
    (hp : price.toNat < 2^160) (hf : fee.toNat < 2^24) (ht : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨4418⟩
      (tick :: poolInitializeTickTail (poolSlot id) fee id currency1Ptr feePtr hooksPtr keyPtr price spacingPtr R)
      mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4555⟩
      (memLoad hooksPtr (initializeEventMemory mem feePtr hooksPtr spacingPtr price tick) ::
        keyPtr :: price :: tick :: UInt256.ofNat 32 :: R)
      (initializeEventMemory mem feePtr hooksPtr spacingPtr price tick) aw' rdata
      (poolInitializePost evm id price tick fee).accountMap k' C' := by
  by_cases hperm : I.perm = false
  · simp only [if_pos hperm]
    exact poolInitializeStaticTrace hstack hperm h
  · simp only [if_neg hperm]
    obtain ⟨aw1, k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_4418_packed hstack
      (Bool.eq_true_of_not_eq_false hperm) h
    rw [poolInitializeWord_compiled hp hf] at rd1
    have hs : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).2 ht
    simp only [poolManagerBlocks.poolManager_block_4418_stack, hs] at rd1
    have hm : (poolInitializePost evm id price tick fee).accountMap =
        sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id) (poolInitializeWord price tick fee) := by
      rw [poolInitializePost, storageStore_accountMap, hI]
    rw [hm]
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [initializeEventMemory, poolManagerBlocks.poolManager_block_4418_memory, hs] using rd1

end Benchmarks.UniswapV4PoolManager
