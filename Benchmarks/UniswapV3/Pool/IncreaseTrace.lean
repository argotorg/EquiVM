import Benchmarks.UniswapV3.Pool.IncreaseSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_020
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem increaseLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5472⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rdLoad := evm_run rd with [
    raw jumpdest (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5472⟩ : UInt256), (UInt8.ofNat 91), .JUMPDEST, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5473⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 0), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5475⟩ : UInt256), (UInt8.ofNat 128), .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ :=
    RD.sload rdLoad (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5476⟩ : UInt256), (UInt8.ofNat 84), .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rdStore := evm_run rdLoaded with [
    raw push1 (UInt256.ofNat 255) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5477⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 255), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 240) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5479⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 240), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw shl (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5481⟩ : UInt256), (UInt8.ofNat 27), .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw not (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5482⟩ : UInt256), (UInt8.ofNat 25), .NOT, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw and (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5483⟩ : UInt256), (UInt8.ofNat 22), .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw swap1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5484⟩ : UInt256), (UInt8.ofNat 144), .SWAP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  exact rdStore.sstoreStatic hperm (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨5485⟩ : UInt256), (UInt8.ofNat 85), .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)


theorem increaseReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5404⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨5472⟩ R mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) =
      slot0FieldWord 30 1 σ ee := (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_5404_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hlocked) rd
    exact Or.inl ⟨uniswapV3Pool_block_5422 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_5404_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩



theorem increaseLockDelegateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5472⟩ R mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ee.codeOwner ≠ v.original) ∨
      (ee.codeOwner = v.original ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨5493⟩ R mem aw rdata
          (storeSlot0Unlocked evm false).accountMap k' C') := by
  obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_5472 (immWords := wordsOf (immStore v))
    (by omega) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hmap := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm false).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) at hmap
  simp only [uniswapV3Pool_block_5472_stack, ← hmap] at rdCall
  exact noDelegateCallX (v := v) rdCall
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) hov

theorem increaseGrowEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw next : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5493⟩ (next :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16053⟩
      (next :: slot0FieldWord 27 2 σ ee :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ ::
        slot0FieldWord 27 2 σ ee :: next :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_5493 (immWords := wordsOf (immStore v))
    hov (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : UInt256.land (UInt256.ofNat 65535)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))) =
      slot0FieldWord 27 2 σ ee := slot0CardinalityNext_evm σ ee
  simp only [uniswapV3Pool_block_5493_stack, hf] at rdCall
  exact ⟨_, _, rdCall⟩

theorem increaseUnlockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw result current next : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5630⟩
      (result :: current :: next :: ⟨857⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hov : R.length + 6 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap ByteArray.empty := by
  obtain ⟨_, _, rdStop⟩ := uniswapV3Pool_block_5630 (immWords := wordsOf (immStore v))
    hov hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_5630_stack, ← hmap] at rdStop
  exact uniswapV3Pool_block_857 (immWords := wordsOf (immStore v)) (by omega) rdStop

theorem increaseFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw result current next junk : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5521⟩
      (result :: junk :: current :: next :: ⟨857⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hcurrent : current.toNat < 2 ^ 16) (hresult : result.toNat < 2 ^ 16)
    (hov : R.length + 12 ≤ 1024) :
    RDret (deployedRuntime v) g s0
      (storeSlot0Unlocked (storeSlot0CardinalityNext evm result) true).accountMap
      ByteArray.empty := by
  have hc : UInt256.land current (UInt256.ofNat 65535) = current := by
    rw [u256_land_comm]; exact uint16Word_clean hcurrent
  have hr : UInt256.land result (UInt256.ofNat 65535) = result := by
    rw [u256_land_comm]; exact uint16Word_clean hresult
  have hmap := storeSlot0CardinalityNext_accountMap evm result
  rw [← hs.accounts, hs.env] at hmap
  change (storeSlot0CardinalityNext evm result).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.land
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 216))))
        (UInt256.mul result (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)))) at hmap
  have hs' : SourceState s0 ee (storeSlot0CardinalityNext evm result).accountMap
      (storeSlot0CardinalityNext evm result) :=
    ⟨(storeSlot0CardinalityNext_originalAccounts evm result).trans hs.world,
      (storeSlot0CardinalityNext_executionEnv evm result).trans hs.env, rfl⟩
  by_cases heq : current = result
  · obtain ⟨_, _, rdUnlock⟩ := uniswapV3Pool_block_5521_taken
      (immWords := wordsOf (immStore v)) (by evm_ov) hperm
      (by rw [hc, hr, heq, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_5521_taken_stack, hr, ← hmap] at rdUnlock
    exact increaseUnlockX (v := v) rdUnlock hs' hperm (by omega)
  · obtain ⟨_, _, rdEmit⟩ := uniswapV3Pool_block_5521_fallthrough
      (immWords := wordsOf (immStore v)) (by evm_ov) hperm
      (by rw [hc, hr]; exact u256_eq_of_ne heq) rd
    simp only [uniswapV3Pool_block_5521_fallthrough_stack, hr, ← hmap] at rdEmit
    have rdUnlock := uniswapV3Pool_block_5566 (immWords := wordsOf (immStore v))
      (by evm_ov) hperm rdEmit
    exact increaseUnlockX (v := v) rdUnlock hs' hperm (by omega)

end Benchmarks.UniswapV3.Pool
