import Benchmarks.UniswapV3.Pool.PositionGet
import Benchmarks.UniswapV3.Pool.CollectPaymentsSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7626⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rdLoad := evm_run rd with [
    raw jumpdest (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7626⟩ : UInt256), (UInt8.ofNat 91), .JUMPDEST, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7627⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 0), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7629⟩ : UInt256), (UInt8.ofNat 128), .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ :=
    RD.sload rdLoad (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7630⟩ : UInt256), (UInt8.ofNat 84), .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rdStore := evm_run rdLoaded with [
    raw push1 (UInt256.ofNat 255) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7631⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 255), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 240) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7633⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 240), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw shl (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7635⟩ : UInt256), (UInt8.ofNat 27), .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw not (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7636⟩ : UInt256), (UInt8.ofNat 25), .NOT, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw and (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7637⟩ : UInt256), (UInt8.ofNat 22), .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup2 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7638⟩ : UInt256), (UInt8.ofNat 129), .DUP2, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  exact rdStore.sstoreStatic hperm (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨7639⟩ : UInt256), (UInt8.ofNat 85), .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)


theorem collectReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7555⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7626⟩ (⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) =
      slot0FieldWord 30 1 σ ee := (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_7555_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hlocked) rd
    simp only [uniswapV3Pool_block_7555_fallthrough_stack] at rdFail
    exact Or.inl ⟨uniswapV3Pool_block_7576 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_7555_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩


theorem collectPositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p lower upper req0 req1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7626⟩
      (⟨0⟩ :: ⟨0⟩ :: req1 :: req0 :: positionTickWord upper :: positionTickWord lower :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 87 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨7652⟩
      (solcMappingSlot ⟨7⟩ (positionKey ee.source lower upper) :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        req1 :: req0 :: positionTickWord upper :: positionTickWord lower :: R)
      (positionGetMem mem p ee.source lower upper ⟨7⟩) aw' rdata
      (storeSlot0Unlocked evm false).accountMap k' C' ∧
      HeapMemory (positionGetMem mem p ee.source lower upper ⟨7⟩) aw' (p + ⟨58⟩) := by
  obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_7626 (immWords := wordsOf (immStore v))
    (by omega) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hmap := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm false).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) at hmap
  simp only [uniswapV3Pool_block_7626_stack, ← hmap] at rdCall
  obtain ⟨aw', k', C', rdPosition, hmPosition⟩ := positionGetX (v := v) ee.source rdCall hm hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  have hkey : positionKey ee.source (positionTickWord lower) (positionTickWord upper) =
      positionKey ee.source lower upper := by
    simp only [positionKey, positionPackedBytes, positionTickWord_idem]
  have hmem : positionGetMem mem p ee.source (positionTickWord lower) (positionTickWord upper) (UInt256.ofNat 7) =
      positionGetMem mem p ee.source lower upper ⟨7⟩ := by
    simp only [positionGetMem, hkey, positionBuildMem, positionDataMem, positionTickWord_idem]
    rfl
  rw [hkey, hmem] at rdPosition
  rw [hmem] at hmPosition
  exact ⟨_, _, _, rdPosition, hmPosition⟩

end Benchmarks.UniswapV3.Pool
