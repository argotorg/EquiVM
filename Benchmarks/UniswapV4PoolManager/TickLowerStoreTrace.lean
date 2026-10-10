import Benchmarks.UniswapV4PoolManager.TickUpdateAccounts
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem tickLowerStoreStatic {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 7038) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7038⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7039⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7041⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7042⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7043⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7044⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r6 hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7045⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

def tickLowerResultMemory (mem : ByteArray) (ptr gross flipped : UInt256) : ByteArray :=
  writeWord (writeWord mem (ptr+⟨32⟩).toNat gross) ptr.toNat flipped
def tickUpperLiquidityTail (id tick packed x5 x6 x7 ptr x9 x10 : UInt256) (delta : Int)
    (R : List UInt256) : List UInt256 :=
  tickGrossWord packed :: tickSlot id (EVM.signed tick) :: packed :: x5 :: x6 :: x7 :: ptr :: x9 :: x10 ::
    tick :: EVM.wordOfInt delta :: R

theorem tickLowerStoreExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id upper gross flipped x5 x6 x7 ptr x9 x10 : UInt256}
    {lower net delta : Int} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical upper) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7038⟩
      (EVM.wordOfInt net :: tickSlot id lower :: gross :: flipped :: (poolSlot id+⟨4⟩) ::
        x5 :: x6 :: x7 :: ptr :: x9 :: x10 :: upper :: EVM.wordOfInt delta :: R)
      mem aw rdata evm.accountMap k C) :
    let post := tickLiquidityStore evm id lower gross net
    let packed := tickFieldWord post id (EVM.signed upper) .liquidityPacked
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨17774⟩
        (tickGrossWord packed :: EVM.wordOfInt delta :: ⟨7100⟩ ::
          tickUpperLiquidityTail id upper packed x5 x6 x7 ptr x9 x10 delta R)
        (twoWordHashMem upper (poolSlot id+⟨4⟩) (tickLowerResultMemory mem ptr gross flipped))
        (M (M (M (M (M aw (ptr+UInt256.ofNat 32) ⟨32⟩) ptr ⟨32⟩) ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)) rdata post.accountMap k' C' := by
  dsimp only
  by_cases hp : I.perm = false
  · rw [if_pos hp]
    exact tickLowerStoreStatic hstack hp h
  · rw [if_neg hp]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7038 hstack
      (Bool.eq_true_of_not_eq_false hp) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have ht' : UInt256.signextend (UInt256.ofNat 2) upper = upper := (signextend24_eq_iff upper).mpr ht
    have hd' : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
      signextend128_wordOfInt hd.1 hd.2
    simp only [poolManagerBlocks.poolManager_block_7038_stack, poolManagerBlocks.poolManager_block_7038_memory,
      ht', hd'] at rd1
    have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((poolSlot id+⟨4⟩).toByteArray.write 0 (upper.toByteArray.write 0
          (flipped.toByteArray.write 0 (gross.toByteArray.write 0 mem (ptr+UInt256.ofNat 32).toNat 32) ptr.toNat 32)
          (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) = tickSlot id (EVM.signed upper) := by
      change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem upper (poolSlot id+⟨4⟩)
        (tickLowerResultMemory mem ptr gross flipped)) = _
      rw [mappingMemory_slot_any]
      simp only [tickSlot, wordOfInt_signed]
    rw [hhash] at rd1
    have hσ := tickLiquidityStore_accounts hI id lower gross net
    change (tickLiquidityStore evm id lower gross net).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (tickSlot id lower) (UInt256.lor gross (UInt256.shiftLeft (EVM.wordOfInt net) (UInt256.ofNat 128))) at hσ
    rw [← hσ] at rd1
    have hI' := (tickLiquidityStore_env evm id lower gross net).trans hI
    have hload : solcSlotWordAt (tickSlot id (EVM.signed upper)) (tickLiquidityStore evm id lower gross net).accountMap I =
        tickFieldWord (tickLiquidityStore evm id lower gross net) id (EVM.signed upper) .liquidityPacked :=
      (storageLoad_codeOwner_eq_solcSlotWordAt _ I _ (by rw [hI'])).symm
    dsimp only [solcSlotWordAt, solcSlotWord] at hload
    rw [hload] at rd1
    exact ⟨k1, C1, rd1⟩

theorem tickLowerStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id upper gross flipped x5 x6 x7 ptr x9 x10 : UInt256}
    {lower net delta : Int} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical upper) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7038⟩
      (EVM.wordOfInt net :: tickSlot id lower :: gross :: flipped :: (poolSlot id+⟨4⟩) ::
        x5 :: x6 :: x7 :: ptr :: x9 :: x10 :: upper :: EVM.wordOfInt delta :: R)
      mem aw rdata evm.accountMap k C) :
    let post := tickLiquidityStore evm id lower gross net
    let packed := tickFieldWord post id (EVM.signed upper) .liquidityPacked
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨17774⟩
        (tickGrossWord packed :: EVM.wordOfInt delta :: ⟨7100⟩ ::
          tickUpperLiquidityTail id upper packed x5 x6 x7 ptr x9 x10 delta R)
        (twoWordHashMem upper (poolSlot id+⟨4⟩) (tickLowerResultMemory mem ptr gross flipped))
        aw' rdata post.accountMap k' C' := by
  have hr := tickLowerStoreExactTrace v hstack hI ht hd h
  dsimp only at hr ⊢
  by_cases hp : I.perm = false
  · simpa only [if_pos hp] using hr
  · rw [if_neg hp] at hr ⊢
    obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
