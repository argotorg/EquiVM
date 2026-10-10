import Benchmarks.UniswapV4PoolManager.TickUpdateAccounts
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem tickUpperStoreStatic {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 7205) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7205⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7206⟩ : UInt256), UInt8.ofNat 111, .Push .PUSH16, some ((UInt256.ofNat 340282366920938463463374607431768211455), 16), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7223⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7224⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7225⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7227⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7228⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7229⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7230⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7231⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7232⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r11 hperm (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨7233⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

def tickUpperResultMemory (mem : ByteArray) (ptr gross flipped : UInt256) : ByteArray :=
  writeWord (writeWord mem (ptr+⟨96⟩).toNat gross) (ptr+⟨64⟩).toNat flipped

theorem tickUpperStoreExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id gross flipped x4 x5 x6 ptr x8 x9 x10 : UInt256}
    {tick net delta : Int} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (hg : gross.toNat < 2^128) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7205⟩
      (tickSlot id tick :: gross :: EVM.wordOfInt net :: flipped :: x4 :: x5 :: x6 :: ptr :: x8 :: x9 :: x10 ::
        EVM.wordOfInt delta :: R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
      RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
        (x4 :: x5 :: x6 :: ptr :: x8 :: x9 :: x10 :: EVM.wordOfInt delta :: R)
        (tickUpperResultMemory mem ptr gross flipped) (M (M aw (ptr+UInt256.ofNat 96) ⟨32⟩) (ptr+UInt256.ofNat 64) ⟨32⟩) rdata (tickLiquidityStore evm id tick gross net).accountMap k' C' := by
  by_cases hp : I.perm = false
  · rw [if_pos hp]
    exact tickUpperStoreStatic hstack hp h
  · rw [if_neg hp]
    have hd' : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
      signextend128_wordOfInt hd.1 hd.2
    have hcond : UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta)) ⟨0⟩) =
        UInt256.isZero (UInt256.fromBool (decide (delta < 0))) := by
      rw [hd', slt_signed, signed_wordOfInt (signedFits128_int256 hd)]
      rfl
    have hclean : UInt256.land gross (UInt256.ofNat 340282366920938463463374607431768211455) = gross :=
      u256LandMaskCleanOfToNat _ _ rfl hg
    have hσ := tickLiquidityStore_accounts hI id tick gross net
    change (tickLiquidityStore evm id tick gross net).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (tickSlot id tick) (UInt256.lor gross (UInt256.shiftLeft (EVM.wordOfInt net) (UInt256.ofNat 128))) at hσ
    by_cases hd0 : 0 ≤ delta
    · rw [if_pos hd0]
      obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7205_taken hstack
        (Bool.eq_true_of_not_eq_false hp) (by rw [hcond, decide_eq_false (by omega)]; decide +kernel)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      simp only [poolManagerBlocks.poolManager_block_7205_taken_stack, poolManagerBlocks.poolManager_block_7205_taken_memory,
        hclean, ← hσ] at rd1
      exact ⟨k1, C1, rd1⟩
    · rw [if_neg hd0]
      obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_7205_fallthrough hstack
        (Bool.eq_true_of_not_eq_false hp) (by rw [hcond, decide_eq_true (by omega)]; rfl) h
      simp only [poolManagerBlocks.poolManager_block_7205_fallthrough_stack, poolManagerBlocks.poolManager_block_7205_fallthrough_memory,
        hclean, ← hσ] at rd1
      exact ⟨k1, C1, rd1⟩

theorem tickUpperStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id gross flipped x4 x5 x6 ptr x8 x9 x10 : UInt256}
    {tick net delta : Int} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hI : evm.executionEnv = I)
    (hg : gross.toNat < 2^128) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨7205⟩
      (tickSlot id tick :: gross :: EVM.wordOfInt net :: flipped :: x4 :: x5 :: x6 :: ptr :: x8 :: x9 :: x10 ::
        EVM.wordOfInt delta :: R) mem aw rdata evm.accountMap k C) :
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
        (x4 :: x5 :: x6 :: ptr :: x8 :: x9 :: x10 :: EVM.wordOfInt delta :: R)
        (tickUpperResultMemory mem ptr gross flipped) aw' rdata (tickLiquidityStore evm id tick gross net).accountMap k' C' := by
  have hr := tickUpperStoreExactTrace v hstack hI hg hd h
  by_cases hp : I.perm = false
  · simpa only [if_pos hp] using hr
  · rw [if_neg hp] at hr ⊢
    obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
