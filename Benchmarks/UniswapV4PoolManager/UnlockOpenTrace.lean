import Benchmarks.UniswapV4PoolManager.BytesCallTrace
import Benchmarks.UniswapV4PoolManager.UnlockABI
import Benchmarks.UniswapV4PoolManager.LockSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_025

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem unlockOpenStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw len src : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hp : I.perm = false)
    (h : RD (deployedRuntime v) I g s0 ⟨8928⟩ (len :: src :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.push2 ⟨9029⟩
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8928⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((⟨9029⟩ : UInt256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8931⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8932⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8933⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 ⟨1⟩
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8934⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨1⟩ : UInt256), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pushConst lockSlot (width := 32) (op := .PUSH32) (by decide)
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8936⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some (lockSlot, 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact tstoreStatic r6 hp
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨8969⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem unlockOpenTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw len src : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (hlen : len.toNat ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨8928⟩ (len :: src :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', C+271+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
      RD (deployedRuntime v) I g s0 ⟨9029⟩
      (UInt256.ofNat (228+paddedSize len.toNat) :: ⟨160⟩ :: ⟨160⟩ :: ⟨0⟩ :: ⟨160⟩ :: R)
      (bytesCallMemory I.calldata mem 160 src.toNat unlockCallbackSelectorWord len)
      aw' rdata (lockSetPost evm true).accountMap k' C' := by
  have hm : poolManagerBlocks.poolManager_block_8928_memory (mem := mem) =
      singleWordCallMemory mem 160 unlockCallbackSelectorWord ⟨32⟩ := by
    unfold poolManagerBlocks.poolManager_block_8928_memory
    change (UInt256.ofNat 32).toByteArray.write 0
      ((UInt256.ofNat 65976631833915796866350252598856538248815255225364396687512814530006169419776).toByteArray.write
        0 mem (memLoad ⟨64⟩ mem).toNat 32) ((memLoad ⟨64⟩ mem)+UInt256.ofNat 4).toNat 32 = _
    rw [hfree]
    rfl
  have rd := poolManagerBlocks.poolManager_block_8928 (by omega) hp
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [poolManagerBlocks.poolManager_block_8928_stack] at rd
  change RD _ _ _ _ ⟨12396⟩
    (src :: len :: (memLoad ⟨64⟩ mem+⟨36⟩) :: ⟨9029⟩ ::
      memLoad ⟨64⟩ mem :: memLoad ⟨64⟩ mem :: ⟨0⟩ :: memLoad ⟨64⟩ mem :: R)
    _ _ _ _ _ _ at rd
  rw [hfree, hm] at rd
  have hstore : (lockSetPost evm true).accountMap = tstoreAccountMap I.codeOwner evm.accountMap
      (UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923)
      (UInt256.ofNat 1) := by
    rw [lockSetPost, transientStore_accountMap, hI]
    rfl
  rw [← hstore] at rd
  obtain ⟨aw', k', C', hc, hr⟩ := encodeBytesCallTrace (off := ⟨160⟩) v (by simp only [List.length_cons]; omega)
    (by rw [hmem]; decide) (by rw [hmem]; exact (by native_decide))
    (by change 160+len.toNat+100 < UInt256.size; norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) rd
  refine ⟨aw', k', C', ?_, hr⟩
  dsimp only [memExpansionCost, Ctstore, GasConstants.Gwarmaccess] at hc
  omega

end Benchmarks.UniswapV4PoolManager
