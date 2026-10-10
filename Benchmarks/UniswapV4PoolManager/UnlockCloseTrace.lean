import Benchmarks.UniswapV4PoolManager.BytesReturnMemory
import Benchmarks.UniswapV4PoolManager.LockSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_025
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem unlockCloseReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata data : ByteArray} {aw ptr dest : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hv : BytesObjectView mem ptr data) (hfree : memLoad ⟨64⟩ mem = dest)
    (hbefore : ptr.toNat+32+data.size ≤ dest.toNat)
    (hfit : dest.toNat+data.size+96 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9089⟩ (ptr :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (lockSetPost evm false).accountMap (bytesReturnEncoding data) := by
  have hlen : memLoad ptr ((UInt256.ofNat 32).toByteArray.write 0 mem dest.toNat 32) =
      UInt256.ofNat data.size := (hv.writeWord_after dest.toNat ⟨32⟩ hbefore).lengthWord
  have hd : (UInt256.ofNat data.size).toNat = data.size := UInt256.toNat_ofNat_of_lt (by omega)
  have hsrc : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 :=
    uadd_word_ofNat_toNat ptr 32 (by omega)
  have h32 : (dest+UInt256.ofNat 32).toNat = dest.toNat+32 :=
    uadd_word_ofNat_toNat dest 32 (by omega)
  have h64 : (dest+UInt256.ofNat 64).toNat = dest.toNat+64 :=
    uadd_word_ofNat_toNat dest 64 (by omega)
  have hsum : (dest+UInt256.ofNat data.size).toNat = dest.toNat+data.size :=
    uadd_word_ofNat_toNat dest data.size (by omega)
  have hend : ((dest+UInt256.ofNat data.size)+UInt256.ofNat 64).toNat = dest.toNat+64+data.size := by
    rw [uadd_word_ofNat_toNat _ 64 (by rw [hsum]; omega), hsum]
    omega
  have hpadded := paddedSize_le_add31 data.size
  have hpad : (paddedWord (UInt256.ofNat data.size)).toNat = paddedSize data.size := by
    rw [paddedWord_toNat _ (by rw [hd]; omega), hd]
  have hrlen : (UInt256.sub (dest+paddedWord (UInt256.ofNat data.size)) dest+UInt256.ofNat 64).toNat =
      64+paddedSize data.size := by
    rw [word_add_sub_left, uadd_word_ofNat_toNat _ 64 (by rw [hpad]; omega), hpad]
    omega
  have hr := poolManager_block_9089 hstack hp h
  have hf : memLoad (UInt256.ofNat 64) mem = dest := hfree
  rw [hf, hlen, hsrc, h32, h64, hend, hd] at hr
  change RDret _ _ _ _ ((bytesReturnMemory mem ptr dest data).readWithPadding dest.toNat
    (UInt256.sub (dest+paddedWord (UInt256.ofNat data.size)) dest+UInt256.ofNat 64).toNat) at hr
  rw [hrlen, bytesReturnMemory_read hv hbefore] at hr
  have hs : (lockSetPost evm false).accountMap = tstoreAccountMap I.codeOwner evm.accountMap
      (UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923) ⟨0⟩ := by
    rw [lockSetPost, transientStore_accountMap, hI]
    rfl
  rw [hs]
  exact hr

theorem unlockCloseTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata data : ByteArray} {aw ptr dest saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hv : BytesObjectView mem ptr data) (hfree : memLoad ⟨64⟩ mem = dest)
    (hbefore : ptr.toNat+32+data.size ≤ dest.toNat)
    (hfit : dest.toNat+data.size+96 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9049⟩ (saved :: ptr :: R) mem aw rdata evm.accountMap k C) :
    if transientWord evm deltaCountSlot = ⟨0⟩ then
      RDret (deployedRuntime v) g s0 (lockSetPost evm false).accountMap (bytesReturnEncoding data)
    else RDrev (deployedRuntime v) g s0 := by
  have hw := transientWord_accountMap hI deltaCountSlot
  by_cases hc : transientWord evm deltaCountSlot = ⟨0⟩
  · rw [if_pos hc]
    have rd := poolManager_block_9049_fallthrough (by simp only [List.length_cons]; omega)
      (by change codeOwnerTransientWord I evm.accountMap deltaCountSlot = ⟨0⟩; rw [← hw]; exact hc) h
    exact unlockCloseReturnTrace v hstack hI hp hv hfree hbefore hfit rd
  · rw [if_neg hc]
    have rd := poolManager_block_9049_taken (by simp only [List.length_cons]; omega)
      (by change codeOwnerTransientWord I evm.accountMap deltaCountSlot ≠ ⟨0⟩; rw [← hw]; exact hc)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManager_block_9202
      (by simp only [poolManager_block_9049_taken_stack, List.length_cons]; omega) rd

end Benchmarks.UniswapV4PoolManager
