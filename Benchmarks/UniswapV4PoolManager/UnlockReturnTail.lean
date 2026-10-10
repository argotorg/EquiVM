import Benchmarks.UniswapV4PoolManager.UnlockReturnPrefix
import Benchmarks.UniswapV4PoolManager.BytesObjectCopyTrace
import Benchmarks.UniswapV4PoolManager.UnlockCloseTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

abbrev unlockDecodedEnd (out : ByteArray) : UInt256 :=
  allocationEnd (unlockRawEnd out) (bytesAllocationSize (unlockReturnLength out))

/-- Finish the reply decoder, preserving the second allocator's panic branch. -/
theorem unlockReturnTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hout : out.size < 2^138) (hmem : 160 ≤ mem.size)
    (hraw : AllocationBounds ⟨160⟩ (UInt256.ofNat out.size))
    (hhead : BytesReturnHeadBounds out)
    (h : RD (deployedRuntime v) I g s0 ⟨11822⟩
      (unlockRawEnd out :: bytesAllocationSize (unlockReturnLength out) :: ⟨9374⟩ ::
        (⟨160⟩+UInt256.ofNat out.size) :: (⟨160⟩+calldataWord out 0) ::
        unlockReturnLength out :: unlockRawEnd out :: saved :: R)
      (copiedReturnMemory out mem 160 (unlockRawEnd out)) aw out evm.accountMap k C) :
    (¬AllocationBounds (unlockRawEnd out) (bytesAllocationSize (unlockReturnLength out)) ∧
      RD (deployedRuntime v) I g s0 ⟨7857⟩
        (unlockDecodedEnd out :: ⟨9374⟩ :: (⟨160⟩+UInt256.ofNat out.size) ::
          (⟨160⟩+calldataWord out 0) :: unlockReturnLength out :: unlockRawEnd out :: saved :: R)
        (copiedReturnMemory out mem 160 (unlockRawEnd out)) aw out evm.accountMap (k+18) (C+59)) ∨
    (¬BytesReturnBounds out ∧ RDrev (deployedRuntime v) g s0) ∨
    (BytesReturnBounds out ∧
      if transientWord evm deltaCountSlot = ⟨0⟩ then
        RDret (deployedRuntime v) g s0 (lockSetPost evm false).accountMap
          (bytesReturnEncoding (bytesReturnPayload out))
      else RDrev (deployedRuntime v) g s0) := by
  rcases allocateCheckedTrace v (by simp only [List.length_cons]; omega)
      (by rw [deployedRuntime_jumps]; jump_dest) h with ⟨hbad, hr⟩ | ⟨hb, rd1⟩
  · exact .inl ⟨hbad, hr⟩
  · let off := calldataWord out 0
    let len := unlockReturnLength out
    let src : UInt256 := ⟨160⟩+off
    let ptr := unlockRawEnd out
    let next := unlockDecodedEnd out
    let m0 := copiedReturnMemory out mem 160 ptr
    let m1 := writeWord m0 64 next
    have hoff : off.toNat ≤ 2^64-1 := hhead.2.1
    have hlen : len.toNat ≤ 2^64-1 := hhead.2.2.2
    have hptr : ptr.toNat ≤ 2^64-1 := hraw.2
    have hnext : next.toNat ≤ 2^64-1 := hb.2
    have ho : (UInt256.ofNat out.size).toNat = out.size :=
      UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
    have hptrNat : ptr.toNat = 160+paddedSize out.size := by
      rw [allocationEnd_toNat _ _ (by rw [ho]; change 160+out.size+31 < 2^256; omega), ho]
      rfl
    have hnextNat : next.toNat = ptr.toNat+32+paddedSize len.toNat :=
      bytesAllocationEnd_toNat ptr len (by change _ < 2^256; omega)
    have hsrc : src.toNat = 160+off.toNat := by
      rw [uadd_toNat]
      change (160+off.toNat)%UInt256.size = _
      exact Nat.mod_eq_of_lt (by change _ < 2^256; omega)
    have he : ((⟨160⟩ : UInt256)+UInt256.ofNat out.size).toNat = 160+out.size :=
      uadd_word_ofNat_toNat ⟨160⟩ out.size (by change 160+out.size < 2^256; omega)
    have hslen : (src+len).toNat = 160+off.toNat+len.toNat := by
      rw [uadd_toNat, hsrc, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    have hend : (src+len+UInt256.ofNat 32).toNat = 160+off.toNat+len.toNat+32 := by
      rw [uadd_word_ofNat_toNat _ 32 (by rw [hslen]; change _ < 2^256; omega), hslen]
    change RD _ _ _ _ ⟨9374⟩
      (((⟨160⟩ : UInt256)+UInt256.ofNat out.size) :: src :: len :: ptr :: saved :: R)
      m1 _ _ _ _ _ at rd1
    by_cases hpayload : off.toNat+32+len.toNat ≤ out.size
    swap
    · have rd := poolManager_block_9374_taken (by simp only [List.length_cons]; omega)
        (by rw [ugt_one (by rw [hend, he]; omega)]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact .inr (.inl ⟨fun hh => hpayload hh.2.2.2.2.2, emptyRevert v
        (by simp only [poolManager_block_9374_taken_stack, List.length_cons]; omega) rd⟩)
    have rd2 := poolManager_block_9374_fallthrough (by simp only [List.length_cons]; omega)
      (ugt_zero (by rw [hend, he]; omega)) rd1
    dsimp only [poolManager_block_9374_fallthrough_stack, poolManager_block_9374_fallthrough_memory] at rd2
    obtain ⟨aw', k', C', _, rd3⟩ := bytesObjectCopyTrace (mem := m1) v (by omega)
      (by rw [hsrc]; change _ < 2^256; omega) (by change _ < 2^256; omega) rd2
    have hfull : BytesReturnBounds out :=
      ⟨hhead.1, lt_trans hout (by decide), hhead.2.1, hhead.2.2.1, hhead.2.2.2, hpayload⟩
    have hm0 : m0.size = max mem.size (160+out.size) :=
      copiedReturnMemory_size _ _ _ _ (by omega) hmem
    have hm1 : m1.size = m0.size := by
      dsimp only [m1]
      rw [writeWord_sparse_size, hm0]
      omega
    have hsrcMem : src.toNat+32+len.toNat ≤ m1.size := by
      rw [hm1, hm0, hsrc]
      omega
    have hsrcBefore : src.toNat+32+len.toNat ≤ ptr.toNat := by
      rw [hsrc, hptrNat]
      have := nat_le_paddedSize out.size
      omega
    have hdata : (bytesReturnPayload out).size = len.toNat := by
      rw [bytesReturnPayload, ByteArray.size_extract]
      change min ((calldataWord out 0).toNat+32+(unlockReturnLength out).toNat) out.size -
        ((calldataWord out 0).toNat+32) = len.toNat
      change off.toNat+32+len.toNat ≤ out.size at hpayload
      change min (off.toNat+32+len.toNat) out.size - (off.toNat+32) = len.toNat
      omega
    have hread : m1.readWithPadding (src.toNat+32) len.toNat = bytesReturnPayload out := by
      dsimp only [m1]
      rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _
        (by rw [hm0, hsrc]; omega) (.inr (by rw [hsrc]; omega)), hsrc,
        show 160+off.toNat+32 = 160+(off.toNat+32) by omega,
        copiedReturnMemory_read _ _ _ _ _ _ (by omega) hmem (by decide) hpayload]
      rfl
    have hv := bytesObjectMemory_view m1 (bytesReturnPayload out) (src.toNat+32) ptr len
      hsrcMem hsrcBefore hdata hread
    have hf : memLoad ⟨64⟩ (bytesObjectMemory m1 (src.toNat+32) ptr len) = next := by
      rw [bytesObjectMemory_load_before _ _ _ _ _ hsrcMem
        (by change 64+32 ≤ m1.size; rw [hm1, hm0]; omega)
        (by change 64+32 ≤ ptr.toNat; rw [hptrNat]; omega)]
      exact writeWord_sparse_load_back m0 ⟨64⟩ next
    refine .inr (.inr ⟨hfull, ?_⟩)
    exact unlockCloseTrace v (by simp only [List.length_cons]; omega) hI hp hv hf
      (by rw [hdata, hnextNat]; have := nat_le_paddedSize len.toNat; omega)
      (by rw [hdata]; change _ < 2^256; omega) rd3

end Benchmarks.UniswapV4PoolManager
