import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory
import Benchmarks.Morpho.MorphoBlue.SafeTransferCodeGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferEncodePC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15084 else 14720)
def safeTransferBeforeCallPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15159 else 14854)
def safeTransferCallPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15163 else 14858)
def safeTransferCallAllocatorPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 11479 else 11535)
def safeTransferAllocationArgs (isFrom : Bool) (ptr : UInt256) : List UInt256 :=
  if isFrom then [ptr] else [ptr, UInt256.ofNat 100]

def safeTransferEncodeStack (isFrom : Bool) (token sender recipient : AccountAddress)
    (value ret : UInt256) (R : List UInt256) : List UInt256 :=
  (if isFrom then [solcAddrMask, value, UInt256.ofNat recipient.val, UInt256.ofNat 0, UInt256.ofNat sender.val]
    else [value, UInt256.ofNat 14854, UInt256.ofNat 14810, UInt256.ofNat 0, UInt256.ofNat recipient.val]) ++
    [UInt256.ofNat token.val, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 15005, ret] ++ R

def safeTransferCallHeader (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (safeTransferCallPayload isFrom sender recipient value mem ptr) ptr.toNat
    (UInt256.ofNat (safeTransferCallSize isFrom))

theorem morphoTransferEncode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress)
    (hstack : R.length + 18 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hb : ptr.toNat + 160 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEncodePC isFrom)
      (safeTransferEncodeStack isFrom token sender recipient value ret R) mem aw out σ k C) :
    ∃ a k C, RD (deployedRuntime v) ee g s0 (safeTransferCallAllocatorPC isFrom)
      (safeTransferAllocationArgs isFrom ptr ++
        [safeTransferBeforeCallPC isFrom, ptr, UInt256.ofNat 0, ptr + UInt256.ofNat 32,
          UInt256.ofNat token.val, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 15005, ret] ++ R)
      (safeTransferCallHeader isFrom sender recipient value mem ptr) a out σ k C := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 := uadd_word_ofNat_toNat ptr 68 (by omega)
  have h100 := uadd_word_ofNat_toNat ptr 100 (by omega)
  have hto : UInt256.land (UInt256.ofNat recipient.val) solcAddrMask = UInt256.ofNat recipient.val :=
    addressWord_val_clean recipient
  have hfrom : UInt256.land (UInt256.ofNat sender.val) solcAddrMask = UInt256.ofNat sender.val :=
    addressWord_val_clean sender
  cases isFrom
  · have htoL : UInt256.land (UInt256.ofNat recipient.val)
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat recipient.val := hto
    obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_14720_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 13 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_14720_stack] at rd0
    rw [hfree, u256_add_assoc] at rd0
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_14810_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 5 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    dsimp only [morphoBlocks.morpho_block_14810_stack, morphoBlocks.morpho_block_14810_memory,
      morphoBlocks.morpho_block_14720_memory] at rd1
    rw [word_add_sub_left, hfree, htoL, h32, h36,
      u256_add_assoc ptr (UInt256.ofNat 36) (UInt256.ofNat 32)] at rd1
    rw [show UInt256.ofNat 36 + UInt256.ofNat 64 = UInt256.ofNat 100 by decide,
      show UInt256.ofNat 100 + UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 = UInt256.ofNat 68 by decide,
      show UInt256.ofNat 36 + UInt256.ofNat 32 = UInt256.ofNat 68 by decide] at rd1
    change RD _ _ _ _ _
      (ptr :: UInt256.ofNat 100 :: UInt256.ofNat 14854 :: ptr :: UInt256.ofNat 0 ::
        (ptr + UInt256.ofNat 32) :: UInt256.ofNat token.val :: UInt256.ofNat 0 :: UInt256.ofNat 0 ::
        UInt256.ofNat 15005 :: ret :: R)
      ((UInt256.ofNat 68).toByteArray.write 0
        (value.toByteArray.write 0 ((UInt256.ofNat recipient.val).toByteArray.write 0
          ((safeTransferSelectorWord false).toByteArray.write 0 mem (ptr.toNat + 32) 32)
            (ptr.toNat + 36) 32) (ptr + UInt256.ofNat 68).toNat 32) ptr.toNat 32)
      _ _ _ _ _ at rd1
    rw [h68] at rd1
    exact ⟨a1, k1, C1, rd1⟩
  · obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_15084_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 10 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_15084_stack, morphoBlocks.morpho_block_15084_memory] at rd0
    rw [hfree, hto, hfrom, h32, h36, h68, h100] at rd0
    exact ⟨a0, k0, C0, rd0⟩

theorem morphoTransferAllocate {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferCallAllocatorPC isFrom)
      (safeTransferAllocationArgs isFrom ptr ++ ret :: R) mem aw out σ k C) :
    ∃ a k C, RD (deployedRuntime v) ee g s0 ret R
      (writeWord mem 64 (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom))) a out σ k C := by
  cases isFrom
  · obtain ⟨a, k, C, rd⟩ := morphoAllocDynamicExact 100 hstack hvalid
      (by change ptr.toNat + 128 < 2 ^ 64 at hfit; omega)
      (by exact hfit) h
    exact ⟨a, k, C, rd⟩
  · change ptr.toNat + 160 < 2 ^ 64 at hfit
    have hp := uadd_word_ofNat_toNat ptr 160 (by change _ < 2 ^ 256; omega)
    have rd0 := morphoBlocks.morpho_block_11479_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [ugt_zero (by rw [hp]; change _ ≤ 18446744073709551615; omega),
        ult_zero (by rw [hp]; omega)]; rfl) h
    exact morphoBlocks.morpho_block_11503_packed (immWords := wordsOf (immStore v))
      (by omega) hvalid rd0

theorem morphoTransferAllocateOverflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (hstack : R.length + 5 ≤ 1024)
    (hp : ptr.toNat < 2 ^ 64) (hbad : 2 ^ 64 ≤ ptr.toNat + safeTransferCallAllocation isFrom)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferCallAllocatorPC isFrom)
      (safeTransferAllocationArgs isFrom ptr ++ ret :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  cases isFrom
  · exact morphoAllocDynamicOverflow 100 hstack (by omega) hbad h
  · change 2 ^ 64 ≤ ptr.toNat + 160 at hbad
    have ha := uadd_word_ofNat_toNat ptr 160 (by change _ < 2 ^ 256; omega)
    have rd0 := morphoBlocks.morpho_block_11479_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [ugt_one (by rw [ha]; change 18446744073709551615 < _; omega)]
          exact u256_lor_one_left_ne_zero _)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega) rd0

end Benchmarks.Morpho.MorphoBlue
