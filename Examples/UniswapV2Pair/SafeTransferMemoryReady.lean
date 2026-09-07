import Examples.UniswapV2Pair.SafeTransferCallCore
import Examples.UniswapV2Pair.SafeTransferFinalMemoryCore
import Examples.UniswapV2Pair.SafeTransferInitialMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

structure SafeTransferMemoryReady (mem : ByteArray) (aw ptr : UInt256) : Prop where
  sizeLo : 96 ≤ mem.size
  gap : ptr.toNat - mem.size < USize.size
  ptrLo : 128 ≤ ptr.toNat
  sizeHi : mem.size ≤ ptr.toNat + 132
  wordsHi : aw.toNat * 32 < UInt256.size
  wordsLo : 96 ≤ aw.toNat * 32
  read64 : mem.readWithPadding 64 32 = ptr.toByteArray
  zeroSlot : ∀ toWord value, (safeTransferDynamicCallMem2 mem ptr toWord value).readWithPadding 96 32 =
    (⟨0⟩ : UInt256).toByteArray

theorem safeTransferMemoryReady_initial :
    SafeTransferMemoryReady solcFreePtrMem (UInt256.ofNat 3) ⟨128⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, solcFreePtrMem_read64, ?_⟩
  · rw [solcFreePtrMem_size]
  · change 128 - solcFreePtrMem.size < _
    rw [solcFreePtrMem_size]; exact lt_usize 32 (by omega)
  · decide
  · rw [solcFreePtrMem_size]; decide
  · native_decide
  · decide
  · intro toWord value
    exact safeTransferDynamicCallMem2_read96_initial toWord value solcFreePtrMem_size

theorem safeTransferMemoryReady_after_call {mem : ByteArray} {aw ptr : UInt256}
    (hready : SafeTransferMemoryReady mem aw ptr) (toWord value : UInt256) (out : ByteArray)
    (hfit : ptr.toNat + out.size + 455 < UInt256.size) :
    ∃ next, SafeTransferMemoryReady (safeTransferDynamicFinalMem mem ptr toWord value out)
      (safeTransferDynamicFinalWords aw ptr out) next ∧ next.toNat ≤ ptr.toNat + out.size + 227 := by
  obtain ⟨next, hm, hgap, hlo, hs, hcap, haw, hawLo, h64, h96⟩ :=
    safeTransferDynamicFinalMemory_invariants_of_zeroSlot aw ptr toWord value out hready.sizeLo
      hready.gap hready.ptrLo hready.sizeHi hready.wordsHi (by omega) (hready.zeroSlot toWord value)
  refine ⟨next, ⟨by omega, hgap, hlo, hs, haw, by omega, h64, ?_⟩, hcap⟩
  intro nextTo nextValue
  exact (safeTransferDynamicCallMem2_read96 next nextTo nextValue hm hgap hlo (by omega)).trans h96

end UniswapV2Pair
