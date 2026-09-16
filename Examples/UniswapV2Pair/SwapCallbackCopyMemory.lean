import Examples.UniswapV2Pair.SwapCallbackCopyRuntime
import Examples.UniswapV2Pair.ReturnDataMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem swapCallbackPaddedLen_toNat (dataLen : UInt256) (hfit : dataLen.toNat + 31 < UInt256.size) :
    (swapCallbackPaddedLen dataLen).toNat = (dataLen.toNat + 31) / 32 * 32 := by
  unfold swapCallbackPaddedLen
  rw [u256_land_comm, show UInt256.lnot ⟨31⟩ = UInt256.ofNat (2 ^ 256 - 2 ^ 5) by native_decide,
    u256_land_high_mask_toNat _ 5 (by omega), uadd_toNat]
  change ((dataLen.toNat + 31) % UInt256.size) / 32 * 32 = _
  rw [Nat.mod_eq_of_lt hfit]

theorem swapCallbackPaddedLen_bounds (dataLen : UInt256) (hfit : dataLen.toNat + 31 < UInt256.size) :
    dataLen.toNat ≤ (swapCallbackPaddedLen dataLen).toNat ∧
      (swapCallbackPaddedLen dataLen).toNat ≤ dataLen.toNat + 31 := by
  rw [swapCallbackPaddedLen_toNat dataLen hfit]
  have hmod := Nat.mod_lt (dataLen.toNat + 31) (by decide : 0 < 32)
  have hdiv := Nat.div_add_mod (dataLen.toNat + 31) 32
  omega

theorem swapCallbackPaddedMem_eq_append {calldata mem : ByteArray} (ptr dataPtr dataLen : UInt256)
    (hmem : mem.size = ptr.toNat + 164) (hdata : dataPtr.toNat + dataLen.toNat ≤ calldata.size)
    (hlen : dataLen.toNat ≠ 0) (hfit : ptr.toNat + 164 + dataLen.toNat < UInt256.size) :
    swapCallbackPaddedMem calldata mem ptr dataPtr dataLen =
      mem ++ calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat) ++ (⟨0⟩ : UInt256).toByteArray := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have hend : ((ptr + ⟨164⟩) + dataLen).toNat = mem.size + dataLen.toNat := by
    rw [uadd_toNat, h164, Nat.mod_eq_of_lt hfit, hmem]
  have hcopy : swapCallbackCopyMem calldata mem ptr dataPtr dataLen =
      mem ++ calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat) := by
    unfold swapCallbackCopyMem
    rw [h164, ← hmem, write_at_end_eq_from _ _ _ _ hlen hdata]
  have hs : (swapCallbackCopyMem calldata mem ptr dataPtr dataLen).size = mem.size + dataLen.toNat := by
    rw [hcopy, ByteArray.size_append, ByteArray.size_extract]
    omega
  unfold swapCallbackPaddedMem
  rw [hend, ← hs, write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]),
    toByteArray_extract_all, hcopy]

theorem swapCallbackPaddedMem_size {calldata mem : ByteArray} (ptr dataPtr dataLen : UInt256)
    (hmem : mem.size = ptr.toNat + 164) (hdata : dataPtr.toNat + dataLen.toNat ≤ calldata.size)
    (hlen : dataLen.toNat ≠ 0) (hfit : ptr.toNat + 164 + dataLen.toNat < UInt256.size) :
    (swapCallbackPaddedMem calldata mem ptr dataPtr dataLen).size = ptr.toNat + 196 + dataLen.toNat := by
  rw [swapCallbackPaddedMem_eq_append ptr dataPtr dataLen hmem hdata hlen hfit,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  omega

theorem swapCallbackPaddedMem_read_below {calldata mem : ByteArray} (ptr dataPtr dataLen : UInt256) (off len : Nat)
    (hmem : mem.size = ptr.toNat + 164) (hdata : dataPtr.toNat + dataLen.toNat ≤ calldata.size)
    (hlen : dataLen.toNat ≠ 0) (hfit : ptr.toNat + 164 + dataLen.toNat < UInt256.size)
    (hread : off + len ≤ mem.size) (hpos : 0 < len) (hlt : len < 2 ^ 64) :
    (swapCallbackPaddedMem calldata mem ptr dataPtr dataLen).readWithPadding off len = mem.readWithPadding off len := by
  rw [swapCallbackPaddedMem_eq_append ptr dataPtr dataLen hmem hdata hlen hfit]
  rw [readWithPadding_eq_extract' _ off len hpos hlt (by rw [ByteArray.size_append, ByteArray.size_append]; omega),
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append]; omega),
    extract_append_left _ _ _ _ hread, readWithPadding_eq_extract' mem off len hpos hlt hread]

end UniswapV2Pair
