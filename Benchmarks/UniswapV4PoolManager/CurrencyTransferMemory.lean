import Benchmarks.UniswapV4PoolManager.CurrencyTransferABI
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.WordReturnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.write0_from_read32_above: arbitrary write offset and length.
theorem write_read32_above (src base : ByteArray) (srcAddr destAddr len readAddr : Nat)
    (hsrc : srcAddr+len ≤ src.size) (hin : destAddr+len ≤ base.size)
    (habove : destAddr+len ≤ readAddr) (hread : readAddr+32 ≤ base.size) :
    (src.write srcAddr base destAddr len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  have hp : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcAddr (srcAddr+len)).size = len := by rw [ByteArray.size_extract]; omega
  have ht : (base.extract (destAddr+len) base.size).size = base.size-(destAddr+len) := by
    rw [ByteArray.size_extract]; omega
  have hps : (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr+len)).size = destAddr+len := by
    rw [ByteArray.size_append, hp, hs]
  rw [write_eq_gen_from src base srcAddr destAddr len hz hsrc hin,
    readWithPadding_eq_extract _ readAddr (by rw [ByteArray.size_append, hps, ht]; omega),
    readWithPadding_eq_extract _ readAddr hread,
    extract_append_right_window _ _ _ _ (by rw [hps]; omega), hps, extract_extract_BA,
    show destAddr+len+(readAddr-(destAddr+len)) = readAddr from by omega,
    show min (destAddr+len+(readAddr+32-(destAddr+len))) base.size = readAddr+32 from by omega]

-- LIBRARY CANDIDATE: a bounded CALL output copy preserves a disjoint later load.
theorem callOutputMem32_load_above (mem out : ByteArray) (read : UInt256)
    (ho : out.size < UInt256.size) (hlo : 32 ≤ read.toNat) (hread : read.toNat+32 ≤ mem.size) :
    memLoad read (callOutputMem mem out ⟨0⟩ ⟨32⟩) = memLoad read mem := by
  unfold callOutputMem
  rw [callOutputLen32 ho]
  change memLoad read (out.write 0 mem 0 (min 32 out.size)) = _
  have hs := byteArray_write_size_of_inBounds out mem 0 (min 32 out.size) (Nat.min_le_right _ _)
    (by omega)
  rw [memLoad, memLoad, hs, if_neg (by omega : ¬read.toNat ≥ mem.size)]
  rw [write_read32_above out mem 0 0 (min 32 out.size) read.toNat (by omega) (by omega) (by omega) hread]
  rw [if_neg (by omega : ¬read.toNat ≥ mem.size)]

def currencyTransferCleanMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem ptr.toNat ⟨0⟩) (ptr+⟨32⟩).toNat ⟨0⟩) (ptr+⟨64⟩).toNat ⟨0⟩

theorem currencyTransferCleanMemory_wordReturn (mem : ByteArray) (ptr : UInt256)
    (hsize : 96 ≤ mem.size) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hbound : ptr.toNat+64 < UInt256.size) (hin : ptr.toNat ≤ mem.size) :
    WordReturnMemory (currencyTransferCleanMemory mem ptr) := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 : (ptr+⟨64⟩).toNat = ptr.toNat+64 := uadd_word_ofNat_toNat ptr 64 hbound
  unfold currencyTransferCleanMemory
  rw [h32, h64]
  let m₁ := writeWord mem ptr.toNat ⟨0⟩
  let m₂ := writeWord m₁ (ptr.toNat+32) ⟨0⟩
  have hg₁ : ptr.toNat-mem.size < USize.size := by rw [Nat.sub_eq_zero_of_le hin]; exact USize.size_pos
  have hs₁ : m₁.size = max mem.size (ptr.toNat+32) := writeWord_size _ _ _ hg₁
  have hg₂ : ptr.toNat+32-m₁.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]; exact USize.size_pos
  have hs₂ : m₂.size = max m₁.size (ptr.toNat+64) := by
    simpa only [Nat.add_assoc] using writeWord_size m₁ (ptr.toNat+32) ⟨0⟩ hg₂
  have hg₃ : ptr.toNat+64-m₂.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]; exact USize.size_pos
  have hs₃ := writeWord_size m₂ (ptr.toNat+64) ⟨0⟩ hg₃
  have hf₁ : memLoad ⟨64⟩ m₁ = ptr := (memLoad_writeWord_below mem ⟨64⟩ _ _ hsize hlo hg₁).trans hfree
  have hf₂ : memLoad ⟨64⟩ m₂ = ptr :=
    (memLoad_writeWord_below _ _ _ _ (by change 96 ≤ m₁.size; omega)
      (by change 96 ≤ ptr.toNat+32; omega) hg₂).trans hf₁
  change WordReturnMemory (writeWord m₂ (ptr.toNat+64) ⟨0⟩)
  apply WordReturnMemory.of_inBounds (by omega)
  rw [memLoad_writeWord_below _ _ _ _ (by change 96 ≤ m₂.size; omega)
    (by change 96 ≤ ptr.toNat+64; omega) hg₃, hf₂]
  omega

theorem currencyTransferOutput_wordReturn (mem out : ByteArray) (ptr selector arg₀ arg₁ : UInt256)
    (hsize : 96 ≤ mem.size) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hbound : ptr.toNat+64 < UInt256.size) (hgap : ptr.toNat-mem.size < USize.size)
    (ho : out.size < UInt256.size) :
    WordReturnMemory (currencyTransferCleanMemory
      (callOutputMem (twoWordCallMemory mem ptr.toNat selector arg₀ arg₁) out ⟨0⟩ ⟨32⟩) ptr) := by
  have hs := twoWordCallMemory_size mem ptr.toNat selector arg₀ arg₁ hgap
  have hcopy : (callOutputMem (twoWordCallMemory mem ptr.toNat selector arg₀ arg₁) out ⟨0⟩ ⟨32⟩).size =
      (twoWordCallMemory mem ptr.toNat selector arg₀ arg₁).size := by
    unfold callOutputMem
    rw [callOutputLen32 ho]
    exact byteArray_write_size_of_inBounds _ _ 0 _ (Nat.min_le_right _ _) (by rw [hs]; omega)
  apply currencyTransferCleanMemory_wordReturn _ ptr (by omega) _ hlo hbound (by omega)
  rw [callOutputMem32_load_above _ out ⟨64⟩ ho (by decide) (by change 96 ≤ _; omega),
    twoWordCallMemory_load_below mem ⟨64⟩ _ _ _ _ hsize hlo hgap, hfree]

end Benchmarks.UniswapV4PoolManager
