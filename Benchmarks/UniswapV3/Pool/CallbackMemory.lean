import Benchmarks.UniswapV3.Pool.CallbackEncoding
import Benchmarks.UniswapV3.Pool.SafeTransferMemory
import Benchmarks.UniswapV3.Pool.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATES: copying an in-bounds source slice, including empty slices.
theorem copyWindow_size_all (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest + len) := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_write_len_zero, Nat.add_zero, max_eq_left hdest]
  · exact copyWindow_size src mem srcOff dest len hz hsrc hdest

theorem copyWindow_read_below_len (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbelow : read + count ≤ dest) (hcount : 0 < count) :
    (src.write srcOff mem dest len).readWithPadding read count =
      mem.readWithPadding read count := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  · have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
    have hs : (src.extract srcOff (srcOff + len)).size = len := by
      rw [ByteArray.size_extract]; omega
    rw [readWithPadding_eq_extract_unbounded _ _ _ hcount (by
        rw [copyWindow_size src mem srcOff dest len hz hsrc hdest]; omega),
      readWithPadding_eq_extract_unbounded _ _ _ hcount (by omega),
      copyWindow_eq src mem srcOff dest len hz hsrc hdest,
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
      extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
    congr 1 <;> omega

theorem copyWindow_read_back_all (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).readWithPadding dest len =
      src.extract srcOff (srcOff + len) := by
  by_cases hz : len = 0
  · subst len
    simp only [byteArray_readWithPadding_zero, Nat.add_zero]
    apply ByteArray.ext
    simp only [ByteArray.data_extract, ByteArray.data_empty]
    exact (Array.extract_eq_empty_of_le (Nat.min_le_left _ _)).symm
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [copyWindow_size src mem srcOff dest len hz hsrc hdest]; omega)]
    simpa only [Nat.add_zero] using
      copyWindow_extract src mem srcOff dest len 0 len hz hsrc hdest (by omega)

theorem memoryPrefix_copyWindow (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) (hl : limit ≤ dest) :
    MemoryPrefix mem (src.write srcOff mem dest len) limit := by
  refine ⟨?_, fun read _ hi _ ↦ ?_⟩
  · rw [copyWindow_size_all src mem srcOff dest len hsrc hdest]; omega
  · exact copyWindow_read_below_len src mem srcOff dest len read 32 hsrc hdest
      (by omega) (by decide)

-- LIBRARY CANDIDATE: a read split that permits empty adjacent windows.
theorem readWindow_split (mem : ByteArray) (off a b : Nat)
    (hin : off + (a + b) ≤ mem.size) :
    mem.readWithPadding off (a + b) =
      mem.readWithPadding off a ++ mem.readWithPadding (off + a) b := by
  by_cases ha : a = 0
  · simp only [ha, Nat.zero_add, Nat.add_zero, byteArray_readWithPadding_zero,
      ByteArray.empty_append]
  · by_cases hb : b = 0
    · simp only [hb, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
    · exact byteArray_readWithPadding_split_unbounded mem off a b (by omega) (by omega) (by omega)

theorem writeWordArray_preserve_below_len (mem : ByteArray) (off read len : Nat)
    (ws : List UInt256) (hbelow : read + len ≤ off) (hin : read + len ≤ mem.size)
    (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWordArray mem off ws).readWithPadding read len = mem.readWithPadding read len := by
  induction ws generalizing mem off with
  | nil => rfl
  | cons w ws ih =>
      rw [writeWordArray, ih _ _ (by omega) (by rw [writeWord_sparse_size]; omega),
        writeWord_sparse_read_preserved_len _ _ _ _ _ (Or.inl ⟨hbelow, hin⟩) hpos hlen]

theorem writeWordArray_bytes (mem : ByteArray) (off : Nat) (ws : List UInt256) :
    (writeWordArray mem off ws).readWithPadding off (32 * ws.length) = wordBytes ws := by
  induction ws generalizing mem off with
  | nil => exact byteArray_readWithPadding_zero mem off
  | cons w ws ih =>
      have hs := writeWordArray_size mem off (w :: ws) (by simp)
      have hr := writeWordArray_read mem off (w :: ws) 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at hr
      rw [List.length_cons, show 32 * (ws.length + 1) = 32 + 32 * ws.length by omega,
        readWindow_split _ _ _ _ (by simp only [List.length_cons] at hs; omega), hr]
      change w.toByteArray ++ (writeWordArray (writeWord mem off w) (off + 32) ws).readWithPadding
        (off + 32) (32 * ws.length) = wordBytes (w :: ws)
      rw [ih, wordBytes]

-- LIBRARY CANDIDATE: the common two-word-and-bytes callback head.
def callbackHeadMem (mem : ByteArray) (off : Nat) (selector a b len : UInt256) : ByteArray :=
  writeWordArray (writeWord mem off selector) (off + 4) [a, b, ⟨96⟩, len]

theorem callbackHeadMem_size (mem : ByteArray) (off : Nat) (selector a b len : UInt256) :
    (callbackHeadMem mem off selector a b len).size = max mem.size (off + 132) := by
  rw [callbackHeadMem, writeWordArray_size _ _ _ (by simp), writeWord_sparse_size]
  simp only [List.length_cons, List.length_nil]
  omega

theorem callbackHeadMem_prefix (mem : ByteArray) (off : Nat) (selector a b len : UInt256) :
    MemoryPrefix mem (callbackHeadMem mem off selector a b len) off :=
  (memoryPrefix_sparse_writeWord mem off off selector (Or.inl (le_refl _))).trans
    (writeWordArray_prefix _ _ off _ (by omega))

theorem callbackHeadMem_read (mem : ByteArray) (off : Nat) (selector a b len : UInt256) :
    (callbackHeadMem mem off selector a b len).readWithPadding off 132 =
      selector.toByteArray.extract 0 4 ++ wordBytes [a, b, ⟨96⟩, len] := by
  rw [show 132 = 4 + 128 from rfl, readWindow_split _ _ _ _ (by
    rw [callbackHeadMem_size]; omega)]
  unfold callbackHeadMem
  rw [writeWordArray_preserve_below_len _ _ _ _ _ (by omega)
    (by rw [writeWord_sparse_size]; omega) (by decide) (by decide)]
  have hselector := writeWord_sparse_read_window mem off 0 4 selector (by decide)
    (by decide) (by decide)
  simp only [Nat.add_zero, Nat.zero_add] at hselector
  rw [hselector]
  congr 1
  exact writeWordArray_bytes _ _ [a, b, ⟨96⟩, len]

theorem callbackHeadMem_read64 (mem : ByteArray) (off : Nat) (selector a b len : UInt256)
    (ho : 96 ≤ off) (hm : 96 ≤ mem.size) :
    (callbackHeadMem mem off selector a b len).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  rw [callbackHeadMem, writeWordArray_preserve_below _ _ _ _ (by omega)
    (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨ho, hm⟩)]


def callbackCopyMem (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) : ByteArray :=
  cd.write srcOff (callbackHeadMem mem off selector a b (UInt256.ofNat len)) (off + 132) len

def callbackMem (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) : ByteArray :=
  writeWord (callbackCopyMem mem off selector a b cd srcOff len) (off + 132 + len) ⟨0⟩

theorem callbackCopyMem_size (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) :
    (callbackCopyMem mem off selector a b cd srcOff len).size =
      max mem.size (off + 132 + len) := by
  rw [callbackCopyMem, copyWindow_size_all _ _ _ _ _ hc (by
    rw [callbackHeadMem_size]; omega), callbackHeadMem_size]
  omega

theorem callbackMem_size (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) :
    (callbackMem mem off selector a b cd srcOff len).size =
      max mem.size (off + 164 + len) := by
  rw [callbackMem, writeWord_sparse_size, callbackCopyMem_size _ _ _ _ _ _ _ _ hc]
  omega

theorem callbackMem_prefix (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) :
    MemoryPrefix mem (callbackMem mem off selector a b cd srcOff len) off :=
  (callbackHeadMem_prefix mem off selector a b _).trans
    ((memoryPrefix_copyWindow cd _ srcOff (off + 132) len off hc
      (by rw [callbackHeadMem_size]; omega) (by omega)).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))))

theorem callbackMem_read64 (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size)
    (ho : 96 ≤ off) (hm : 96 ≤ mem.size) :
    (callbackMem mem off selector a b cd srcOff len).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  rw [callbackMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
    rw [callbackCopyMem_size _ _ _ _ _ _ _ _ hc]; omega⟩)]
  rw [callbackCopyMem, copyWindow_read_below_len _ _ _ _ _ _ _ hc (by
    rw [callbackHeadMem_size]; omega) (by omega) (by decide),
    callbackHeadMem_read64 _ _ _ _ _ _ ho hm]

theorem callbackMem_read_head (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) :
    (callbackMem mem off selector a b cd srcOff len).readWithPadding off 132 =
      selector.toByteArray.extract 0 4 ++ wordBytes [a, b, ⟨96⟩, UInt256.ofNat len] := by
  rw [callbackMem, writeWord_sparse_read_preserved_len _ _ _ _ _ (Or.inl ⟨by omega, by
    rw [callbackCopyMem_size _ _ _ _ _ _ _ _ hc]; omega⟩) (by decide) (by decide)]
  rw [callbackCopyMem, copyWindow_read_below_len _ _ _ _ _ _ _ hc (by
    rw [callbackHeadMem_size]; omega) (by omega) (by decide), callbackHeadMem_read]

theorem callbackMem_read_data (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) (hl : len < 2 ^ 64) :
    (callbackMem mem off selector a b cd srcOff len).readWithPadding (off + 132) len =
      cd.extract srcOff (srcOff + len) := by
  by_cases hz : len = 0
  · subst len
    simp only [byteArray_readWithPadding_zero, Nat.add_zero]
    apply ByteArray.ext
    simp only [ByteArray.data_extract, ByteArray.data_empty]
    exact (Array.extract_eq_empty_of_le (Nat.min_le_left _ _)).symm
  · rw [callbackMem, writeWord_sparse_read_preserved_len _ _ _ _ _ (Or.inl ⟨by omega, by
      rw [callbackCopyMem_size _ _ _ _ _ _ _ _ hc]; omega⟩) (by omega) hl]
    exact copyWindow_read_back_all cd _ srcOff (off + 132) len hc (by
      rw [callbackHeadMem_size]; omega)

theorem callbackMem_read_padding (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) :
    (callbackMem mem off selector a b cd srcOff len).readWithPadding (off + 132 + len)
      (paddedSize len - len) = ByteArray.zeroes (paddedSize len - len) := by
  have hb : paddedSize len - len ≤ 32 := by unfold paddedSize; omega
  by_cases hz : paddedSize len - len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
    exact (zeroes_zero rfl).symm
  · have hr := writeWord_sparse_read_window
      (callbackCopyMem mem off selector a b cd srcOff len) (off + 132 + len) 0
      (paddedSize len - len) ⟨0⟩ (by omega) (by omega) (by omega)
    simp only [Nat.add_zero, Nat.zero_add] at hr
    rw [callbackMem, hr, zero_toByteArray_eq_zeroes32, zeroes32_extract_zeroes _ hb]

theorem callbackMem_read (mem : ByteArray) (off : Nat) (selector a b : UInt256)
    (cd : ByteArray) (srcOff len : Nat) (hc : srcOff + len ≤ cd.size) (hl : len < 2 ^ 64) :
    (callbackMem mem off selector a b cd srcOff len).readWithPadding off (132 + paddedSize len) =
      selector.toByteArray.extract 0 4 ++ wordPairBytesPayload a b
        (cd.extract srcOff (srcOff + len)) := by
  have hpad : len ≤ paddedSize len ∧ paddedSize len ≤ len + 31 := by unfold paddedSize; omega
  have hs : (cd.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [readWindow_split _ _ _ _ (by rw [callbackMem_size _ _ _ _ _ _ _ _ hc]; omega),
    callbackMem_read_head _ _ _ _ _ _ _ _ hc]
  rw [show paddedSize len = len + (paddedSize len - len) by omega,
    readWindow_split _ _ _ _ (by rw [callbackMem_size _ _ _ _ _ _ _ _ hc]; omega),
    callbackMem_read_data _ _ _ _ _ _ _ _ hc hl, callbackMem_read_padding]
  simp only [wordBytes, wordPairBytesPayload, hs, ByteArray.append_empty, ByteArray.append_assoc]
  rfl

end Benchmarks.UniswapV3.Pool
