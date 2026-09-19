import Solm.Benchmarks.Auction.MemoryGrowth
import Solm.Benchmarks.Auction.RawEthRoutine
import Solm.Benchmarks.Auction.DepositCall
import Solm.Benchmarks.Auction.TransferRoutine
import Solm.Benchmarks.Auction.BurnCall
import Solm.Benchmarks.Auction.NounTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem emptyEncodedWords_mono {aw ptr} (ha : ActiveWords aw)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) : aw.toNat ≤ (emptyEncodedWords aw ptr).toNat := by
  have hn := nextEmptyPtr_toNat hb
  have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  unfold emptyEncodedWords emptyHeaderWords
  rw [expandedWords32_chain ha (le_refl _) hb32,
    expandedWords32_chain ha (by omega) (by omega)]
  exact expandedWords_mono ha (by change _ + 32 ≤ _; omega)

theorem rawReturnWords_mono {aw ptr out} (ha : ActiveWords aw)
    (hb : ptr.toNat + out.size + 63 ≤ 2 ^ 200) :
    aw.toNat ≤ (rawReturnWords aw ptr out).toNat := by
  unfold rawReturnWords
  split
  · exact le_refl _
  · have hp : (UInt256.add ptr ⟨32⟩).toNat = ptr.toNat + 32 :=
      addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
    have ho : (UInt256.ofNat out.size).toNat = out.size :=
      ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
    exact le_trans (expandedWords_mono ha hb32)
      (expandedWords_mono (activeWords_expand32 ha hb32) (by rw [hp, ho]; omega))

theorem rawEthWords_mono {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200) (ho : out.size < 2 ^ 138) :
    aw.toNat ≤ (rawEthWords aw ptr out).toNat := by
  have hb64 : ptr.toNat + 64 ≤ 2 ^ 200 := by omega
  have hn := nextEmptyPtr_toNat hb64
  exact le_trans (emptyEncodedWords_mono hm.active hb64)
    (rawReturnWords_mono (emptyEncoded_heap hm hb64).active (by omega))

theorem depositCallWords_mono {aw ptr} (ha : ActiveWords aw)
    (hb : ptr.toNat + 32 ≤ 2 ^ 200) : aw.toNat ≤ (depositCallWords aw ptr).toNat := by
  exact le_trans (expandedWords_mono ha hb)
    (expandedWords_mono (activeWords_expand32 ha hb) (by change _ + 4 ≤ _; omega))

theorem callWords1_mono {aw ptr} (ha : ActiveWords aw)
    (hb : ptr.toNat + 36 ≤ 2 ^ 200) : aw.toNat ≤ (callWords1 aw ptr).toNat := by
  have hp : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  unfold callWords1
  rw [expandedWords32_chain ha (by omega) (by omega)]
  exact expandedWords_mono ha (by change _ + 32 ≤ _; omega)

theorem callWords2_mono {aw ptr} (ha : ActiveWords aw)
    (hb : ptr.toNat + 68 ≤ 2 ^ 200) : aw.toNat ≤ (callWords2 aw ptr).toNat := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 :=
    addWord_toNat ptr ⟨36⟩ (by change ptr.toNat + 36 < 2 ^ 256; omega)
  unfold callWords2
  rw [expandedWords32_chain ha (by omega) (by omega),
    expandedWords32_chain ha (by omega) (by omega)]
  exact expandedWords_mono ha (by change _ + 32 ≤ _; omega)

theorem burnCallWords_mono {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 36 ≤ 2 ^ 200) : aw.toNat ≤ (burnCallWords aw ptr).toNat :=
  le_trans (callWords1_mono hm.active hb)
    (expandedWords_mono (callMem1_heap hm burnWord ⟨0⟩ hb).active hb)

theorem nounTransferCallWords_mono {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 100 ≤ 2 ^ 200) : aw.toNat ≤ (nounTransferCallWords aw ptr).toNat := by
  have hb68 : ptr.toNat + 68 ≤ 2 ^ 200 := by omega
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 :=
    addWord_toNat ptr ⟨68⟩ (by change ptr.toNat + 68 < 2 ^ 256; omega)
  have hg := expandedWords_mono (callMem2_heap hm transferFromWord ⟨0⟩ ⟨0⟩ hb68).active
    (off := ptr + ⟨68⟩) (size := ⟨32⟩) (by change _ + 32 ≤ _; omega)
  exact le_trans (le_trans (callWords2_mono hm.active hb68) hg)
    (expandedWords_mono (callMem3_heap hm transferFromWord ⟨0⟩ ⟨0⟩ ⟨0⟩ hb).active hb)

theorem transferFinalWords_mono {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 68 ≤ 2 ^ 200) : aw.toNat ≤ (transferFinalWords aw ptr).toNat := by
  have ha := (callMem2_heap hm transferWord ⟨0⟩ ⟨0⟩ hb).active
  have ho : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  exact le_trans (le_trans (callWords2_mono hm.active hb) (callActiveWords_mono ha hb ho))
    (expandedWords_mono (callActiveWords_active ha hb ho) ho)

end Auction
