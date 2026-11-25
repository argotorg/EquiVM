import Benchmarks.Midnight.ReturnData
import Benchmarks.Midnight.MemoryPrefix
import Reasoning.HeapMemory
import Reasoning.ABIComposite

/-! The allocated return-data header, its first word, and preservation of caller memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem returnDataMem_properties {mem out : ByteArray} {ptr : UInt256}
    (hm : 96 ≤ mem.size) (hl : 96 ≤ ptr.toNat) (hn : out.size ≠ 0)
    (hb : ptr.toNat + 32 < UInt256.size) :
    (returnDataMem mem out ptr).size = max mem.size (ptr.toNat + 32 + out.size) ∧
    memLoad (UInt256.ofNat 64) (returnDataMem mem out ptr) = returnDataPtr ptr out.size ∧
    memLoad ptr (returnDataMem mem out ptr) = UInt256.ofNat out.size ∧
    (32 ≤ out.size → memLoad (ptr + UInt256.ofNat 32) (returnDataMem mem out ptr) =
      calldataWord out 0) := by
  let m0 := writeWord mem 64 (returnDataPtr ptr out.size)
  let m1 := writeWord m0 ptr.toNat (UInt256.ofNat out.size)
  have hs0 : m0.size = mem.size := by
    rw [show m0 = writeWord mem 64 (returnDataPtr ptr out.size) from rfl, writeWord_sparse_size]
    omega
  have hs1 : m1.size = max mem.size (ptr.toNat + 32) := by
    rw [show m1 = writeWord m0 ptr.toNat (UInt256.ofNat out.size) from rfl,
      writeWord_sparse_size, hs0]
  have hs : (returnDataMem mem out ptr).size = max mem.size (ptr.toNat + 32 + out.size) := by
    change (out.write 0 m1 (ptr.toNat + 32) out.size).size = _
    rw [writeBytes_size _ _ _ hn (by rw [hs1]; omega), hs1]
    omega
  have hread (off : Nat) (ho : off + 32 ≤ ptr.toNat + 32) :
      (returnDataMem mem out ptr).readWithPadding off 32 = m1.readWithPadding off 32 :=
    write_read_below_gen_extend out m1 (ptr.toNat + 32) out.size off hn le_rfl
      (by rw [hs1]; omega) ho
  refine ⟨hs, ?_, ?_, ?_⟩
  · apply mloadWordValue_of_readWithPadding
    · change 64 < _; rw [hs]; omega
    · change (returnDataMem mem out ptr).readWithPadding 64 32 = _
      rw [hread 64 (by omega)]
      dsimp only [m1]
      rw [writeWord_sparse_read_preserved _ ptr.toNat 64 _
        (Or.inl ⟨hl, by rw [hs0]; exact hm⟩)]
      exact writeWord_sparse_read_back mem 64 _
  · apply mloadWordValue_of_readWithPadding (by rw [hs]; omega)
    rw [hread ptr.toNat le_rfl]
    exact writeWord_sparse_read_back m0 ptr.toNat _
  · intro hw
    have hp := uadd_word_ofNat_toNat ptr 32 hb
    apply mloadWordValue_of_readWithPadding (by rw [hs, hp]; omega)
    rw [hp, calldataWord_bytes hw]
    exact byteArray_write_prefix32 out m1 (ptr.toNat + 32) hw (by rw [hs1]; omega)

theorem memoryPrefix_writeBytes (out mem : ByteArray) (dest limit : Nat)
    (hn : out.size ≠ 0) (hdest : dest ≤ mem.size) (hbelow : limit ≤ dest) :
    MemoryPrefix mem (out.write 0 mem dest out.size) limit := by
  refine ⟨by rw [writeBytes_size _ _ _ hn hdest]; omega, fun off _ hlim _ ↦ ?_⟩
  exact write_read_below_gen_extend out mem dest out.size off hn le_rfl hdest (by omega)

theorem returnDataMem_prefix {mem out : ByteArray} {ptr : UInt256} (hn : out.size ≠ 0) :
    MemoryPrefix mem (returnDataMem mem out ptr) ptr.toNat := by
  refine (memoryPrefix_writeWord mem 64 ptr.toNat (returnDataPtr ptr out.size)
    (Or.inr (by decide))).trans
    ((memoryPrefix_writeWord _ ptr.toNat ptr.toNat (UInt256.ofNat out.size)
      (Or.inl le_rfl)).trans ?_)
  apply memoryPrefix_writeBytes out _ (ptr.toNat + 32) ptr.toNat hn
  · rw [writeWord_sparse_size]; omega
  · omega

end Benchmarks.Midnight
