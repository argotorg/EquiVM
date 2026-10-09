import Benchmarks.CompoundIII.Comet.TokenBalanceCall
import Benchmarks.CompoundIII.Comet.CallWordMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def tokenBalanceSelectorWord : UInt256 := UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩

def tokenBalanceInputMemory (mem : ByteArray) (ptr : UInt256)
    (owner : AccountAddress) : ByteArray :=
  callWordMemory mem ptr tokenBalanceSelectorWord (EVM.word owner.val)

theorem tokenBalanceInputMemory_payload {mem : ByteArray} {ptr : UInt256} {owner : AccountAddress}
    (hb : ptr.toNat + 36 < UInt256.size) :
    (tokenBalanceInputMemory mem ptr owner).readWithPadding ptr.toNat 36 =
      tokenBalancePayload owner := by
  have hr := callWordMemory_payload (mem := mem) (ptr := ptr)
    (selector := tokenBalanceSelectorWord) (arg := EVM.word owner.val) hb
  have hsel : tokenBalanceSelectorWord.toByteArray.extract 0 4 =
      ByteArray.mk #[112, 160, 130, 49] := by decide +kernel
  rw [hsel, toByteArray_eq_toBytesBE] at hr
  exact hr.trans (by
    apply ByteArray.ext
    simp only [ByteArray.data_append, tokenBalancePayload, List.append_toArray])

def tokenBalanceCopyMemory (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) : ByteArray :=
  callOutputMem (tokenBalanceInputMemory mem ptr owner) out ptr ⟨32⟩

def tokenBalanceReturnMemory (mem : ByteArray) (ptr : UInt256) (owner : AccountAddress)
    (out : ByteArray) : ByteArray :=
  writeWord (tokenBalanceCopyMemory mem ptr owner out) 64 (ptr + ⟨32⟩)

theorem tokenBalanceCopyMemory_size {mem out : ByteArray} {ptr : UInt256} {owner : AccountAddress}
    (hb : ptr.toNat + 36 < UInt256.size) (hhi : out.size < UInt256.size) :
    (tokenBalanceCopyMemory mem ptr owner out).size = max mem.size (ptr.toNat + 36) := by
  unfold tokenBalanceCopyMemory tokenBalanceInputMemory
  rw [callOutput32_size _ _ _ hhi (by rw [callWordMemory_size hb]; omega), callWordMemory_size hb]

theorem tokenBalanceReturnMemory_size {mem out : ByteArray} {ptr : UInt256} {owner : AccountAddress}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 36 < UInt256.size) (hhi : out.size < UInt256.size) :
    (tokenBalanceReturnMemory mem ptr owner out).size = max mem.size (ptr.toNat + 36) := by
  rw [tokenBalanceReturnMemory, writeWord_sparse_size, tokenBalanceCopyMemory_size hb hhi]
  omega

theorem tokenBalanceReturnMemory_word {mem out : ByteArray} {ptr : UInt256} {owner : AccountAddress}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 36 < UInt256.size)
    (hsize : 32 ≤ out.size) (hhi : out.size < UInt256.size) :
    memLoad ptr (tokenBalanceReturnMemory mem ptr owner out) = calldataWord out 0 := by
  apply loadedWord_of_read
  · rw [tokenBalanceReturnMemory_size hlo hb hhi]
    omega
  · rw [tokenBalanceReturnMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by omega, by rw [tokenBalanceCopyMemory_size hb hhi]; omega⟩)]
    exact callOutput32_read_word _ _ _ hhi hsize (by
      unfold tokenBalanceInputMemory
      rw [callWordMemory_size hb]
      omega)

end Benchmarks.CompoundIII.Comet
