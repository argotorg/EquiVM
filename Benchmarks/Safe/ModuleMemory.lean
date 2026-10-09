import Benchmarks.Safe.PreModuleTrace
import Benchmarks.Safe.MemoryBytesDecoded
import Benchmarks.Safe.ByteCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES twoWordHashMem_read32_above64 to arbitrary in-bounds read lengths.
theorem twoWordHashRead (key slot : UInt256) (mem : ByteArray) (off count : Nat)
    (hin : off + count ≤ mem.size) (hlo : 64 ≤ off) :
    (twoWordHashMem key slot mem).readWithPadding off count =
      mem.readWithPadding off count := by
  change (writeWord (writeWord mem 0 key) 32 slot).readWithPadding off count = _
  rw [writeWordReadAbove _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
    (by omega), writeWordReadAbove _ _ _ _ _ hin (by omega)]

theorem preModuleReturnRead (mem out : ByteArray) (ptr : UInt256) (off count : Nat)
    (hm : ptr.toNat ≤ mem.size) (hlo : 96 ≤ off) (hhi : off + count ≤ ptr.toNat) :
    (preModuleReturnMemory mem out ptr).readWithPadding off count =
      mem.readWithPadding off count := by
  have hs := byteArray_write_size_ge_base out mem 0 ptr.toNat (min 32 out.size)
  rw [preModuleReturnMemory, writeWordReadAbove _ _ _ _ _ (by
    change off + count ≤ (out.write 0 mem ptr.toNat (min 32 out.size)).size; omega) hlo]
  exact copyWindowReadBelow out mem 0 ptr.toNat (min 32 out.size) off count
    (by simp) hm hhi

def modulePayloadWords (payload : ByteArray) : List UInt256 :=
  memoryWords (memoryBytesDecoded payload) 160 ((payload.size + 31) / 32)

def moduleScratch (payload : ByteArray) (sender : UInt256) : ByteArray :=
  twoWordHashMem sender ⟨1⟩ (memoryBytesDecoded payload)

def moduleGuardMemory (payload : ByteArray) (target value operation sender : UInt256) : ByteArray :=
  preModuleCallMemory (moduleScratch payload sender) (memoryBytesInitialEnd payload.size)
    payload.size target value operation sender (modulePayloadWords payload)

def modulePreMemoryForm (payload : ByteArray) (target value operation sender : UInt256)
    (mem : ByteArray) : Prop :=
  mem = moduleScratch payload sender ∨
    ∃ out, out.size < 2 ^ 138 ∧ mem = preModuleReturnMemory
      (moduleGuardMemory payload target value operation sender) out
      (UInt256.ofNat (memoryBytesInitialEnd payload.size))

theorem moduleScratch_size (payload : ByteArray) (sender : UInt256) :
    (moduleScratch payload sender).size = 192 + payload.size := by
  rw [moduleScratch, twoWordHashMem_size_of_ge64 _ _ (by rw [memoryBytesDecoded_size]; omega),
    memoryBytesDecoded_size]

theorem moduleGuardMemory_size (payload : ByteArray) (target value operation sender : UInt256) :
    (moduleGuardMemory payload target value operation sender).size =
      memoryBytesInitialEnd payload.size + 228 + payload.size := by
  apply preModuleCallMemory_size
  · rw [moduleScratch_size]
    unfold memoryBytesInitialEnd ABI.paddedSize
    omega
  · exact memoryWords_length _ _ _

theorem modulePreMemoryPreserved {payload : ByteArray} {target value operation sender : UInt256}
    {mem : ByteArray} (hn : payload.size ≤ 2 ^ 64 - 192)
    (hm : modulePreMemoryForm payload target value operation sender mem)
    (off count : Nat) (hlo : 96 ≤ off) (hin : off + count ≤ 160 + payload.size) :
    mem.readWithPadding off count = (memoryBytesDecoded payload).readWithPadding off count := by
  have he := memoryBytesInitialEnd_bound hn
  have heNat : (UInt256.ofNat (memoryBytesInitialEnd payload.size)).toNat =
      memoryBytesInitialEnd payload.size := ulit_toNat' _ (lt_trans he (by decide))
  have hi : off + count ≤ memoryBytesInitialEnd payload.size := by
    unfold memoryBytesInitialEnd ABI.paddedSize; omega
  rcases hm with rfl | ⟨out, hout, rfl⟩
  · exact twoWordHashRead _ _ _ _ _ (by rw [memoryBytesDecoded_size]; omega) (by omega)
  rw [preModuleReturnRead _ _ _ _ _ (by rw [heNat, moduleGuardMemory_size]; omega)
      hlo (by rw [heNat]; exact hi)]
  rw [moduleGuardMemory, preModuleCallMemory_preserved _ _ _ _ _ _ _ _ _ _
      (by rw [moduleScratch_size]; omega) hi]
  exact twoWordHashRead _ _ _ _ _ (by rw [memoryBytesDecoded_size]; omega) (by omega)

theorem modulePreMemoryData {payload : ByteArray} {target value operation sender : UInt256}
    {mem : ByteArray} (hn : payload.size ≤ 2 ^ 64 - 192)
    (hm : modulePreMemoryForm payload target value operation sender mem) :
    memLoad ⟨128⟩ mem = UInt256.ofNat payload.size ∧
      mem.readWithPadding 160 payload.size = payload := by
  constructor
  · rw [memLoadReadWord, show (⟨128⟩ : UInt256).toNat = 128 by rfl,
      modulePreMemoryPreserved hn hm 128 32 (by decide) (by omega)]
    exact (memLoadReadWord _ ⟨128⟩).symm.trans (memoryBytesDecoded_length payload)
  · rw [modulePreMemoryPreserved hn hm 160 payload.size (by decide) (by omega),
      memoryBytesDecoded_payload]

theorem modulePreMemoryFree {payload : ByteArray} {target value operation sender : UInt256}
    {mem : ByteArray} (hn : payload.size ≤ 2 ^ 64 - 192)
    (hm : modulePreMemoryForm payload target value operation sender mem) :
    ∃ ptr, memLoad ⟨64⟩ mem = ptr ∧ 96 ≤ mem.size ∧ 96 ≤ ptr.toNat ∧ ptr.toNat < 2 ^ 200 := by
  have he := memoryBytesInitialEnd_bound hn
  have heNat : (UInt256.ofNat (memoryBytesInitialEnd payload.size)).toNat =
      memoryBytesInitialEnd payload.size := ulit_toNat' _ (lt_trans he (by decide))
  have hlo : 160 ≤ memoryBytesInitialEnd payload.size := by unfold memoryBytesInitialEnd; omega
  rcases hm with rfl | ⟨out, hout, rfl⟩
  · refine ⟨UInt256.ofNat (memoryBytesInitialEnd payload.size), ?_, ?_, ?_, ?_⟩
    · rw [moduleScratch, memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl,
        twoWordHashRead _ _ _ _ _ (by rw [memoryBytesDecoded_size]; omega) (by decide)]
      exact (memLoadReadWord _ ⟨64⟩).symm.trans (memoryBytesDecoded_free payload)
    · rw [moduleScratch_size]; omega
    · rw [heNat]; omega
    · rw [heNat]; exact lt_trans he (by decide)
  · refine ⟨preModuleNextPtr (UInt256.ofNat (memoryBytesInitialEnd payload.size)) out,
      preModuleReturnFree _ _ _, preModuleReturnSize (by rw [moduleGuardMemory_size]; omega),
      ?_, ?_⟩
    all_goals
      rw [preModuleNextPtr_toNat (by rw [heNat]; omega), heNat]
      omega

end Benchmarks.Safe
