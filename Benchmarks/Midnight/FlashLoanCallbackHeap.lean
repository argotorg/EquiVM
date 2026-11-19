import Benchmarks.Midnight.FlashLoanCallbackMagic
import Benchmarks.Midnight.TransferHeap
import Benchmarks.Midnight.WordReplyMemory

/-! The heap invariant after decoding the callback's one-word acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanCallbackResultMemory (mem : ByteArray) (root : UInt256) : ByteArray :=
  flashLoanMagicMemory (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32)))

theorem flashLoanCallbackResultMemory_heap {mem : ByteArray} {aw root : UInt256} {C : Nat}
    (hroot : root.toNat + 32 < UInt256.size) (hlower : 128 ≤ root.toNat)
    (hsize : root.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (ha : MemoryFunding (transferHeapCredit root + 4)
      (flashLoanCallbackResultMemory mem root) aw C) :
    TransferHeap (flashLoanCallbackResultMemory mem root) aw (root + UInt256.ofNat 32) C := by
  have hn : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ hroot
  have hs : (writeWord mem 64 (root + UInt256.ofNat 32)).size = mem.size := by
    rw [writeWord_sparse_size]
    omega
  have hs1 : (flashLoanMagicMemory (writeWord mem 64 (root + UInt256.ofNat 32))).size =
      mem.size := by
    rw [flashLoanMagicMemory_size _ (by rw [hs]; omega), hs]
  have hs2 : (flashLoanCallbackResultMemory mem root).size = mem.size := by
    rw [flashLoanCallbackResultMemory, flashLoanMagicMemory_size _ (by rw [hs1]; omega), hs1]
  have hread (read : UInt256) (hlo : 32 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
      memLoad read (flashLoanCallbackResultMemory mem root) =
        memLoad read (writeWord mem 64 (root + UInt256.ofNat 32)) := by
    rw [flashLoanCallbackResultMemory, flashLoanMagicMemory_load _ _ hlo (by rw [hs1]; exact hin),
      flashLoanMagicMemory_load _ _ hlo (by rw [hs]; exact hin)]
  have halign' : (root + UInt256.ofNat 32).toNat % 32 = 0 := by rw [hn]; omega
  refine ⟨by rw [hs2]; omega, by rw [hn]; omega, ?_, ?_, ?_, halign', ?_⟩
  · rw [hread _ (by decide) (by change 64 + 32 ≤ mem.size; omega)]
    exact memLoad_writeWord mem (UInt256.ofNat 64) _
  · rw [hread _ (by decide) (by change 96 + 32 ≤ mem.size; omega),
      memLoad_writeWord_preserved _ _ _ _ (by change 96 + 32 ≤ mem.size; omega)
        (Or.inr (by decide)), hzero]
  · have hc := ha.covered
    change (flashLoanCallbackResultMemory mem root).size ≤ 32 * aw.toNat at hc
    rw [hs2] at hc
    rw [hn]
    omega
  · exact ha.weaken (transferHeapCredit_grows (by rw [hn]; omega) halign halign'
      (by rw [hn]; omega))

theorem midnightFlashLoanCallbackReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (success : Bool) (hstack : R.length + 11 ≤ 1024)
    (hout : out.size < UInt256.size) (hroot : root.toNat + 32 < 2^64)
    (hlower : 128 ≤ root.toNat) (hsize : root.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (ha : success = true → MemoryFunding (transferHeapCredit root + 4)
      (wordReplyMemory mem out root) aw C)
    (rd : RD midnightBytecode I g s0 ⟨16368⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R)
      (wordReplyMemory mem out root) aw out σ k C) :
    ((success = false ∨ out.size < 32 ∨ calldataWord out 0 ≠ flashLoanMagic) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ calldataWord out 0 = flashLoanMagic ∧
      ∃ aw' k' C',
        TransferHeap (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root)
          aw' (root + UInt256.ofNat 32) C' ∧
        RD midnightBytecode I g s0 ⟨16403⟩ (⟨0⟩ :: R)
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' out σ k' C') := by
  cases success with
  | false =>
    have rd1 := midnightBlocks.midnight_block_16368_taken
      (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd
    have hn := UInt256.toNat_ofNat_of_lt hout
    exact Or.inl ⟨Or.inl rfl, midnightBlocks.midnight_block_13748
      (by simp only [List.length_cons]; omega)
      (by rw [hn]; change 0 + out.size ≤ out.size; omega) rd1⟩
  | true =>
    rcases midnightFlashLoanCallbackDecode true hstack hout hroot hlower
        (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize)
        (wordReplyMemory_load mem out root hsize) (ha rfl) rd with
      ⟨hfail, hrev⟩ | ⟨_, h32, aw1, k1, C1, ha1, rd1⟩
    · rcases hfail with hfalse | hshort
      · cases hfalse
      · exact Or.inl ⟨Or.inr (Or.inl hshort), hrev⟩
    · rcases midnightFlashLoanCallbackMagic (by omega) ha1 rd1 with
        ⟨hbad, hrev⟩ | ⟨he, aw2, k2, C2, ha2, rd2⟩
      · exact Or.inl ⟨Or.inr (Or.inr hbad), hrev⟩
      · refine Or.inr ⟨rfl, h32, he, aw2, k2, C2, ?_, rd2⟩
        apply flashLoanCallbackResultMemory_heap (by change _ < 2^256; omega) hlower
          (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize) ?_ halign ha2
        rw [wordReplyMemory_load_before _ _ _ _ hsize (by change 96 + 32 ≤ root.toNat; omega),
          hzero]

end Benchmarks.Midnight
