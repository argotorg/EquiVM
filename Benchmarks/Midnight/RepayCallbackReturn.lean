import Benchmarks.Midnight.RepayCallbackMagic
import Benchmarks.Midnight.FlashLoanCallbackHeap
import Benchmarks.Midnight.MemoryPrefix

/-! Repayment acknowledgement decoding and preservation of allocated market memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem flashLoanMagicMemory_prefix (mem : ByteArray) (limit : Nat) :
    MemoryPrefix mem (flashLoanMagicMemory mem) limit :=
  (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide)))

theorem callbackResultMemory_prefix (mem : ByteArray) (root : UInt256) (limit : Nat) :
    MemoryPrefix mem (flashLoanCallbackResultMemory mem root) limit :=
  ((memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide))).trans
    (flashLoanMagicMemory_prefix _ _)).trans (flashLoanMagicMemory_prefix _ _)

theorem wordReplyMemory_prefix (mem out : ByteArray) (root : UInt256) (limit : Nat)
    (hsize : root.toNat + 32 ≤ mem.size) (hlimit : limit ≤ root.toNat) :
    MemoryPrefix mem (wordReplyMemory mem out root) limit := by
  refine ⟨by rw [wordReplyMemory_size _ _ _ hsize], fun off _ hlim hin ↦ ?_⟩
  by_cases hz : min 32 out.size = 0
  · simp only [wordReplyMemory, hz, ByteArray.write, if_true]
  · exact copySparse_read_before out mem 0 root.toNat (min 32 out.size) off 32 hz
      (by omega) (by decide) hin (by omega)

theorem callbackResultMemory_size (mem : ByteArray) (root : UInt256) (hsize : 96 ≤ mem.size) :
    (flashLoanCallbackResultMemory mem root).size = mem.size := by
  have hw : (writeWord mem 64 (root + UInt256.ofNat 32)).size = mem.size := by
    rw [writeWord_sparse_size]; omega
  rw [flashLoanCallbackResultMemory, flashLoanMagicMemory_size _ (by
    rw [flashLoanMagicMemory_size _ (by rw [hw]; omega), hw]; omega),
    flashLoanMagicMemory_size _ (by rw [hw]; omega), hw]

theorem callbackResultMemory_free (mem : ByteArray) (root : UInt256) (hsize : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (flashLoanCallbackResultMemory mem root) =
      root + UInt256.ofNat 32 := by
  have hw : 96 ≤ (writeWord mem 64 (root + UInt256.ofNat 32)).size := by
    rw [writeWord_sparse_size]; omega
  rw [flashLoanCallbackResultMemory,
    flashLoanMagicMemory_load _ _ (by decide) (by
      rw [flashLoanMagicMemory_size _ (by omega)]; exact hw),
    flashLoanMagicMemory_load _ (UInt256.ofNat 64) (by decide) (by exact hw)]
  exact memLoad_writeWord mem (UInt256.ofNat 64) _

theorem midnightRepayCallbackReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root budgetRoot : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 11 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64) (hlower : 832 ≤ root.toNat)
    (hsize : root.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : success = true → TransferBudget budgetRoot credit
      (wordReplyMemory mem out root) aw C)
    (rd : RD midnightBytecode I g s0 ⟨10222⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R)
      (wordReplyMemory mem out root) aw out σ k C) :
    ((success = false ∨ out.size < 32 ∨ calldataWord out 0 ≠ flashLoanMagic) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ calldataWord out 0 = flashLoanMagic ∧
      ∃ aw' k' C',
        TransferBudget budgetRoot credit
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' C' ∧
        RD midnightBytecode I g s0 ⟨10259⟩ R
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' out σ k' C') := by
  have hz : memLoad (UInt256.ofNat 800) (wordReplyMemory mem out root) = ⟨0⟩ := by
    rw [wordReplyMemory_load_before _ _ _ _ hsize (by exact hlower), hzero]
  rcases midnightRepayCallbackDecode success hstack hout hroot (by omega)
      (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize) hz
      (wordReplyMemory_load mem out root hsize) hb rd with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨hbad.imp_right Or.inl, hrev⟩
  · rcases midnightRepayCallbackMagic (by omega) hb1 rd1 with
      ⟨hbad, hrev⟩ | ⟨he, aw2, k2, C2, hb2, rd2⟩
    · exact Or.inl ⟨Or.inr (Or.inr hbad), hrev⟩
    · exact Or.inr ⟨htrue, h32, he, aw2, k2, C2, hb2, rd2⟩

end Benchmarks.Midnight
