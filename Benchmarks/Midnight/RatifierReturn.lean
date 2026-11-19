import Benchmarks.Midnight.RatifierDecode
import Benchmarks.Midnight.RepayCallbackReturn

/-! Ratifier acknowledgement validation, with the decoded reply's memory funding retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightRatifierMagic {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw value : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11391⟩ (value :: flashLoanMagic :: R)
      mem aw out σ k C) :
    (value ≠ flashLoanMagic ∧ RDrev midnightBytecode g s0) ∨
    (value = flashLoanMagic ∧ ∃ aw' k' C',
      MemoryFunding credit (flashLoanMagicMemory mem) aw' C' ∧
      RD midnightBytecode I g s0 ⟨11413⟩ R
        (flashLoanMagicMemory mem) aw' out σ k' C') := by
  have hm : memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32) = flashLoanMagic := by
    rw [flashLoanMagic_copy, flashLoanMagic_load]
  by_cases he : value = flashLoanMagic
  · have rd1 := midnightBlocks.midnight_block_11391_fallthrough hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) = ⟨0⟩
          rw [hm]; exact u256_sub_eq_zero_iff_eq.mpr he) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_11391_fallthrough_memory
      memory_fund ha)
    have hf := And.intro ha1 rd1
    simp only [midnightBlocks.midnight_block_11391_fallthrough_stack,
      midnightBlocks.midnight_block_11391_fallthrough_memory,
      show (UInt256.ofNat 24513).toNat = 24513 from rfl,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, flashLoanMagic_copy] at hf
    exact Or.inr ⟨he, _, _, _, hf⟩
  · have rd1 := midnightBlocks.midnight_block_11391_taken hstack
      (by change UInt256.sub value (memLoad ⟨0⟩ (midnightBytecode.write 24513 mem 0 32)) ≠ ⟨0⟩
          rw [hm]; exact fun h ↦ he (u256_sub_eq_zero_iff_eq.mp h)) (by jump_dest) rd
    exact Or.inl ⟨he, midnightBlocks.midnight_block_14781
      (by change R.length + 2 ≤ 1024; omega) rd1⟩

theorem midnightRatifierReturn {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (success : Bool) (hstack : R.length + 11 ≤ 1024)
    (hout : out.size < UInt256.size) (hroot : root.toNat + 32 < 2^64)
    (hlower : 128 ≤ root.toNat) (hsize : root.toNat + 32 ≤ mem.size)
    (ha : MemoryFunding credit (wordReplyMemory mem out root) aw C)
    (rd : RD midnightBytecode I g s0 ⟨11379⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R)
      (wordReplyMemory mem out root) aw out σ k C) :
    ((success = false ∨ out.size < 32 ∨ calldataWord out 0 ≠ flashLoanMagic) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ calldataWord out 0 = flashLoanMagic ∧
      ∃ aw' k' C',
        MemoryFunding credit
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' C' ∧
        RD midnightBytecode I g s0 ⟨11413⟩ R
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' out σ k' C') := by
  rcases midnightRatifierDecode success hstack hout hroot hlower
      (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize)
      (wordReplyMemory_load mem out root hsize) ha rd with
    ⟨hfail, hrev⟩ | ⟨hs, h32, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨hfail.imp_right Or.inl, hrev⟩
  · rcases midnightRatifierMagic (by omega) ha1 rd1 with
      ⟨hbad, hrev⟩ | ⟨he, aw2, k2, C2, ha2, rd2⟩
    · exact Or.inl ⟨Or.inr (Or.inr hbad), hrev⟩
    · exact Or.inr ⟨hs, h32, he, aw2, k2, C2, ha2, rd2⟩

end Benchmarks.Midnight
