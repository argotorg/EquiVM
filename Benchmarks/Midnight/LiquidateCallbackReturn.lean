import Benchmarks.Midnight.LiquidateCallbackMagic
import Benchmarks.Midnight.RepayCallbackReturn

/-! Liquidation's callback acknowledgement preserves its heap for the loan-token pull. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallbackReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (success : Bool) (hstack : R.length + 11 ≤ 1024)
    (hout : out.size < UInt256.size) (hroot : root.toNat + 32 < 2^64)
    (hlower : 832 ≤ root.toNat) (hsize : root.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (ha : success = true → MemoryFunding (transferHeapCredit root + 4)
      (wordReplyMemory mem out root) aw C)
    (rd : RD midnightBytecode I g s0 ⟨6228⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R)
      (wordReplyMemory mem out root) aw out σ k C) :
    ((success = false ∨ out.size < 32 ∨ calldataWord out 0 ≠ flashLoanMagic) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ calldataWord out 0 = flashLoanMagic ∧
      ∃ aw' k' C',
        TransferHeap (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root)
          aw' (root + UInt256.ofNat 32) C' ∧
        RD midnightBytecode I g s0 ⟨6265⟩ R
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' out σ k' C') := by
  have hz1 : memLoad (UInt256.ofNat 800) (wordReplyMemory mem out root) = ⟨0⟩ := by
    rw [wordReplyMemory_load_before _ _ _ _ hsize (by exact hlower), hz]
  rcases midnightLiquidateCallbackDecode success hstack hout hroot (by omega)
      (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize) hz1
      (wordReplyMemory_load mem out root hsize) ha rd with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨hbad.imp_right Or.inl, hrev⟩
  · rcases midnightLiquidateCallbackMagic (by omega) ha1 rd1 with
      ⟨hbad, hrev⟩ | ⟨he, aw2, k2, C2, ha2, rd2⟩
    · exact Or.inl ⟨Or.inr (Or.inr hbad), hrev⟩
    · refine Or.inr ⟨htrue, h32, he, aw2, k2, C2, ?_, rd2⟩
      apply flashLoanCallbackResultMemory_heap (by change _ < 2^256; omega)
        (by omega) (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize)
        _ halign ha2
      rw [wordReplyMemory_load_before _ _ _ _ hsize (by change 128 ≤ root.toNat; omega), hzero]

end Benchmarks.Midnight
