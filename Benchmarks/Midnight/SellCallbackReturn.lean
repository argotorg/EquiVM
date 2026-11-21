import Benchmarks.Midnight.SellCallbackMagic
import Benchmarks.Midnight.RepayCallbackReturn
import Benchmarks.Midnight.FundingBudget

/-! Buyer callback reply decoding and acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightSellCallbackReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root budgetRoot : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (success : Bool)
    (hstack : R.length + 11 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64) (hlower : 832 ≤ root.toNat)
    (hsize : root.toNat + 32 ≤ mem.size)
    (hb : success = true → TransferBudget budgetRoot credit
      (wordReplyMemory mem out root) aw C)
    (rd : RD midnightBytecode I g s0 ⟨13631⟩
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R)
      (wordReplyMemory mem out root) aw out σ k C) :
    ((success = false ∨ out.size < 32 ∨ calldataWord out 0 ≠ flashLoanMagic) ∧
      RDrev midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧ calldataWord out 0 = flashLoanMagic ∧
      ∃ aw' k' C',
        TransferBudget budgetRoot credit
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' C' ∧
        RD midnightBytecode I g s0 ⟨13665⟩ R
          (flashLoanCallbackResultMemory (wordReplyMemory mem out root) root) aw' out σ k' C') := by
  rcases midnightSellCallbackDecode success hstack hout hroot (by omega)
      (by rw [wordReplyMemory_size _ _ _ hsize]; exact hsize)
      (wordReplyMemory_load mem out root hsize) hb rd with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨hbad.imp_right Or.inl, hrev⟩
  · rcases midnightSellCallbackMagic (by omega) hb1 rd1 with
      ⟨hbad, hrev⟩ | ⟨he, aw2, k2, C2, hb2, rd2⟩
    · exact Or.inl ⟨Or.inr (Or.inr hbad), hrev⟩
    · exact Or.inr ⟨htrue, h32, he, aw2, k2, C2, hb2, rd2⟩

end Benchmarks.Midnight
