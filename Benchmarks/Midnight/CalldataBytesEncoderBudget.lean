import Benchmarks.Midnight.CalldataBytesEncoder
import Benchmarks.Midnight.TransferBudget

/-! Calldata bytes encoding with the transfer budget retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataBytesEncoderBudget {budgetRoot : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw len ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hlen : len.toNat < 2^64) (hout : output.toNat + len.toNat + 96 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19711⟩ (ptr :: len :: output :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧
      TransferBudget budgetRoot credit
        (calldataBytesEncodeMemory mem I.calldata output.toNat ptr.toNat len.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ret
        ((output + UInt256.ofNat (returnDataAllocation len.toNat)) :: R)
        (calldataBytesEncodeMemory mem I.calldata output.toNat ptr.toNat len.toNat)
        aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19711 hstack hret rd
  have ha1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1 (by
    rcases ha with hsmall | ⟨halign, ha⟩
    · exact Or.inl hsmall
    refine Or.inr ⟨halign, ?_⟩
    constructor
    · have hp := ha.paid
      simp only [memExpansionCost] at hp ⊢
      omega
    · exact ((ha.covered.write32 len.toByteArray 0 output).write I.calldata ptr.toNat
        (output + UInt256.ofNat 32) len).write32 (⟨0⟩ : UInt256).toByteArray 0
        (UInt256.ofNat 32 + (len + output)))
  have ho : (output + UInt256.ofNat 32).toNat = output.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hz : (UInt256.ofNat 32 + (len + output)).toNat = output.toNat + 32 + len.toNat := by
    rw [u256_add_comm (UInt256.ofNat 32), u256_add_comm len,
      uadd_word_ofNat_toNat _ _ (by
        rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]; omega),
      uadd_toNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have he : (UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (UInt256.ofNat 31 + len) +
        output) + UInt256.ofNat 32 = output + UInt256.ofNat (returnDataAllocation len.toNat) := by
    rw [u256_add_comm _ output, u256_add_assoc,
      u256_add_comm _ (UInt256.ofNat 32), ← u256_ofNat_toNat len,
      returnDataAllocation_word (by change _ < 2^256; omega)]
    rw [u256_ofNat_toNat]
  have hf := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_19711_stack,
    midnightBlocks.midnight_block_19711_memory, he, ho, hz] at hf
  refine ⟨_, _, _, ?_, by
    simpa only [calldataBytesEncodeMemory, copyZeroMemory, Reasoning.Theory.writeWord,
      u256_ofNat_toNat] using hf⟩
  omega

end Benchmarks.Midnight
