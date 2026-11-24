import Benchmarks.CurveVault.AllowanceMemory
import Benchmarks.CurveVault.AllowanceSpendSites

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitAllowanceFlow (isWithdraw : Bool) : VaultAllowanceSpendFlow :=
  if isWithdraw then .withdraw else .redeem

theorem vaultDebitAllowancePrepare (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner old : UInt256} {R : List UInt256}
    (hsize : 640 ≤ mem.size) (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I σ (vaultAllowanceSlot (AccountAddress.ofNat owner.toNat) I.source) = old)
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isWithdraw then 4431 else 5104)) R mem aw rdata σ k C) :
    ∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      (vaultDebitAllowanceFlow isWithdraw).allowanceOffset + 32 ≤ mem'.size ∧
      WordMemoryRange mem mem' 192 (vaultDebitAllowanceFlow isWithdraw).allowanceOffset ∧
      memLoad (UInt256.ofNat (vaultDebitAllowanceFlow isWithdraw).allowanceOffset) mem' = old ∧
      RD fork vaultBytecode I g s0
        (UInt256.ofNat (if old = UInt256.ofNat (UInt256.size - 1)
          then (vaultDebitAllowanceFlow isWithdraw).next else (vaultDebitAllowanceFlow isWithdraw).entry))
        R mem' aw' rdata σ k' C' := by
  let off := (vaultDebitAllowanceFlow isWithdraw).allowanceOffset
  let scratch := vaultAllowanceRawMemory I σ mem 608 off
  have hm := vaultAllowanceRawMemory_eq (allowanceOffset := off) (by omega) hmo hcanon hold
  change scratch = old.toByteArray.write 0 (vaultApproveHashMemory mem owner (UInt256.ofNat I.source.val)) off 32 at hm
  have hgap : off - (vaultApproveHashMemory mem owner (UInt256.ofNat I.source.val)).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by cases isWithdraw <;> exact lt_usize _ (by decide +kernel))
  have hs : off + 32 ≤ scratch.size := by
    rw [hm]
    exact toByteArray_write_size_ge_off_add32 _ _ off hgap
  have hframe : WordMemoryRange mem scratch 192 off := by
    rw [hm]
    exact (wordMemoryRange_vyperHash mem ⟨12⟩ owner 192 off (by omega)).trans
      ((wordMemoryRange_vyperHash _ _ (UInt256.ofNat I.source.val) 192 off (by omega)).trans
        (wordMemoryRange_write _ old off 192 off hgap (Or.inl (le_refl _))))
  have hread : memLoad (UInt256.ofNat off) scratch = old := by
    rw [hm]
    exact memLoad_write_back _ _ off (by cases isWithdraw <;> decide +kernel) hgap
  have hrd : ∃ aw' k' C', RD fork vaultBytecode I g s0
      (UInt256.ofNat (if old = UInt256.ofNat (UInt256.size - 1)
        then (vaultDebitAllowanceFlow isWithdraw).next else (vaultDebitAllowanceFlow isWithdraw).entry))
      R scratch aw' rdata σ k' C' := by
    by_cases hmax : old = UInt256.ofNat (UInt256.size - 1)
    · rw [if_pos hmax]
      have hc : UInt256.eq (memLoad (UInt256.ofNat off) scratch) (UInt256.ofNat (UInt256.size - 1)) ≠ ⟨0⟩ := by
        rw [hread, hmax, u256_eq_refl]; decide +kernel
      cases isWithdraw
      · exact vaultBlocks.vault_block_5104_taken_packed hstack hc (by native_decide) h
      · exact vaultBlocks.vault_block_4431_taken_packed hstack hc (by native_decide) h
    · rw [if_neg hmax]
      have hc : UInt256.eq (memLoad (UInt256.ofNat off) scratch) (UInt256.ofNat (UInt256.size - 1)) = ⟨0⟩ := by
        rw [hread]; exact u256_eq_of_ne hmax
      cases isWithdraw
      · exact vaultBlocks.vault_block_5104_fallthrough_packed hstack hc h
      · exact vaultBlocks.vault_block_4431_fallthrough_packed hstack hc h
  obtain ⟨aw', k', C', rd⟩ := hrd
  exact ⟨scratch, aw', k', C', hs, hframe, hread, rd⟩

end Benchmarks.CurveVault
