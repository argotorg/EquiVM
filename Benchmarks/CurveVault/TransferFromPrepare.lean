import Benchmarks.CurveVault.TransferFromApprove
import Benchmarks.CurveVault.AllowanceMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultTransferFromRawMemory (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) : ByteArray :=
  let first := wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 192) mem) mem)
  let hashed := wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64) first)
    (wordAt32Mem (UInt256.ofNat I.source.val) first)
  (codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) hashed)).toByteArray.write 0 hashed 256 32

theorem vaultTransferFromRawMemory_eq {I : ExecutionEnv} {σ : AccountMap} {mem : ByteArray}
    {sender old : UInt256} (hsize : 256 ≤ mem.size)
    (hmf : memLoad (UInt256.ofNat 192) mem = sender) (hcanon : sender.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
      (vaultAllowanceSlot (AccountAddress.ofNat sender.toNat) I.source) = old) :
    vaultTransferFromRawMemory I σ mem =
      old.toByteArray.write 0 (vaultApproveHashMemory mem sender (UInt256.ofNat I.source.val)) 256 32 := by
  exact vaultAllowanceRawMemory_eq (by omega) hmf hcanon hold

theorem vaultTransferFromPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender old : UInt256} {R : List UInt256}
    (hsize : 256 ≤ mem.size) (hmf : memLoad (UInt256.ofNat 192) mem = sender)
    (hcanon : sender.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
      (vaultAllowanceSlot (AccountAddress.ofNat sender.toNat) I.source) = old)
    (hperm : I.perm = true) (hstack : R.length + 4 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C) :
    ∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      288 ≤ mem'.size ∧ WordMemoryRange mem mem' 192 256 ∧
      memLoad (UInt256.ofNat 256) mem' = old ∧
      RD fork vaultBytecode I g s0
        (if old = UInt256.ofNat (UInt256.size - 1) then UInt256.ofNat 5845 else UInt256.ofNat 5804)
        R mem' aw' rdata (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
  let scratch := vaultTransferFromRawMemory I σ mem
  have hm := vaultTransferFromRawMemory_eq hsize hmf hcanon hold
  change scratch = old.toByteArray.write 0 (vaultApproveHashMemory mem sender (UInt256.ofNat I.source.val)) 256 32 at hm
  have hgap : 256 - (vaultApproveHashMemory mem sender (UInt256.ofNat I.source.val)).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by omega))
  have hs : 288 ≤ scratch.size := by
    rw [hm]
    exact toByteArray_write_size_ge_off_add32 _ _ 256 hgap
  have hframe : WordMemoryRange mem scratch 192 256 := by
    rw [hm]
    exact (wordMemoryRange_vyperHash mem ⟨12⟩ sender 192 256 (by omega)).trans
      ((wordMemoryRange_vyperHash _ _ (UInt256.ofNat I.source.val) 192 256 (by omega)).trans
        (wordMemoryRange_write _ old 256 192 256 hgap (Or.inl (le_refl _))))
  have hread : memLoad (UInt256.ofNat 256) scratch = old := by
    rw [hm]
    exact memLoad_write_back _ _ 256 (by decide +kernel) hgap
  have hc : UInt256.eq (memLoad (UInt256.ofNat 256) scratch) (UInt256.ofNat (UInt256.size - 1)) =
      UInt256.eq old (UInt256.ofNat (UInt256.size - 1)) := by rw [hread]
  have rd : ∃ aw' k' C', RD fork vaultBytecode I g s0
      (if old = UInt256.ofNat (UInt256.size - 1) then UInt256.ofNat 5845 else UInt256.ofNat 5804)
      R scratch aw' rdata (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
    by_cases hmax : old = UInt256.ofNat (UInt256.size - 1)
    · rw [if_pos hmax]
      exact vaultBlocks.vault_block_5726_taken_packed hstack hperm
        (ne_of_eq_of_ne hc (by rw [hmax, u256_eq_refl]; decide +kernel)) (by native_decide) h
    · rw [if_neg hmax]
      exact vaultBlocks.vault_block_5726_fallthrough_packed hstack hperm (hc.trans (u256_eq_of_ne hmax)) h
  obtain ⟨aw', k', C', hrd⟩ := rd
  exact ⟨scratch, aw', k', C', hs, hframe, hread, hrd⟩

end Benchmarks.CurveVault
