import Benchmarks.CurveVault.AllowanceAdjustSource
import Benchmarks.CurveVault.AllowanceAdjustMemory
import Benchmarks.CurveVault.AddressWord
import Benchmarks.CurveVault.RuntimeBlocks_021
import Benchmarks.CurveVault.RuntimeBlocks_022

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAdjustEntryPc (increase : Bool) : UInt256 := if increase then UInt256.ofNat 6036 else UInt256.ofNat 6209
def vaultAdjustClampPc (increase : Bool) : UInt256 := if increase then UInt256.ofNat 6095 else UInt256.ofNat 6268
def vaultAdjustFinishPc (increase : Bool) : UInt256 := if increase then UInt256.ofNat 6132 else UInt256.ofNat 6273

def vaultAdjustRawMemory (increase : Bool) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) : ByteArray :=
  let hashed := vaultAllowanceRawHashMemory mem (UInt256.ofNat I.source.val)
  let old := codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) hashed)
  let cached := old.toByteArray.write 0 hashed 224 32
  (vaultAdjustWrapped increase (memLoad (UInt256.ofNat 224) cached) (calldataWord I.calldata 36)).toByteArray.write 0 cached 256 32

theorem vaultAdjustRawMemory_eq (increase : Bool) {I : ExecutionEnv} {σ : AccountMap} {mem : ByteArray}
    {spender old : UInt256} (hsize : 224 ≤ mem.size)
    (hspender : memLoad (UInt256.ofNat 192) mem = spender) (hcanon : spender.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
      (vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat)) = old) :
    vaultAdjustRawMemory increase I σ mem = vaultAdjustMemory mem (UInt256.ofNat I.source.val) spender old
      (vaultAdjustWrapped increase old (calldataWord I.calldata 36)) := by
  have hh := vaultAllowanceRawHashMemory_eq hsize (addressWord_canonical I.source) hspender
  have hs0 : (wordAt0Mem ⟨12⟩ (wordAt32Mem (UInt256.ofNat I.source.val) mem)).size = mem.size := by
    rw [wordAt0Mem_size_of_ge64 _ (by rw [wordAt32Mem_size_of_ge_64 _ (by omega)]; omega),
      wordAt32Mem_size_of_ge_64 _ (by omega)]
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) (vaultAllowanceRawHashMemory mem (UInt256.ofNat I.source.val)) =
      vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat) := by
    rw [hh]
    unfold vaultApproveHashMemory
    rw [vyperHashMem_address _ _ _ (by rw [hs0]; omega) hcanon, addressWord_roundtrip]
    rfl
  dsimp only [vaultAdjustRawMemory]
  rw [hslot, hold]
  rw [memLoad_write_back _ _ 224 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by omega))), hh]
  rfl

theorem vaultAdjustCondition (increase : Bool) (old value : UInt256) :
    UInt256.isZero (UInt256.lt (if increase then value else old) (if increase then old else value)) =
      if vaultAdjustOverflow increase old value then ⟨0⟩ else ⟨1⟩ := by
  cases increase <;> simp only [vaultAdjustOverflow, Bool.false_eq_true, if_true, if_false]
  · by_cases hlt : old.toNat < value.toNat
    · rw [ult_one hlt]; simp only [hlt, decide_true, if_true]; rfl
    · rw [ult_zero (by omega)]; simp only [hlt, decide_false, Bool.false_eq_true, if_false]; rfl
  · by_cases hlt : value.toNat < old.toNat
    · rw [ult_one hlt]; simp only [hlt, decide_true, if_true]; rfl
    · rw [ult_zero (by omega)]; simp only [hlt, decide_false, Bool.false_eq_true, if_false]; rfl

theorem vaultAdjustPrepare (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {spender old : UInt256} {R : List UInt256}
    (hsize : 224 ≤ mem.size) (hspender : memLoad (UInt256.ofNat 192) mem = spender)
    (hcanon : spender.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩)
      (vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat)) = old)
    (hperm : I.perm = true) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustEntryPc increase) R mem aw rdata σ k C) :
    ∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      288 ≤ mem'.size ∧ memLoad (UInt256.ofNat 192) mem' = spender ∧
      memLoad (UInt256.ofNat 224) mem' = old ∧
      memLoad (UInt256.ofNat 256) mem' = vaultAdjustValue increase old (calldataWord I.calldata 36) ∧
      RD fork vaultBytecode I g s0 (vaultAdjustFinishPc increase) R mem' aw' rdata
        (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
  let value := vaultAdjustWrapped increase old (calldataWord I.calldata 36)
  let scratch := vaultAdjustRawMemory increase I σ mem
  have hm := vaultAdjustRawMemory_eq increase hsize hspender hcanon hold
  obtain ⟨hsize', hms, hmc, hmv⟩ := vaultAdjustMemory_reads (owner := UInt256.ofNat I.source.val) old value hsize hspender
  rw [← hm] at hsize' hms hmc hmv
  change 288 ≤ scratch.size at hsize'
  have hc : UInt256.isZero (UInt256.lt
      (if increase then memLoad (UInt256.ofNat 256) scratch else memLoad (UInt256.ofNat 224) scratch)
      (if increase then memLoad (UInt256.ofNat 224) scratch else memLoad (UInt256.ofNat 256) scratch)) =
      if vaultAdjustOverflow increase old value then ⟨0⟩ else ⟨1⟩ := by
    rw [hmc, hmv]
    exact vaultAdjustCondition _ _ _
  by_cases hover : vaultAdjustOverflow increase old value = true
  · have hc0 : UInt256.isZero (UInt256.lt
        (if increase then memLoad (UInt256.ofNat 256) scratch else memLoad (UInt256.ofNat 224) scratch)
        (if increase then memLoad (UInt256.ofNat 224) scratch else memLoad (UInt256.ofNat 256) scratch)) = ⟨0⟩ := by
      rw [hc, hover]; rfl
    have rdClamp : ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultAdjustClampPc increase) R scratch aw' rdata
        (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
      cases increase
      · exact vaultBlocks.vault_block_6209_fallthrough_packed (by omega) hperm hc0 h
      · exact vaultBlocks.vault_block_6036_fallthrough_packed (by omega) hperm hc0 h
    obtain ⟨aw1, k1, C1, rd⟩ := rdClamp
    have rdFinish : ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultAdjustFinishPc increase) R
        ((vaultAdjustBound increase).toByteArray.write 0 scratch 256 32) aw' rdata
        (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
      cases increase
      · exact vaultBlocks.vault_block_6268_packed (by omega) rd
      · exact vaultBlocks.vault_block_6095_packed (by omega) rd
    obtain ⟨aw2, k2, C2, rd⟩ := rdFinish
    have hgap : 256 - scratch.size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by omega))
    refine ⟨_, aw2, k2, C2, toByteArray_write_size_ge_off_add32 _ _ 256 hgap, ?_, ?_, ?_, rd⟩
    · rw [memLoad_below_write _ _ 256 192 (by omega) (by omega) hgap (by decide +kernel), hms]
    · rw [memLoad_below_write _ _ 256 224 (by omega) (by omega) hgap (by decide +kernel), hmc]
    · rw [memLoad_write_back _ _ 256 (by decide +kernel) hgap]
      simp only [vaultAdjustValue, show vaultAdjustOverflow increase old (vaultAdjustWrapped increase old (calldataWord I.calldata 36)) = true from hover, if_true]
  · have hover' : vaultAdjustOverflow increase old value = false := by simpa using hover
    have hc1 : UInt256.isZero (UInt256.lt
        (if increase then memLoad (UInt256.ofNat 256) scratch else memLoad (UInt256.ofNat 224) scratch)
        (if increase then memLoad (UInt256.ofNat 224) scratch else memLoad (UInt256.ofNat 256) scratch)) ≠ ⟨0⟩ := by
      rw [hc, hover']; decide +kernel
    have rdFinish : ∃ aw' k' C', RD fork vaultBytecode I g s0 (vaultAdjustFinishPc increase) R scratch aw' rdata
        (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩) k' C' := by
      cases increase
      · exact vaultBlocks.vault_block_6209_taken_packed (by omega) hperm hc1 (by native_decide) h
      · exact vaultBlocks.vault_block_6036_taken_packed (by omega) hperm hc1 (by native_decide) h
    obtain ⟨aw2, k2, C2, rd⟩ := rdFinish
    refine ⟨scratch, aw2, k2, C2, hsize', hms, hmc, ?_, rd⟩
    simpa only [vaultAdjustValue, show vaultAdjustOverflow increase old (vaultAdjustWrapped increase old (calldataWord I.calldata 36)) = false from hover', Bool.false_eq_true, if_false] using hmv

end Benchmarks.CurveVault
