import Benchmarks.EAS.EAS.RevokeIdentityControl
import Benchmarks.EAS.EAS.RevokeStatusControl
import Benchmarks.EAS.EAS.RevokeGuards

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easRevokeGuards {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell request idx word schema : UInt256} {revoker : AccountAddress} {R : List UInt256}
    (v : EASImmutables) (kind : RevokeKind) (hstack : R.length+11 ≤ 1024)
    (hs : SourceState s0 ee σ evm) (hp : memLoad cell mem = request) (hw : memLoad request mem = word)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.uidPC
      (cell::idx::revokeGuardTail kind schema (UInt256.ofNat revoker.val) R) mem aw rdata σ k C) :
    if revokeGuardsValid (storedAttestationRecord evm word) schema revoker then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.writePC
        (revokeWriteStack kind request idx (dbSlot word) schema (UInt256.ofNat revoker.val) R)
        (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  let a := storedAttestationRecord evm word
  have huWord : a.uid = solcSlotWord σ ee (dbSlot word) := hs.storageRead _
  have hsWord : a.schema = solcSlotWord σ ee (dbSlot word+⟨1⟩) := hs.storageRead _
  have htWord : a.revocationTime = UInt256.land (UInt256.shiftRight
      (solcSlotWord σ ee (dbSlot word+⟨2⟩)) ⟨128⟩) ⟨18446744073709551615⟩ := by
    change UInt256.land (UInt256.shiftRight (EVM.storageLoad evm evm.executionEnv.codeOwner _) _) _ = _
    rw [hs.storageRead]
  have haWord : UInt256.ofNat a.attester.val = UInt256.land (solcSlotWord σ ee (dbSlot word+⟨5⟩)) solcAddrMask := by
    have h := congrArg (fun ws : List UInt256 => ws[7]!) (storedAttestationRecord_words evm word)
    change UInt256.ofNat a.attester.val = UInt256.land (solcSlotWord evm.accountMap evm.executionEnv (dbSlot word+⟨5⟩)) solcAddrMask at h
    simpa only [hs.env,← hs.accounts] using h
  have hai : UInt256.land (solcSlotWord σ ee (dbSlot word+⟨5⟩)) solcAddrMask =
      UInt256.land (UInt256.ofNat revoker.val) solcAddrMask ↔ a.attester = revoker := by
    rw [show UInt256.land (UInt256.ofNat revoker.val) solcAddrMask = UInt256.ofNat revoker.val from addressWord_val_clean revoker,← haWord]
    constructor
    · intro h; simpa only [accountAddress_roundtrip] using congrArg AccountAddress.ofUInt256 h
    · intro h; rw [h]
  have hbi : UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (dbSlot word+⟨5⟩)) ⟨160⟩) ⟨255⟩ ≠ ⟨0⟩ ↔ a.revocable = true := by
    change _ ↔ (!(decide (UInt256.land (UInt256.shiftRight (EVM.storageLoad evm evm.executionEnv.codeOwner _) _) _ = ⟨0⟩))) = true
    rw [hs.storageRead]
    simp only [Bool.not_eq_true',decide_eq_false_iff_not]
  have h0 := easRevokeUIDCheck v kind (by cases kind <;> simp only [revokeGuardTail,List.length_cons] <;> omega) hp hw rd
  rw [← huWord] at h0
  by_cases hu : a.uid ≠ ⟨0⟩
  · rw [if_pos hu] at h0
    obtain ⟨aw1,k1,C1,rd1⟩ := h0
    have h1 := easRevokeSchemaCheck v kind (by omega) rd1
    rw [← hsWord] at h1
    by_cases hschema : a.schema = schema
    · rw [if_pos hschema] at h1
      obtain ⟨aw2,k2,C2,rd2⟩ := h1
      have h2 := easRevokeAttesterCheck v kind hstack rd2
      by_cases hattester : a.attester = revoker
      · rw [if_pos (hai.mpr hattester)] at h2
        obtain ⟨aw3,k3,C3,rd3⟩ := h2
        have h3 := easRevokeRevocableCheck v kind
          (by cases kind <;> simp only [revokePermissionStack,List.length_cons] <;> omega) rd3
        by_cases hrevocable : a.revocable = true
        · rw [if_pos (hbi.mpr hrevocable)] at h3
          obtain ⟨aw4,k4,C4,rd4⟩ := h3
          have h4 := easRevokeTimeCheck v kind hstack rd4
          rw [← htWord] at h4
          by_cases htime : a.revocationTime = ⟨0⟩
          · rw [if_pos ⟨hu,hschema,hattester,hrevocable,htime⟩]
            simpa only [if_pos htime] using h4
          · rw [if_neg (fun h => htime h.2.2.2.2)]
            simpa only [if_neg htime] using h4
        · rw [if_neg (fun h => hrevocable h.2.2.2.1)]
          simpa only [if_neg (fun h => hrevocable (hbi.mp h))] using h3
      · rw [if_neg (fun h => hattester h.2.2.1)]
        simpa only [if_neg (fun h => hattester (hai.mp h))] using h2
    · rw [if_neg (fun h => hschema h.2.1)]
      simpa only [if_neg hschema] using h1
  · rw [if_neg (fun h => hu h.1)]
    simpa only [if_neg hu] using h0

end Benchmarks.EAS.EAS
