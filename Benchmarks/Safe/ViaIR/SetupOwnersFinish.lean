import Benchmarks.Safe.ViaIR.SetupOwnersStore

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

-- GENERALIZES safeAssignThreshold to any caller locals without a shadowing binding.
theorem safeAssignThresholdLocals (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage thresholdRef
      (uint256Value value) = .ok ({ contract := contract, locals := locals },
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "threshold" })
    (loc := uint256Loc ⟨4⟩)
  · exact hb
  · simp [evalStorageRef, evalStorageRefSteps, thresholdRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm ⟨4⟩ value

def setupOwnersFinishState (p : SetupOwnersInput) (evm : EVM.State)
    (current : UInt256) : EVM.State :=
  let evm₁ := writeOwnerLink evm current ⟨1⟩
  let evm₂ := Stele.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner ⟨3⟩
    (UInt256.ofNat p.owners.length)
  Stele.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨4⟩ p.threshold

theorem safeSetupOwnersFinishSource (evm : EVM.State) {p locals i current}
    (hl : SetupOwnersLocals p locals i current) (hc : current.toNat < EVM.addressModulus)
    (hn : p.owners.length < UInt256.size)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := locals } evm
      (setupOwnersFunction.body.drop 7)
      (.ok { contract := contract, locals := locals } (setupOwnersFinishState p evm current)) := by
  have hfirst := safeAssignOwnerLink evm locals (.var "currentOwner") current ⟨1⟩
    hl.ownersAbsent hc (by decide) (evalLocalValue hl.current)
  have hlen : evalExpr? config { contract := contract, locals := locals }
      (writeOwnerLink evm current ⟨1⟩) (.var "ownersLength") =
      .ok (uint256Value (UInt256.ofNat p.owners.length)) := by
    rw [uint256Value, ulit_toNat' _ hn]
    exact evalLocalValue hl.length
  exact .consNormal (.assign (hperm := Or.inr hperm) (safeEvalOwnerSentinel evm locals) hfirst)
    (.consNormal (.assign (hperm := Or.inr (by simpa only [writeOwnerLink, storageStore_executionEnv] using hperm)) hlen (safeAssignOwnerCount _ locals _ hl.countAbsent))
      (.consNormal (.assign (hperm := Or.inr (by simpa only [writeOwnerLink, storageStore_executionEnv] using hperm)) (evalLocalValue hl.threshold)
        (safeAssignThresholdLocals _ locals _ hl.thresholdAbsent)) .nil))

theorem setupOwnersFinishState_accounts (p : SetupOwnersInput) (evm : EVM.State)
    (current : UInt256) :
    (setupOwnersFinishState p evm current).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (sstoreAccountMap evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (mapSlot current ⟨2⟩)
            (setAddressOffset0Word (solcSlotWordAt (mapSlot current ⟨2⟩)
              evm.accountMap evm.executionEnv) ⟨1⟩)) ⟨3⟩ (UInt256.ofNat p.owners.length))
        ⟨4⟩ p.threshold := by
  simp only [setupOwnersFinishState, storageStore_accountMap, storageStore_executionEnv,
    writeOwnerLink, storageLoad_eq_solcSlotWord]
  rfl

set_option maxRecDepth 2000 in
theorem safeSetupOwnersFinishTrace (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata i}
    {current src handler len dataStart target token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3341⟩
      (src :: i :: current :: p.threshold :: handler :: handler :: len :: dataStart :: target ::
        target :: token :: receiver :: payment :: UInt256.ofNat p.owners.length :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hc : current.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 (if handler = ⟨0⟩ then ⟨3401⟩ else ⟨3671⟩)
      (handler :: len :: dataStart :: ⟨3409⟩ :: target :: target :: token :: receiver ::
        payment :: ⟨0⟩ :: R) (twoWordHashMem current ⟨2⟩ mem)
      aw' rdata (setupOwnersFinishState p evm current).accountMap k' C' := by
  have hh := twoWordHashMemMapSlotAny current ⟨2⟩ mem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 2).toByteArray.write 0
      (current.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  have hw (word : UInt256) : UInt256.lor (UInt256.land word (UInt256.lnot solcAddrMask))
      (UInt256.ofNat 1) = setAddressOffset0Word word ⟨1⟩ := by
    rw [setAddressOffset0Word]
    congr 1
  rw [setupOwnersFinishState_accounts, hee, hacc]
  by_cases hz : handler = ⟨0⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3341_fallthrough_packed hov hperm hz h
    simp only [safeRuntime_block_3341_fallthrough_stack, safeRuntime_block_3341_fallthrough_memory,
      safeAddressMask, solcAddrMask_clean_left hc, safeAddressHighMask] at h'
    rw [hh] at h'
    simp only [hw] at h'
    exact ⟨aw', k', C', by simpa only [hz, ite_true] using h'⟩
  · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3341_taken_packed hov hperm hz
      (by jump_dest) h
    simp only [safeRuntime_block_3341_taken_stack, safeRuntime_block_3341_taken_memory,
      safeAddressMask, solcAddrMask_clean_left hc, safeAddressHighMask] at h'
    rw [hh] at h'
    simp only [hw] at h'
    exact ⟨aw', k', C', by simpa only [hz, ite_false] using h'⟩

end Benchmarks.Safe.ViaIR
