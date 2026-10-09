import Benchmarks.Safe.SetupOwnersStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- GENERALIZES safeAssignThreshold to any caller locals without a shadowing binding.
theorem safeAssignThresholdLocals (evm : EVM.State) (locals : Store) (value : UInt256)
    (hb : locals["threshold"]? = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage thresholdRef
      (uint256Value value) = .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) := by
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
  let evm₂ := Solm.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner ⟨3⟩
    (UInt256.ofNat p.owners.length)
  Solm.EVM.storageStore evm₂ evm₂.executionEnv.codeOwner ⟨4⟩ p.threshold

theorem safeSetupOwnersFinishSource (evm : EVM.State) {p locals i current}
    (hl : SetupOwnersLocals p locals i current) (hc : current.toNat < EVM.addressModulus)
    (hn : p.owners.length < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm
      (setupOwnersFunction.body.drop 7)
      (.ok { contract := contract, locals := locals } (setupOwnersFinishState p evm current)) := by
  have hfirst := safeAssignOwnerLink evm locals (.var "currentOwner") current ⟨1⟩
    hl.ownersAbsent hc (by decide) (evalLocalValue hl.current)
  have hlen : evalExpr? config { contract := contract, locals := locals }
      (writeOwnerLink evm current ⟨1⟩) (.var "ownersLength") =
      .ok (uint256Value (UInt256.ofNat p.owners.length)) := by
    rw [uint256Value, ulit_toNat' _ hn]
    exact evalLocalValue hl.length
  exact .consNormal (.assign (safeEvalOwnerSentinel evm locals) hfirst)
    (.consNormal (.assign hlen (safeAssignOwnerCount _ locals _ hl.countAbsent))
      (.consNormal (.assign (evalLocalValue hl.threshold)
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

set_option maxRecDepth 100000 in
theorem safeSetupOwnersFinishTrace (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata i} {current src ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8199⟩
      (i :: UInt256.ofNat p.owners.length :: current :: p.threshold :: src :: ret :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hc : current.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 9 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret R (twoWordHashMem current ⟨2⟩ mem)
      aw' rdata (setupOwnersFinishState p evm current).accountMap k' C' := by
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_8199_packed hov hperm hret h
  simp only [safeRuntime_block_8199_stack, safeRuntime_block_8199_memory, safeAddressMask,
    solcAddrMask_clean hc] at h'
  have hh := twoWordHashMemMapSlotAny current ⟨2⟩ mem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 2).toByteArray.write 0
      (current.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) = _ at hh
  have hw (word : UInt256) : UInt256.lor (UInt256.ofNat 1)
      (UInt256.land (UInt256.lnot solcAddrMask) word) = setAddressOffset0Word word ⟨1⟩ := by
    simpa only [show UInt256.land (⟨1⟩ : UInt256) solcAddrMask = ⟨1⟩ from by decide] using
      maskedAddressStoreWord word ⟨1⟩
  rw [hh] at h'
  simp only [hw] at h'
  rw [setupOwnersFinishState_accounts, hee, hacc]
  exact ⟨aw', k', C', h'⟩

end Benchmarks.Safe
