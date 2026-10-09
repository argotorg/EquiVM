import Benchmarks.Safe.Authorization
import Benchmarks.Safe.Storage
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def fallbackHandlerArgs (handler : UInt256) : Store :=
  (∅ : Store).insert "handler" (.address (AccountAddress.ofNat handler.toNat))

def fallbackHandlerFrame (handler : UInt256) : Frame :=
  { contract := contract, locals := fallbackHandlerArgs handler }

theorem safeEvalHandler (evm : EVM.State) (handler : UInt256) :
    evalExpr? config (fallbackHandlerFrame handler) evm (.var "handler") =
      .ok (.address (AccountAddress.ofNat handler.toNat)) := by
  simp [fallbackHandlerFrame, fallbackHandlerArgs, evalExpr?, EvalResult.ofOption]

theorem safeHandlerGuard (evm : EVM.State) (handler : UInt256) :
    evalExpr? config (fallbackHandlerFrame handler) evm (neE (.var "handler") this) =
      .ok (.bool (decide (AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner))) := by
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), safeEvalHandler]
  simp [this, evalExpr?, envValue, evalBinaryOpNeAddress, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]

theorem safeAssignFallbackHandler (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus) :
    assignStorageRef? config (fallbackHandlerFrame handler) evm .storage fallbackHandlerRef
      (.address (AccountAddress.ofNat handler.toNat)) =
      .ok (fallbackHandlerFrame handler,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot handler) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "_fallbackHandler" })
    (loc := wordLoc fallbackHandlerSlot .address)
  · simp [fallbackHandlerFrame, fallbackHandlerArgs, fallbackHandlerRef]
  · simp [evalStorageRef, evalStorageRefSteps, fallbackHandlerRef,
      EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨.address, rfl⟩
  · exact storageLocStore_bytes32 evm fallbackHandlerSlot handler _
      (valueToWord_address_ofNat_canonical handler hcanon)

theorem safeInternalSetFallbackHandlerSource (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner) :
    ExecFuncBody config (fallbackHandlerFrame handler) evm internalSetFallbackHandlerFunction.body
      (.returned (fallbackHandlerFrame handler)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot handler) none)
          := by
  exact .execBlockOK (.consNormal (.requireTrue (by simpa [hne] using safeHandlerGuard evm handler))
    (.consNormal (.assign (safeEvalHandler evm handler)
      (safeAssignFallbackHandler evm handler hcanon)) .nil))

theorem safeInternalSetFallbackHandlerStatic (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (fallbackHandlerFrame handler) evm internalSetFallbackHandlerFunction.body
      .staticViolation := by
  exact .execBlockStatic
    (.consNormal (.requireTrue (by simpa [hne] using safeHandlerGuard evm handler))
      (.consStatic (.assignStatic (safeEvalHandler evm handler)
        (safeAssignFallbackHandler evm handler hcanon) hperm)))

theorem safeInternalSetFallbackHandlerRevert (evm : EVM.State) (handler : UInt256)
    (heq : AccountAddress.ofNat handler.toNat = evm.executionEnv.codeOwner) :
    ExecFuncBody config (fallbackHandlerFrame handler) evm internalSetFallbackHandlerFunction.body
      .reverted := by
  exact .execBlockRevert (.consRevert (.requireFalse
    (by simpa [heq] using safeHandlerGuard evm handler)))

theorem safeInternalFallbackTrace {I g s0 σ k C aw mem rdata} {handler ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8283⟩ (handler :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret R mem aw rdata
      (sstoreAccountMap I.codeOwner σ fallbackHandlerSlot handler) k' C' :=
  safeRuntime_block_8283 hov hperm hret h

theorem safeInternalFallbackTraceStatic {I g s0 σ k C aw mem rdata} {handler : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8283⟩ (handler :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hdest := h.jumpdest (by native_decide) (by simp; omega)
  have hslot := RD.pushConst (width := 32) (op := .PUSH32) hdest fallbackHandlerSlot
    (by decide) (by native_decide) (by simp; omega)
  exact hslot.sstoreStatic hperm (by native_decide) (by omega)

theorem safeInternalFallbackTraceRevert {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8267⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h6898 := safeRuntime_block_8267 (by omega) (by jump_dest) h
  exact safeRuntime_block_6898 (by simp; omega) h6898

end Benchmarks.Safe
