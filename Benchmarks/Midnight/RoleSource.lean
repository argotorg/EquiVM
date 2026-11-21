import Benchmarks.Midnight.AdminSource

/-! Authorization against the configured role-address slots. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def roleAllowed (evm : EVM.State) (slot : UInt256) : Prop :=
  solcSourceWord evm.executionEnv = UInt256.land
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask

instance (evm : EVM.State) (slot : UInt256) : Decidable (roleAllowed evm slot) := inferInstanceAs (Decidable (_ = _))

def roleGuard (name : Ident) : Expr := .binary .eq (.env .caller) (.storage { base := name })

theorem evalRoleGuard {frame : Frame} (evm : EVM.State) (name : Ident) (slot : UInt256)
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? name = none)
    (hty : storageTypeAt? contract.storage { base := name } = some (.elem .address))
    (hloc : midnightStorageLayout { base := name } = some (.leaf (addressOffset0Loc slot))) :
    evalExpr? config frame evm (roleGuard name) = .ok (.bool (decide (roleAllowed evm slot))) := by
  have hread : evalExpr? config frame evm (.storage { base := name }) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) := by
    apply evalExpr_storage_scalar_value (loc := addressOffset0Loc slot)
      (er := { base := name }) (t := .address) hbase
      (by simp [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind])
      (by rw [hcontract]; exact hty) rfl hloc (storageLocLoad_address_offset0 evm slot)
  rw [show roleGuard name = .binary .eq (.env .caller) (.storage { base := name }) from rfl,
    evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and) (by decide : BinaryOp.eq ≠ .or)]
  simp only [evalExpr?, envValue, hread, bind, pure, EvalResult.bind, evalBinaryOp?,
    Reasoning.VyperDispatch.value_address_beq]
  simp only [sourceAddress_eq_iff evm.executionEnv _ (solcAddrMask_result_canonical _)]
  rfl

end Benchmarks.Midnight
