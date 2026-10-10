import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Balance storage operations and wrapping arithmetic for ERC20 updates. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def balanceSlot (owner : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)

def balanceWord (evm : State) (owner : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceSlot owner)

def balanceStore (evm : State) (owner : AccountAddress) (value : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (balanceSlot owner) value

def balanceDebitState (evm : State) (owner : AccountAddress) (value : UInt256) : State :=
  balanceStore evm owner (UInt256.sub (balanceWord evm owner) value)

def balanceMoveState (evm : State) (sender recipient : AccountAddress) (value : UInt256) : State :=
  let debited := balanceDebitState evm sender value
  balanceStore debited recipient (balanceWord debited recipient + value)

-- LIBRARY CANDIDATE: explicit uint256 casts wrap addition in an arbitrary frame.
theorem wrappingAddSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.cast (.binary .add lhs rhs)
      (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (uint256Value (a + b)) := by
  have hm := signedAddWrap a b (Int.ofNat b.toNat) (normalizeInt_uint256_word b)
  rw [u256_add_comm b a] at hm
  simp only [evalExpr?, ha, hb, uint256Value, bind, EvalResult.bind, evalBinaryOp?,
    castValue?, normalizeInt, EvalResult.ofOption]
  exact congrArg (fun i ↦ EvalResult.ok (Value.int i)) hm

-- LIBRARY CANDIDATE: explicit uint256 casts wrap subtraction, including underflow.
theorem wrappingSubSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.cast (.binary .sub lhs rhs)
      (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (uint256Value (UInt256.sub a b)) := by
  have hm := signedSubWrap a b (Int.ofNat b.toNat) (normalizeInt_uint256_word b)
  simp only [evalExpr?, ha, hb, uint256Value, bind, EvalResult.bind, evalBinaryOp?,
    castValue?, normalizeInt, EvalResult.ofOption]
  exact congrArg (fun i ↦ EvalResult.ok (Value.int i)) hm

theorem evalStorage_balance (evm : State) (locals imms : Store) (name : Ident)
    (owner : AccountAddress) (hbase : locals.get? "_balances" = none)
    (howner : locals.get? name = some (.address owner)) :
    evalExpr? config ⟨contract, locals, imms⟩ evm
      (.storage ⟨"_balances", [.mindex (.var name)]⟩) =
      .ok (uint256Value (balanceWord evm owner)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"_balances", [.mindex (.address owner)]⟩) (t := .int (.uint ⟨256, by decide⟩))
    hbase (evalStorageRef_addressIndex "_balances" name owner howner) rfl rfl
    (loc := uint256Loc (balanceSlot owner))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address owner))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact storageLocLoad_uint256 evm _

theorem assignStorage_balance (evm : State) (locals imms : Store) (name : Ident)
    (owner : AccountAddress) (value : UInt256) (hbase : locals.get? "_balances" = none)
    (howner : locals.get? name = some (.address owner)) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"_balances", [.mindex (.var name)]⟩ (uint256Value value) =
      .ok (⟨contract, locals, imms⟩, balanceStore evm owner value) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"_balances", [.mindex (.address owner)]⟩)
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) hbase
    (evalStorageRef_addressIndex "_balances" name owner howner) rfl rfl
    (loc := uint256Loc (balanceSlot owner))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.address owner))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ value

end Benchmarks.Morpho.MetaMorphoV1_1
