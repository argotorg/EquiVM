import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Packed boolean reads and writes for the allocator mapping. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def allocatorSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨11⟩ (UInt256.ofNat addr.val)

def allocatorByte (evm : EVM.State) (addr : AccountAddress) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allocatorSlot addr)) ⟨255⟩

def allocatorBoolWord (evm : EVM.State) (addr : AccountAddress) : UInt256 :=
  UInt256.isZero (UInt256.isZero (allocatorByte evm addr))

def setAllocatorState (evm : EVM.State) (addr : AccountAddress) (flag : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (allocatorSlot addr)
    (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allocatorSlot addr))
      flag)

theorem evalStorage_allocator (evm : EVM.State) (locals imms : Store) (name : Ident)
    (addr : AccountAddress) (hbase : locals.get? "isAllocator" = none)
    (haddr : locals.get? name = some (.address addr)) :
    evalExpr? config ⟨contract, locals, imms⟩ evm
      (.storage ⟨"isAllocator", [.mindex (.var name)]⟩) =
      .ok (wordToElem .bool (allocatorByte evm addr)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"isAllocator", [.mindex (.address addr)]⟩) (t := .bool)
    hbase (evalStorageRef_addressIndex "isAllocator" name addr haddr) rfl rfl
    (loc := boolOffset0Loc (allocatorSlot addr))
  · change some (StorageAddr.leaf (boolOffset0Loc
      (solcMappingSlot ⟨11⟩ (keyValueToWord (.address addr))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact storageLocLoad_bool_offset0 evm _

theorem assignStorage_allocator (evm : EVM.State) (locals imms : Store) (name : Ident)
    (addr : AccountAddress) (flag : UInt256) (hbase : locals.get? "isAllocator" = none)
    (haddr : locals.get? name = some (.address addr)) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"isAllocator", [.mindex (.var name)]⟩ (wordToElem .bool flag) =
      .ok (⟨contract, locals, imms⟩, setAllocatorState evm addr flag) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"isAllocator", [.mindex (.address addr)]⟩) (ty := .elem .bool)
    hbase (evalStorageRef_addressIndex "isAllocator" name addr haddr) rfl rfl
    (loc := boolOffset0Loc (allocatorSlot addr))
  · change some (StorageAddr.leaf (boolOffset0Loc
      (solcMappingSlot ⟨11⟩ (keyValueToWord (.address addr))))) = _
    rw [keyValueToWord_address]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_bool_word_offset0 evm _ flag

set_option maxRecDepth 2000 in
theorem boolWordNeSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (wordToElem .bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (wordToElem .bool b)) :
    evalExpr? cfg frame evm (.binary .ne lhs rhs) =
      .ok (.bool (decide (UInt256.isZero (UInt256.isZero a) ≠
        UInt256.isZero (UInt256.isZero b)))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  have hv (w : UInt256) : w.val = 0 ↔ w = ⟨0⟩ :=
    ⟨fun h ↦ congrArg UInt256.mk h, fun h ↦ congrArg UInt256.val h⟩
  have hn (w : UInt256) : UInt256.isZero (UInt256.isZero w) =
      if w = ⟨0⟩ then ⟨0⟩ else ⟨1⟩ := by
    by_cases hz : w = ⟨0⟩
    · subst w
      decide
    · rw [if_neg hz, isZero_eq_zero_of_ne hz]
      rfl
  rw [hn, hn]
  simp only [bind, EvalResult.bind, wordToElem, beq_iff_eq, hv]
  by_cases hza : a = ⟨0⟩ <;> by_cases hzb : b = ⟨0⟩ <;>
    simp only [hza, hzb, ↓reduceIte] <;> decide

end Benchmarks.Morpho.MetaMorphoV1_1
