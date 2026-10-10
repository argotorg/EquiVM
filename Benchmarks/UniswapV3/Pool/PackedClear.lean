import Benchmarks.UniswapV3.Pool.PackedPrefixStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def clearPackedPrefix (evm : EVM.State) (slot : UInt256) (bits : Nat) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner slot
    (packedPrefixWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩ bits)

theorem clearPackedPrefix_full (evm : EVM.State) (slot : UInt256) :
    clearPackedPrefix evm slot 256 = EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩ := by
  have hw : packedPrefixWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩ 256 =
      (⟨0⟩ : UInt256) := by
    unfold packedPrefixWord
    have hb := (EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
    change (EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256 at hb
    rw [Nat.div_eq_of_lt hb]
    rfl
  exact congrArg (EVM.storageStore evm evm.executionEnv.codeOwner slot) hw

-- LIBRARY CANDIDATE: clearing the first packed field starts a zero prefix.
theorem storageLocStore_clearLow (evm : EVM.State) (loc : StorageLoc)
    (hoff : loc.offset.val = 0) (hbit : loc.bitOffset = none) :
    storageLocStore evm loc (.int 0) = some (clearPackedPrefix evm loc.slot (8 * loc.size.val)) := by
  apply storageLocStore_packed_of_toNat evm loc (.int 0) ⟨0⟩ _ rfl hbit
  rw [packedPrefixWord_toNat _ ⟨0⟩ _ (by have h := loc.size.isLt; omega)
    (by change 0 < 2 ^ (8 * loc.size.val); positivity)]
  simp only [hoff, show (⟨0⟩ : UInt256).toNat = 0 from rfl, pow_zero,
    Nat.mod_one, Nat.zero_mod, Nat.one_mul, Nat.zero_add, Nat.add_zero,
    show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

-- LIBRARY CANDIDATE: clearing an adjacent field extends a zero prefix.
theorem storageLocStore_clearMore (evm : EVM.State) (loc : StorageLoc)
    (hbit : loc.bitOffset = none) :
    storageLocStore (clearPackedPrefix evm loc.slot (8 * loc.offset.val)) loc (.int 0) =
      some (clearPackedPrefix evm loc.slot (8 * (loc.offset.val + loc.size.val))) := by
  apply storageLocStore_extendPrefix evm loc (.int 0) ⟨0⟩ ⟨0⟩ ⟨0⟩ rfl hbit
  · change 0 < 2 ^ (8 * loc.offset.val)
    positivity
  · simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_mod, Nat.mul_zero,
      Nat.zero_add]

-- GENERALIZES the fixed-type clear lemmas in Reasoning.PackedStorage.
theorem solidityClearStorage_elem {layout : StorageLayout} {evm evm' : EVM.State}
    {er : EvaledStorageRef} {ty : ABI.ElemType} {loc : StorageLoc}
    (hloc : layout er = some (.leaf loc))
    (hstore : storageLocStore evm loc (.int 0) = some evm') :
    solidityClearStorage? layout evm er (.elem ty) = .ok evm' := by
  simp only [solidityClearStorage?, solidityLeafLoc?_of_leaf hloc, hstore,
    EvalResult.ofOption, bind, EvalResult.bind]

end Benchmarks.UniswapV3.Pool
