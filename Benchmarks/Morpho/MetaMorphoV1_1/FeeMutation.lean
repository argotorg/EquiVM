import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! The low twelve-byte fee assignment preserves the packed recipient address. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setFeeWord (old data : UInt256) : UInt256 :=
  UInt256.ofNat (data.toNat % 2 ^ 96 + old.toNat / 2 ^ 96 * 2 ^ 96)

theorem setFeeWord_toNat (old data : UInt256) :
    (setFeeWord old data).toNat =
      data.toNat % 2 ^ 96 + old.toNat / 2 ^ 96 * 2 ^ 96 := by
  apply UInt256.toNat_ofNat_of_lt
  have hw : old.toNat < 2 ^ 256 := old.val.isLt
  have hd := Nat.mod_lt data.toNat (by decide : 0 < 2 ^ 96)
  change _ < 2 ^ 256
  omega

theorem setFeeWord_bytecode (old data : UInt256) :
    UInt256.lor (UInt256.land data (UInt256.ofNat (2 ^ 96 - 1)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ 96 - 1))) old) =
      setFeeWord old data := by
  apply u256_inj
  rw [u256_lor_toNat_exact, uland_toNat, u256_land_comm, uland_toNat]
  change Nat.lor (Nat.land data.toNat (2 ^ 96 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 96)) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 96 (by decide) old.val.isLt,
    nat_lor_shift_add _ _ 96 (Nat.mod_lt _ (by decide)), setFeeWord_toNat]

theorem storageLocStore_fee (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm
      { slot := slot, offset := 0, size := 12, hbound := by decide,
        type := .int (.uint ⟨96, by decide⟩) }
      (uint256Value data) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setFeeWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof data).1.take 12 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 12) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE,
    setFeeWord_toNat]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof data).2]
  change data.toNat % 2 ^ 96 + 2 ^ 96 * (_ / 2 ^ 96) = _
  omega

def setFeeState (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨18⟩
    (setFeeWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩) value)

theorem assignStorage_fee (evm : EVM.State) (locals imms : Store)
    (value : UInt256) (hbase : locals.get? "fee" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage ⟨"fee", []⟩
      (uint256Value value) = .ok (⟨contract, locals, imms⟩, setFeeState evm value) := by
  exact assignStorageRef_storage_scalar_value (er := ⟨"fee", []⟩)
    (ty := .elem (.int (.uint ⟨96, by decide⟩))) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
    rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_fee evm ⟨18⟩ value)

end Benchmarks.Morpho.MetaMorphoV1_1
