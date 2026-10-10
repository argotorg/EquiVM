import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Storing the high twenty-byte fee-recipient address preserves the low twelve-byte fee. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setHighAddressWord (old : UInt256) (recipient : AccountAddress) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 96 + recipient.toNat * 2 ^ 96)

theorem setHighAddressWord_toNat (old : UInt256) (recipient : AccountAddress) :
    (setHighAddressWord old recipient).toNat = old.toNat % 2 ^ 96 + recipient.toNat * 2 ^ 96 := by
  apply UInt256.toNat_ofNat_of_lt
  have hlo := Nat.mod_lt old.toNat (by decide : 0 < 2 ^ 96)
  have hhi : recipient.toNat < 2 ^ 160 := recipient.isLt
  change _ < 2 ^ 256
  omega

theorem setHighAddressWord_bytecode (old : UInt256) (recipient : AccountAddress) :
    UInt256.lor (UInt256.land old
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96)) (UInt256.ofNat 1)))
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat recipient.toNat) (UInt256.ofNat 96))
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96))
          (UInt256.ofNat 1)))) = setHighAddressWord old recipient := by
  have hm : UInt256.land
      (UInt256.shiftLeft (UInt256.ofNat recipient.toNat) (UInt256.ofNat 96))
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96))
        (UInt256.ofNat 1))) =
      UInt256.shiftLeft (UInt256.ofNat recipient.toNat) (UInt256.ofNat 96) :=
    addressWord_shiftLeft96_high_mask recipient
  have hr : (UInt256.ofNat recipient.toNat).toNat = recipient.toNat :=
    UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le recipient.isLt (by decide))
  rw [hm]
  apply u256_inj
  rw [u256_lor_toNat_exact, uland_toNat]
  change Nat.lor (Nat.land old.toNat (2 ^ 96 - 1))
    (UInt256.shiftLeft (UInt256.ofNat recipient.toNat) ⟨96⟩).toNat = _
  rw [shiftLeft96_toNat_of_lt_160 (UInt256.ofNat recipient.toNat)
      (addressWord_val_canonical recipient), hr,
    nat_land_mask_eq_mod, nat_lor_shift_add _ _ 96 (Nat.mod_lt _ (by decide)),
    setHighAddressWord_toNat]

theorem storageLocStore_highAddress (evm : EVM.State) (slot : UInt256)
    (recipient : AccountAddress) :
    storageLocStore evm
      { slot := slot, offset := 12, size := 20, hbound := by decide, type := .address }
      (.address recipient) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setHighAddressWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          recipient)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 12 ++
      (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat recipient.toNat)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 32) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setHighAddressWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat recipient.toNat)).2]
  have hr : (UInt256.ofNat recipient.toNat).toNat = recipient.toNat :=
    UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le recipient.isLt (by decide))
  rw [hr]
  change _ % 2 ^ 96 + 2 ^ 96 * (recipient.toNat % 2 ^ 160) +
    2 ^ 256 * (_ / 2 ^ 256) = _
  have ha : recipient.toNat < 2 ^ 160 := recipient.isLt
  have hw : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256 :=
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt hw]
  omega

def setFeeRecipientState (evm : EVM.State) (recipient : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨18⟩
    (setHighAddressWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩) recipient)

theorem assignStorage_feeRecipient (evm : EVM.State) (locals imms : Store)
    (recipient : AccountAddress) (hbase : locals.get? "feeRecipient" = none) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage ⟨"feeRecipient", []⟩
      (.address recipient) =
      .ok (⟨contract, locals, imms⟩, setFeeRecipientState evm recipient) := by
  exact assignStorageRef_storage_scalar_value (er := ⟨"feeRecipient", []⟩)
    (ty := .elem .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
    rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_highAddress evm ⟨18⟩ recipient)

end Benchmarks.Morpho.MetaMorphoV1_1
