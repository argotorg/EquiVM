import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `withdraw()` local words, memory, and body facts -/

def withdrawSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def withdrawSenderKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def withdrawPendingSlot (I : ExecutionEnv) : UInt256 :=
  pendingReturnsSlot (withdrawSenderKey I)

def withdrawAmountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (withdrawPendingSlot I) ⟨0⟩)

def withdrawZeroMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (withdrawPendingSlot I) ⟨0⟩

def withdrawRestoreMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (withdrawZeroMap σ I) (withdrawPendingSlot I)
    (withdrawAmountWord σ I)

def withdrawZeroState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (withdrawPendingSlot evm.executionEnv) ⟨0⟩

def withdrawRestoreState (evm : EVM.State) (amount : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (withdrawPendingSlot evm.executionEnv) amount

theorem withdrawZeroState_originalMap (evm : EVM.State) :
    (withdrawZeroState evm).σ₀ = evm.σ₀ := by
  unfold withdrawZeroState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_genesisBlockHeader (evm : EVM.State) :
    (withdrawZeroState evm).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold withdrawZeroState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_blocks (evm : EVM.State) :
    (withdrawZeroState evm).blocks = evm.blocks := by
  unfold withdrawZeroState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawZeroState_substate (evm : EVM.State) :
    (withdrawZeroState evm).substate = evm.substate := by
  unfold withdrawZeroState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

def withdrawAmountStore (amount : UInt256) : Store :=
  (∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))

def withdrawCallStore (amount : UInt256) (success : Bool) (out : ByteArray) : Store :=
  ((withdrawAmountStore amount).insert "success" (.bool success)).insert "_data" (.bytes out)

def withdrawCallFrame (amount : UInt256) (success : Bool) (out : ByteArray) : Frame :=
  { contract := simpleAuctionContract, locals := withdrawCallStore amount success out }

noncomputable def withdrawPendingBaseMem : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def withdrawPendingKeyMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (withdrawSenderWord I)).write 0 solcFreePtrMem 0 32

noncomputable def withdrawPendingHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (withdrawPendingKeyMem I) 32 32

noncomputable def withdrawRehashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
    ((UInt256.toByteArray (withdrawSenderWord I)).write 0 (withdrawPendingHashMem I) 0 32) 32 32

noncomputable def withdrawRestoreHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
    ((UInt256.toByteArray (withdrawSenderWord I)).write 0 (withdrawRehashMem I) 0 32) 32 32

theorem withdrawSenderWord_canonical (I : ExecutionEnv) :
    (withdrawSenderWord I).toNat < EVM.addressModulus := by
  unfold withdrawSenderWord
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt

theorem withdrawKeyValueToWord_sender (I : ExecutionEnv) :
    keyValueToWord (withdrawSenderKey I) = withdrawSenderWord I := by
  unfold withdrawSenderKey withdrawSenderWord keyValueToWord
  apply u256_inj
  simp only [Fin.val_castLE]
  exact (ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide))).symm

theorem withdrawSenderWord_toNat (I : ExecutionEnv) :
    (withdrawSenderWord I).toNat = I.source.val := by
  unfold withdrawSenderWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem withdrawSender_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (withdrawSenderWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [withdrawSenderWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem withdrawPendingSlot_eq (I : ExecutionEnv) :
    withdrawPendingSlot I = simpleAuctionMappingSlot (withdrawSenderWord I) ⟨4⟩ := by
  unfold withdrawPendingSlot pendingReturnsSlot simpleAuctionMappingSlot
  rw [withdrawKeyValueToWord_sender]

theorem withdrawPendingBaseMem_size : withdrawPendingBaseMem.size = 96 := by
  unfold withdrawPendingBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem withdrawPendingHashMem_size (I : ExecutionEnv) : (withdrawPendingHashMem I).size = 96 := by
  unfold withdrawPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by
      unfold withdrawPendingKeyMem
      rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
      norm_num),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, toByteArray_size]
  unfold withdrawPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem withdrawPendingBaseMem_read32 :
    withdrawPendingBaseMem.readWithPadding 32 32 = UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold withdrawPendingBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)]
  rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size ≤ 32
        rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size =
          (UInt256.toByteArray (⟨4⟩ : UInt256)).size from rfl, toByteArray_size]]

theorem withdrawPendingKeyMem_size (I : ExecutionEnv) : (withdrawPendingKeyMem I).size = 96 := by
  unfold withdrawPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem withdrawPendingKeyMem_read0 (I : ExecutionEnv) :
    (withdrawPendingKeyMem I).readWithPadding 0 32 =
      UInt256.toByteArray (withdrawSenderWord I) := by
  unfold withdrawPendingKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [show (UInt256.toByteArray (withdrawSenderWord I)).extract 0 32 =
      UInt256.toByteArray (withdrawSenderWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (withdrawSenderWord I)).data.size ≤ 32
        rw [show (UInt256.toByteArray (withdrawSenderWord I)).data.size =
          (UInt256.toByteArray (withdrawSenderWord I)).size from rfl, toByteArray_size]]

theorem withdrawPendingHashMem_read0_64 (I : ExecutionEnv) :
    (withdrawPendingHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSenderWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold withdrawPendingHashMem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawPendingKeyMem_size]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, withdrawPendingKeyMem_size,
          toByteArray_size]
        norm_num)]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [withdrawPendingKeyMem_size]; omega)]
  have hkey0 :
      (withdrawPendingKeyMem I).extract 0 32 =
        UInt256.toByteArray (withdrawSenderWord I) := by
    rw [← readWithPadding_eq_extract (withdrawPendingKeyMem I) 0
      (by rw [withdrawPendingKeyMem_size]; omega)]
    exact withdrawPendingKeyMem_read0 I
  rw [ByteArray.append_assoc]
  rw [extract_append_span ((withdrawPendingKeyMem I).extract 0 32)
      ((UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 ++
        (withdrawPendingKeyMem I).extract (32 + 32) (withdrawPendingKeyMem I).size)
      0 64
      (by rw [hkey0, toByteArray_size]; omega)
      (by rw [hkey0, toByteArray_size]; omega)]
  rw [hkey0]
  rw [show (UInt256.toByteArray (withdrawSenderWord I)).extract 0
      (UInt256.toByteArray (withdrawSenderWord I)).size =
      UInt256.toByteArray (withdrawSenderWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        exact le_rfl]
  rw [toByteArray_size]
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_extract, toByteArray_size]; norm_num)]
  rw [show 64 - 32 = 32 by norm_num]
  have hslot : (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) := by
      apply ByteArray.ext
      rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
      show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size ≤ 32
      rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size =
        (UInt256.toByteArray (⟨4⟩ : UInt256)).size from rfl, toByteArray_size]
  exact congrArg (fun tail => UInt256.toByteArray (withdrawSenderWord I) ++ tail) (by
    rw [hslot]
    exact hslot)

theorem withdrawPendingHashMem_read64 (I : ExecutionEnv) :
    (withdrawPendingHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawPendingHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [withdrawPendingKeyMem_size]; omega) (by omega) (by rw [withdrawPendingKeyMem_size])]
  unfold withdrawPendingKeyMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega) (by omega) (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem withdrawPendingHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawPendingHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawPendingHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawPendingHashMem_size]; decide) (by decide)
    (withdrawPendingHashMem_read64 I)

theorem withdrawBoolReturnMem_size (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawPendingHashMem I) 128 32).size = 160 := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawPendingHashMem_size]; omega)
      (by rw [withdrawPendingHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, withdrawPendingHashMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem withdrawBoolReturnMem_read64 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawPendingHashMem I) 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawPendingHashMem_size]; omega)
      (by rw [withdrawPendingHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, withdrawPendingHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, withdrawPendingHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    norm_num)]
  rw [extract_append_left (withdrawPendingHashMem I)
      (ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawPendingHashMem I).size))) 64 96
      (by rw [withdrawPendingHashMem_size])]
  rw [← readWithPadding_eq_extract (withdrawPendingHashMem I) 64
    (by rw [withdrawPendingHashMem_size])]
  exact withdrawPendingHashMem_read64 I

theorem withdrawBoolReturnMem_mload64 (I : ExecutionEnv) (b : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          ((UInt256.toByteArray b).write 0 (withdrawPendingHashMem I) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (((UInt256.toByteArray b).write 0 (withdrawPendingHashMem I) 128 32).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawBoolReturnMem_size]; decide) (by decide)
    (withdrawBoolReturnMem_read64 I b)

theorem withdrawBoolReturnMem_read128 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawPendingHashMem I) 128 32).readWithPadding 128 32 =
      UInt256.toByteArray b := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [withdrawBoolReturnMem_size])]
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawPendingHashMem_size]; omega)
      (by rw [withdrawPendingHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (withdrawPendingHashMem I ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawPendingHashMem I).size)))
      (UInt256.toByteArray b) 128 160 (by
        rw [ByteArray.size_append, withdrawPendingHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, withdrawPendingHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray b).size ≤ 32
    rw [toByteArray_size])

theorem withdrawByteArray_extract_self (b : ByteArray) : b.extract 0 b.size = b := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
  exact le_rfl

theorem withdraw_write_len_zero (src base : ByteArray) (sa da : ℕ) :
    src.write sa base da 0 = base := by
  unfold ByteArray.write
  simp

theorem withdraw_readWithPadding_zero (mem : ByteArray) (addr : ℕ) :
    mem.readWithPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : addr ≥ mem.size
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)

theorem withdrawByteArray_eq_empty_of_size_eq_zero (b : ByteArray) (h : b.size = 0) :
    b = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero (by simpa using h)

theorem withdraw_extract_two_chunks_0 (A B C : ByteArray) (hA : A.size = 32)
    (hB : B.size = 32) :
    (A ++ B ++ C).extract 0 64 = A ++ B := by
  rw [extract_append_left (A ++ B) C 0 64 (by rw [ByteArray.size_append, hA, hB])]
  rw [show 64 = (A ++ B).size by rw [ByteArray.size_append, hA, hB]]
  exact withdrawByteArray_extract_self _

-- PROMOTE -> Reasoning.Memory: append-shaped write when RETURNDATACOPY writes at memory end.
theorem withdraw_write_at_end_eq (src base : ByteArray) (len : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) :
    src.write 0 base base.size len = base ++ src.extract 0 len := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (0 ≥ src.size) from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  have hcopy : min len (src.size - 0) = len := by omega
  have htail : min base.size (base.size + len) - (base.size + len) = 0 := by omega
  have hgap : base.size - base.size = 0 := by omega
  rw [hcopy, htail, hgap]
  simp only [Nat.zero_add]
  rw [show (ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize)).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := (⟨↑(0:ℕ)⟩ : USize)) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rfl : base.data.size ≤ base.size)]
  have hcopy2 : min len (src.data.size - 0) = len := by
    have : src.data.size = src.size := rfl
    omega
  rw [hcopy2]
  rw [show base.data.extract (base.size + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    omega]
  simp

def withdrawReturnDataRounded (o : ByteArray) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨63⟩) (UInt256.lnot ⟨31⟩)

def withdrawReturnDataPtr (o : ByteArray) : UInt256 :=
  (⟨128⟩ : UInt256) + withdrawReturnDataRounded o

noncomputable def withdrawReturnDataPtrMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (withdrawReturnDataPtr o)).write 0 (withdrawRehashMem I) 64 32

noncomputable def withdrawReturnDataSizeMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat o.size)).write 0 (withdrawReturnDataPtrMem I o) 128 32

noncomputable def withdrawReturnDataMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (withdrawReturnDataSizeMem I o) 160 o.size

def withdrawReturnDataActiveWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 o.size)

def withdrawReturnDataBoolActiveWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (withdrawReturnDataActiveWords o).toNat
    (withdrawReturnDataPtr o).toNat 32)

noncomputable def withdrawReturnDataBoolMem (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) : ByteArray :=
  (UInt256.toByteArray b).write 0 (withdrawReturnDataMem I o)
    (withdrawReturnDataPtr o).toNat 32

noncomputable def withdrawReturnDataRestoreKeyMem (I : ExecutionEnv) (o : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (withdrawSenderWord I)).write 0 (withdrawReturnDataMem I o) 0 32

noncomputable def withdrawReturnDataRestoreHashMem (I : ExecutionEnv) (o : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (withdrawReturnDataRestoreKeyMem I o) 32 32

noncomputable def withdrawReturnDataRestoreBoolMem (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) : ByteArray :=
  (UInt256.toByteArray b).write 0 (withdrawReturnDataRestoreHashMem I o)
    (withdrawReturnDataPtr o).toNat 32

theorem withdrawReturnDataRounded_le (o : ByteArray) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataRounded o).toNat ≤ o.size + 63 := by
  unfold withdrawReturnDataRounded UInt256.land UInt256.toNat
  refine le_trans (show
      (Fin.land ((UInt256.ofNat o.size + ⟨63⟩).val) (UInt256.lnot ⟨31⟩).val).val ≤
        ((UInt256.ofNat o.size + ⟨63⟩).val).val from by
      simp [Fin.land]
      exact le_trans (Nat.mod_le _ _) (by
        refine Nat.le_of_testBit fun i hi => ?_
        change (((UInt256.ofNat o.size + ⟨63⟩ : UInt256).val.val &&&
            (UInt256.lnot ⟨31⟩).val.val).testBit i = true) at hi
        rw [Nat.testBit_and] at hi
        simp only [Bool.and_eq_true] at hi
        exact hi.1)) ?_
  change ((UInt256.ofNat o.size + ⟨63⟩ : UInt256).toNat) ≤ o.size + 63
  rw [uadd_toNat]
  have hof : (UInt256.ofNat o.size).toNat = o.size := by
    exact UInt256.toNat_ofNat_of_lt (by
      have hpow : 2 ^ 255 < UInt256.size := by norm_num [UInt256.size]
      omega)
  rw [hof]
  exact Nat.mod_le _ _

theorem withdrawReturnDataPtr_toNat_le (o : ByteArray) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataPtr o).toNat ≤ 191 + o.size := by
  have hround := withdrawReturnDataRounded_le o hosz
  unfold withdrawReturnDataPtr
  rw [uadd_toNat]
  have hlt : (⟨128⟩ : UInt256).toNat + (withdrawReturnDataRounded o).toNat < UInt256.size := by
    have hpow : 2 ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  omega

theorem withdrawReturnDataPtr_toNat_ge (o : ByteArray) (hosz : o.size < 2 ^ 255) :
    96 ≤ (withdrawReturnDataPtr o).toNat := by
  unfold withdrawReturnDataPtr
  rw [uadd_toNat]
  have hround := withdrawReturnDataRounded_le o hosz
  have hlt : (⟨128⟩ : UInt256).toNat + (withdrawReturnDataRounded o).toNat < UInt256.size := by
    have hpow : 2 ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  omega

-- PROMOTE -> Reasoning.Memory: read back a 32-byte word write that may extend memory by a gap.
theorem withdraw_toByteArray_write_read_back_of_gap (b : UInt256) (mem : ByteArray) (off : ℕ)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding off 32 =
      UInt256.toByteArray b := by
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact withdrawByteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt' hgap, toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (USize.ofNat (off - mem.size)))
      (UInt256.toByteArray b) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' hgap]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' hgap]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
      rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _]

-- PROMOTE -> Reasoning.Memory: read below a 32-byte word write that may extend memory by a gap.
theorem withdraw_toByteArray_write_read_below_of_gap
    (b : UInt256) (mem : ByteArray) (off read : ℕ)
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below _ _ off read (by rw [toByteArray_size]) hle hbelow
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt' hgap, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' hgap]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

theorem withdrawRehashMem_size (I : ExecutionEnv) : (withdrawRehashMem I).size = 96 := by
  unfold withdrawRehashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size,
        toByteArray_size]
      norm_num),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size, toByteArray_size]
  norm_num

theorem withdrawReturnDataPtrMem_size (I : ExecutionEnv) (o : ByteArray) :
    (withdrawReturnDataPtrMem I o).size = 96 := by
  unfold withdrawReturnDataPtrMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
  norm_num

theorem withdrawReturnDataSizeMem_size (I : ExecutionEnv) (o : ByteArray) :
    (withdrawReturnDataSizeMem I o).size = 160 := by
  unfold withdrawReturnDataSizeMem
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawReturnDataPtrMem_size]; omega)
      (by rw [withdrawReturnDataPtrMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, withdrawReturnDataPtrMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem withdrawReturnDataMem_eq (I : ExecutionEnv) (o : ByteArray) (ho0 : o.size ≠ 0) :
    withdrawReturnDataMem I o = withdrawReturnDataSizeMem I o ++ o := by
  unfold withdrawReturnDataMem
  rw [show 160 = (withdrawReturnDataSizeMem I o).size by rw [withdrawReturnDataSizeMem_size]]
  rw [withdraw_write_at_end_eq o (withdrawReturnDataSizeMem I o) o.size ho0 le_rfl]
  rw [show o.extract 0 o.size = o from withdrawByteArray_extract_self o]

theorem withdrawReturnDataMem_size (I : ExecutionEnv) (o : ByteArray) (ho0 : o.size ≠ 0) :
    (withdrawReturnDataMem I o).size = 160 + o.size := by
  rw [withdrawReturnDataMem_eq I o ho0, ByteArray.size_append, withdrawReturnDataSizeMem_size]

theorem withdrawReturnDataSizeMem_read64 (I : ExecutionEnv) (o : ByteArray) :
    (withdrawReturnDataSizeMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (withdrawReturnDataPtr o) := by
  have hptr :
      (withdrawReturnDataPtrMem I o).readWithPadding 64 32 =
        UInt256.toByteArray (withdrawReturnDataPtr o) := by
    unfold withdrawReturnDataPtrMem
    rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by rw [withdrawRehashMem_size]; omega)]
    rw [show (UInt256.toByteArray (withdrawReturnDataPtr o)).extract 0 32 =
        UInt256.toByteArray (withdrawReturnDataPtr o) from by
      rw [show 32 = (UInt256.toByteArray (withdrawReturnDataPtr o)).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _]
  unfold withdrawReturnDataSizeMem
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawReturnDataPtrMem_size]; omega)
      (by rw [withdrawReturnDataPtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
    rw [ByteArray.size_append, ByteArray.size_append, withdrawReturnDataPtrMem_size,
      ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
      toByteArray_size]
    norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, withdrawReturnDataPtrMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    norm_num)]
  rw [extract_append_left (withdrawReturnDataPtrMem I o)
      (ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawReturnDataPtrMem I o).size))) 64 96
      (by rw [withdrawReturnDataPtrMem_size])]
  rw [← readWithPadding_eq_extract (withdrawReturnDataPtrMem I o) 64
    (by rw [withdrawReturnDataPtrMem_size])]
  exact hptr

theorem withdrawReturnDataMem_read64 (I : ExecutionEnv) (o : ByteArray) (ho0 : o.size ≠ 0) :
    (withdrawReturnDataMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (withdrawReturnDataPtr o) := by
  rw [withdrawReturnDataMem_eq I o ho0]
  rw [readWithPadding_eq_extract _ 64 (by
    rw [ByteArray.size_append, withdrawReturnDataSizeMem_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [withdrawReturnDataSizeMem_size]; omega)]
  rw [← readWithPadding_eq_extract _ 64 (by rw [withdrawReturnDataSizeMem_size]; omega)]
  exact withdrawReturnDataSizeMem_read64 I o

theorem withdrawReturnDataPtr_gap (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataPtr o).toNat - (withdrawReturnDataMem I o).size < USize.size := by
  have hle := withdrawReturnDataPtr_toNat_le o hosz
  rw [withdrawReturnDataMem_size I o ho0]
  exact lt_usize _ (by omega)

theorem withdraw_u256_mul_toNat (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % UInt256.size := by
  rfl

theorem withdrawReturnDataActiveWords_M_mul32_lt (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 5).toNat 160 o.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 5 ≤ (160 + o.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((160 + o.size + 31) / 32) * 32 ≤ 160 + o.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem withdrawReturnDataActiveWords_toNat_ge (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    5 ≤ (withdrawReturnDataActiveWords o).toNat := by
  unfold withdrawReturnDataActiveWords
  have hmul := withdrawReturnDataActiveWords_M_mul32_lt o hosz
  have hMlt : MachineState.M (UInt256.ofNat 5).toNat 160 o.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
  unfold MachineState.M
  split
  · norm_num
  · exact Nat.le_max_left _ _

theorem withdrawReturnDataActiveWords_mul32_lt (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataActiveWords o).toNat * 32 < UInt256.size := by
  unfold withdrawReturnDataActiveWords
  have hmul := withdrawReturnDataActiveWords_M_mul32_lt o hosz
  have hMlt : MachineState.M (UInt256.ofNat 5).toNat 160 o.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hmul

theorem withdrawReturnDataActiveWords_mload64_haw (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    ¬ (⟨64⟩ : UInt256) ≥ withdrawReturnDataActiveWords o * ⟨32⟩ := by
  intro h
  have hle :
      (withdrawReturnDataActiveWords o * ⟨32⟩).toNat ≤
        (⟨64⟩ : UInt256).toNat := h
  rw [withdraw_u256_mul_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (withdrawReturnDataActiveWords_mul32_lt o hosz),
    show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
  have hge := withdrawReturnDataActiveWords_toNat_ge o hosz
  omega

theorem withdrawReturnDataBoolActiveWords_M_mul32_lt (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    MachineState.M (withdrawReturnDataActiveWords o).toNat
        (withdrawReturnDataPtr o).toNat 32 * 32 < UInt256.size := by
  simp [MachineState.M]
  by_cases hle : (withdrawReturnDataActiveWords o).toNat ≤
      ((withdrawReturnDataPtr o).toNat + 32 + 31) / 32
  · rw [Nat.max_eq_right hle]
    have hdiv : (((withdrawReturnDataPtr o).toNat + 32 + 31) / 32) * 32 ≤
        (withdrawReturnDataPtr o).toNat + 32 + 31 :=
      Nat.div_mul_le_self _ _
    have hptr := withdrawReturnDataPtr_toNat_le o hosz
    have hcap : 2 ^ 255 + 254 < UInt256.size := by norm_num [UInt256.size]
    omega
  · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
    exact withdrawReturnDataActiveWords_mul32_lt o hosz

theorem withdrawReturnDataBoolActiveWords_toNat_ge (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    5 ≤ (withdrawReturnDataBoolActiveWords o).toNat := by
  unfold withdrawReturnDataBoolActiveWords
  have hmul := withdrawReturnDataBoolActiveWords_M_mul32_lt o hosz
  have hMlt : MachineState.M (withdrawReturnDataActiveWords o).toNat
        (withdrawReturnDataPtr o).toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  simp [MachineState.M]
  exact Or.inl (withdrawReturnDataActiveWords_toNat_ge o hosz)

theorem withdrawReturnDataBoolActiveWords_mul32_lt (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataBoolActiveWords o).toNat * 32 < UInt256.size := by
  unfold withdrawReturnDataBoolActiveWords
  have hmul := withdrawReturnDataBoolActiveWords_M_mul32_lt o hosz
  have hMlt : MachineState.M (withdrawReturnDataActiveWords o).toNat
        (withdrawReturnDataPtr o).toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hmul

theorem withdrawReturnDataBoolActiveWords_mload64_haw (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    ¬ (⟨64⟩ : UInt256) ≥ withdrawReturnDataBoolActiveWords o * ⟨32⟩ := by
  intro h
  have hle :
      (withdrawReturnDataBoolActiveWords o * ⟨32⟩).toNat ≤
        (⟨64⟩ : UInt256).toNat := h
  rw [withdraw_u256_mul_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (withdrawReturnDataBoolActiveWords_mul32_lt o hosz),
    show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
  have hge := withdrawReturnDataBoolActiveWords_toNat_ge o hosz
  omega

set_option maxHeartbeats 1000000 in
theorem withdrawRehashMem_read0_64 (I : ExecutionEnv) :
    (withdrawRehashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSenderWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [withdrawRehashMem_size]; norm_num)]
  unfold withdrawRehashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size,
        toByteArray_size]
      norm_num)]
  let M := (UInt256.toByteArray (withdrawSenderWord I)).write 0 (withdrawPendingHashMem I) 0 32
  let S := UInt256.toByteArray (⟨4⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray (withdrawSenderWord I) ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [withdraw_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray (withdrawSenderWord I) := by
      dsimp [M]
      rw [← readWithPadding_eq_extract _ 0 (by
        rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size,
          toByteArray_size]
        norm_num)]
      rw [write32_read_back _ _ 0 (by rw [toByteArray_size])
        (by rw [withdrawPendingHashMem_size]; omega)]
      rw [show 32 = (UInt256.toByteArray (withdrawSenderWord I)).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨4⟩ : UInt256)).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size, toByteArray_size]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

theorem withdrawRehashMem_read64 (I : ExecutionEnv) :
    (withdrawRehashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawRehashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
  · rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])]
    · exact withdrawPendingHashMem_read64 I
    · rw [withdrawPendingHashMem_size]; omega
    · omega
    · rw [withdrawPendingHashMem_size]
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size, toByteArray_size]
    norm_num
  · omega
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawPendingHashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawPendingHashMem_size, toByteArray_size]
    norm_num

theorem withdrawRehashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawRehashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawRehashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawRehashMem_size]; decide) (by decide)
    (withdrawRehashMem_read64 I)

theorem withdrawReturnDataMem_mload64 (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawReturnDataMem I o).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawReturnDataActiveWords o * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawReturnDataMem I o).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = withdrawReturnDataPtr o := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := withdrawReturnDataActiveWords o)
    (v := withdrawReturnDataPtr o)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      withdrawReturnDataMem_size I o ho0]; omega)
    (withdrawReturnDataActiveWords_mload64_haw o hosz)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      withdrawReturnDataMem_read64 I o ho0)

theorem withdrawReturnDataBoolMem_read64 (I : ExecutionEnv) (o : ByteArray) (b : UInt256)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataBoolMem I o b).readWithPadding 64 32 =
      UInt256.toByteArray (withdrawReturnDataPtr o) := by
  unfold withdrawReturnDataBoolMem
  rw [withdraw_toByteArray_write_read_below_of_gap _ _ (withdrawReturnDataPtr o).toNat 64
    (by rw [withdrawReturnDataMem_size I o ho0]; omega)
    (by exact withdrawReturnDataPtr_toNat_ge o hosz)
    (withdrawReturnDataPtr_gap I o ho0 hosz)]
  exact withdrawReturnDataMem_read64 I o ho0

theorem withdrawReturnDataBoolMem_readPtr (I : ExecutionEnv) (o : ByteArray) (b : UInt256)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataBoolMem I o b).readWithPadding (withdrawReturnDataPtr o).toNat 32 =
      UInt256.toByteArray b := by
  unfold withdrawReturnDataBoolMem
  exact withdraw_toByteArray_write_read_back_of_gap b (withdrawReturnDataMem I o)
    (withdrawReturnDataPtr o).toNat (withdrawReturnDataPtr_gap I o ho0 hosz)

theorem withdrawReturnDataBoolMem_size_gt64 (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (⟨64⟩ : UInt256).toNat < (withdrawReturnDataBoolMem I o b).size := by
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  unfold withdrawReturnDataBoolMem
  by_cases hle : (withdrawReturnDataPtr o).toNat ≤ (withdrawReturnDataMem I o).size
  · rw [write32_eq _ _ _ (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append]
    have hprefix :
        ((withdrawReturnDataMem I o).extract 0 (withdrawReturnDataPtr o).toNat).size =
          (withdrawReturnDataPtr o).toNat := by
      rw [ByteArray.size_extract]
      omega
    have hword : ((UInt256.toByteArray b).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, toByteArray_size]
      norm_num
    rw [hprefix, hword]
    have hptr := withdrawReturnDataPtr_toNat_ge o hosz
    omega
  · have hge : (withdrawReturnDataMem I o).size ≤ (withdrawReturnDataPtr o).toNat := by
      omega
    rw [toByteArray_write_eq _ _ _ hge (withdrawReturnDataPtr_gap I o ho0 hosz)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' (withdrawReturnDataPtr_gap I o ho0 hosz), toByteArray_size]
    have hbase := withdrawReturnDataMem_size I o ho0
    have hptr := withdrawReturnDataPtr_toNat_ge o hosz
    omega

theorem withdrawReturnDataBoolMem_mload64 (I : ExecutionEnv) (o : ByteArray) (b : UInt256)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawReturnDataBoolMem I o b).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawReturnDataBoolActiveWords o * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawReturnDataBoolMem I o b).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = withdrawReturnDataPtr o := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := withdrawReturnDataBoolActiveWords o)
    (v := withdrawReturnDataPtr o)
    (withdrawReturnDataBoolMem_size_gt64 I o b ho0 hosz)
    (withdrawReturnDataBoolActiveWords_mload64_haw o hosz)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      withdrawReturnDataBoolMem_read64 I o b ho0 hosz)

theorem withdrawReturnDataPtr_add_sub (o : ByteArray) (hosz : o.size < 2 ^ 255) :
    UInt256.sub ((⟨32⟩ : UInt256) + withdrawReturnDataPtr o) (withdrawReturnDataPtr o) =
      ⟨32⟩ := by
  apply u256_inj
  have hptr_le := withdrawReturnDataPtr_toNat_le o hosz
  have hlt : 32 + (withdrawReturnDataPtr o).toNat < UInt256.size := by
    have hpow : 2 ^ 255 + 223 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hsum :
      ((⟨32⟩ : UInt256) + withdrawReturnDataPtr o).toNat =
        32 + (withdrawReturnDataPtr o).toNat := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hlt]
  rw [usub_toNat
      (a := ((⟨32⟩ : UInt256) + withdrawReturnDataPtr o))
      (b := withdrawReturnDataPtr o) (by rw [hsum]; omega),
    hsum]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  omega

theorem withdrawReturnDataActiveWords_mstore0_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataActiveWords o).toNat 0 32) =
      withdrawReturnDataActiveWords o := by
  have hM : MachineState.M (withdrawReturnDataActiveWords o).toNat 0 32 =
      (withdrawReturnDataActiveWords o).toNat := by
    simp [MachineState.M]
    have hge := withdrawReturnDataActiveWords_toNat_ge o hosz
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem withdrawReturnDataActiveWords_mstore32_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataActiveWords o).toNat 32 32) =
      withdrawReturnDataActiveWords o := by
  have hM : MachineState.M (withdrawReturnDataActiveWords o).toNat 32 32 =
      (withdrawReturnDataActiveWords o).toNat := by
    simp [MachineState.M]
    have hge := withdrawReturnDataActiveWords_toNat_ge o hosz
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem withdrawReturnDataActiveWords_mem64_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataActiveWords o).toNat 64 32) =
      withdrawReturnDataActiveWords o := by
  have hM : MachineState.M (withdrawReturnDataActiveWords o).toNat 64 32 =
      (withdrawReturnDataActiveWords o).toNat := by
    simp [MachineState.M]
    have hge := withdrawReturnDataActiveWords_toNat_ge o hosz
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem withdrawReturnDataActiveWords_keccak0_64_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataActiveWords o).toNat 0 64) =
      withdrawReturnDataActiveWords o := by
  have hM : MachineState.M (withdrawReturnDataActiveWords o).toNat 0 64 =
      (withdrawReturnDataActiveWords o).toNat := by
    simp [MachineState.M]
    have hge := withdrawReturnDataActiveWords_toNat_ge o hosz
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem withdrawReturnDataBoolActiveWords_mem64_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataBoolActiveWords o).toNat 64 32) =
      withdrawReturnDataBoolActiveWords o := by
  have hM : MachineState.M (withdrawReturnDataBoolActiveWords o).toNat 64 32 =
      (withdrawReturnDataBoolActiveWords o).toNat := by
    simp [MachineState.M]
    have hge := withdrawReturnDataBoolActiveWords_toNat_ge o hosz
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem withdrawReturnDataBoolActiveWords_ptr32_same (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    UInt256.ofNat (MachineState.M (withdrawReturnDataBoolActiveWords o).toNat
      (withdrawReturnDataPtr o).toNat 32) = withdrawReturnDataBoolActiveWords o := by
  unfold withdrawReturnDataBoolActiveWords
  have hmul := withdrawReturnDataBoolActiveWords_M_mul32_lt o hosz
  have hMlt : MachineState.M (withdrawReturnDataActiveWords o).toNat
        (withdrawReturnDataPtr o).toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  have hM : MachineState.M
        (MachineState.M (withdrawReturnDataActiveWords o).toNat
          (withdrawReturnDataPtr o).toNat 32)
        (withdrawReturnDataPtr o).toNat 32 =
      MachineState.M (withdrawReturnDataActiveWords o).toNat
        (withdrawReturnDataPtr o).toNat 32 := by
    simp [MachineState.M]
  rw [hM]

theorem withdrawReturnDataRestoreKeyMem_size (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) :
    (withdrawReturnDataRestoreKeyMem I o).size = 160 + o.size := by
  unfold withdrawReturnDataRestoreKeyMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    withdrawReturnDataMem_size I o ho0]
  omega

theorem withdrawReturnDataRestoreHashMem_size (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) :
    (withdrawReturnDataRestoreHashMem I o).size = 160 + o.size := by
  unfold withdrawReturnDataRestoreHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [withdrawReturnDataRestoreKeyMem_size I o ho0]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    withdrawReturnDataRestoreKeyMem_size I o ho0]
  omega

theorem withdrawReturnDataRestoreHashMem_read64 (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) :
    (withdrawReturnDataRestoreHashMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (withdrawReturnDataPtr o) := by
  unfold withdrawReturnDataRestoreHashMem withdrawReturnDataRestoreKeyMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
  · rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])]
    · exact withdrawReturnDataMem_read64 I o ho0
    · rw [withdrawReturnDataMem_size I o ho0]; omega
    · omega
    · rw [withdrawReturnDataMem_size I o ho0]; omega
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
      toByteArray_size]
    omega
  · omega
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
      toByteArray_size]
    omega

set_option maxHeartbeats 1000000 in
theorem withdrawReturnDataRestoreHashMem_read0_64 (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) :
    (withdrawReturnDataRestoreHashMem I o).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSenderWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold withdrawReturnDataRestoreHashMem withdrawReturnDataRestoreKeyMem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
    rw [write32_eq _ _ 32 (by rw [toByteArray_size])]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
        toByteArray_size]
      omega
    · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
        toByteArray_size]
      omega)]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])]
  · let M := (UInt256.toByteArray (withdrawSenderWord I)).write 0
      (withdrawReturnDataMem I o) 0 32
    let S := UInt256.toByteArray (⟨4⟩ : UInt256)
    change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray (withdrawSenderWord I) ++ S
    rw [show 0 + 64 = 64 by norm_num]
    rw [withdraw_extract_two_chunks_0]
    · have hM0 : M.extract 0 32 = UInt256.toByteArray (withdrawSenderWord I) := by
        dsimp [M]
        rw [← readWithPadding_eq_extract _ 0 (by
          rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
            ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
            ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
            toByteArray_size]
          omega)]
        rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
        rw [show 32 = (UInt256.toByteArray (withdrawSenderWord I)).size by
          rw [toByteArray_size]]
        exact withdrawByteArray_extract_self _
      have hSself : S.extract 0 32 = S := by
        dsimp [S]
        rw [show 32 = (UInt256.toByteArray (⟨4⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact withdrawByteArray_extract_self _
      rw [hM0, hSself]
    · rw [ByteArray.size_extract]
      dsimp [M]
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
        toByteArray_size]
      omega
    · rw [ByteArray.size_extract]
      dsimp [S]
      rw [toByteArray_size]
      norm_num
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawReturnDataMem_size I o ho0,
      toByteArray_size]
    omega

theorem withdrawReturnDataRestoreHashKeccak (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((withdrawReturnDataRestoreHashMem I o).readWithPadding 0 64))) =
      withdrawPendingSlot I := by
  rw [withdrawReturnDataRestoreHashMem_read0_64 I o ho0, withdrawPendingSlot_eq]
  exact mappingSlot_single (withdrawSenderWord I) ⟨4⟩

theorem withdrawReturnDataRestoreHashMem_mload64 (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawReturnDataRestoreHashMem I o).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawReturnDataActiveWords o * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawReturnDataRestoreHashMem I o).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = withdrawReturnDataPtr o := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := withdrawReturnDataActiveWords o)
    (v := withdrawReturnDataPtr o)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      withdrawReturnDataRestoreHashMem_size I o ho0]; omega)
    (withdrawReturnDataActiveWords_mload64_haw o hosz)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      withdrawReturnDataRestoreHashMem_read64 I o ho0)

theorem withdrawReturnDataRestoreBoolMem_read64 (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataRestoreBoolMem I o b).readWithPadding 64 32 =
      UInt256.toByteArray (withdrawReturnDataPtr o) := by
  unfold withdrawReturnDataRestoreBoolMem
  rw [withdraw_toByteArray_write_read_below_of_gap _ _
    (withdrawReturnDataPtr o).toNat 64
    (by rw [withdrawReturnDataRestoreHashMem_size I o ho0]; omega)
    (by exact withdrawReturnDataPtr_toNat_ge o hosz)
    (by
      have hle := withdrawReturnDataPtr_toNat_le o hosz
      rw [withdrawReturnDataRestoreHashMem_size I o ho0]
      exact lt_usize _ (by omega))]
  exact withdrawReturnDataRestoreHashMem_read64 I o ho0

theorem withdrawReturnDataRestorePtr_gap (I : ExecutionEnv) (o : ByteArray)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataPtr o).toNat - (withdrawReturnDataRestoreHashMem I o).size <
      USize.size := by
  have hle := withdrawReturnDataPtr_toNat_le o hosz
  rw [withdrawReturnDataRestoreHashMem_size I o ho0]
  exact lt_usize _ (by omega)

theorem withdrawReturnDataRestoreBoolMem_readPtr (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (withdrawReturnDataRestoreBoolMem I o b).readWithPadding (withdrawReturnDataPtr o).toNat 32 =
      UInt256.toByteArray b := by
  unfold withdrawReturnDataRestoreBoolMem
  exact withdraw_toByteArray_write_read_back_of_gap b (withdrawReturnDataRestoreHashMem I o)
    (withdrawReturnDataPtr o).toNat (withdrawReturnDataRestorePtr_gap I o ho0 hosz)

theorem withdrawReturnDataRestoreBoolMem_size_gt64 (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (⟨64⟩ : UInt256).toNat < (withdrawReturnDataRestoreBoolMem I o b).size := by
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  unfold withdrawReturnDataRestoreBoolMem
  by_cases hle : (withdrawReturnDataPtr o).toNat ≤
      (withdrawReturnDataRestoreHashMem I o).size
  · rw [write32_eq _ _ _ (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append]
    have hprefix :
        ((withdrawReturnDataRestoreHashMem I o).extract 0
            (withdrawReturnDataPtr o).toNat).size =
          (withdrawReturnDataPtr o).toNat := by
      rw [ByteArray.size_extract]
      omega
    have hword : ((UInt256.toByteArray b).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, toByteArray_size]
      norm_num
    rw [hprefix, hword]
    have hptr := withdrawReturnDataPtr_toNat_ge o hosz
    omega
  · have hge : (withdrawReturnDataRestoreHashMem I o).size ≤
        (withdrawReturnDataPtr o).toNat := by
      omega
    rw [toByteArray_write_eq _ _ _ hge (withdrawReturnDataRestorePtr_gap I o ho0 hosz)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' (withdrawReturnDataRestorePtr_gap I o ho0 hosz),
      toByteArray_size]
    have hbase := withdrawReturnDataRestoreHashMem_size I o ho0
    have hptr := withdrawReturnDataPtr_toNat_ge o hosz
    omega

theorem withdrawReturnDataRestoreBoolMem_mload64 (I : ExecutionEnv) (o : ByteArray)
    (b : UInt256) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawReturnDataRestoreBoolMem I o b).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawReturnDataBoolActiveWords o * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawReturnDataRestoreBoolMem I o b).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = withdrawReturnDataPtr o := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := withdrawReturnDataBoolActiveWords o)
    (v := withdrawReturnDataPtr o)
    (withdrawReturnDataRestoreBoolMem_size_gt64 I o b ho0 hosz)
    (withdrawReturnDataBoolActiveWords_mload64_haw o hosz)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      withdrawReturnDataRestoreBoolMem_read64 I o b ho0 hosz)

theorem withdrawRehashKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((withdrawRehashMem I).readWithPadding 0 64)))
      = withdrawPendingSlot I := by
  rw [withdrawRehashMem_read0_64, withdrawPendingSlot_eq]
  exact mappingSlot_single (withdrawSenderWord I) ⟨4⟩

theorem withdrawRehashBoolReturnMem_size (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRehashMem I) 128 32).size = 160 := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRehashMem_size]; omega)
      (by rw [withdrawRehashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, withdrawRehashMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem withdrawRehashBoolReturnMem_read64 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRehashMem I) 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRehashMem_size]; omega)
      (by rw [withdrawRehashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, withdrawRehashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, withdrawRehashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    norm_num)]
  rw [extract_append_left (withdrawRehashMem I)
      (ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawRehashMem I).size))) 64 96
      (by rw [withdrawRehashMem_size])]
  rw [← readWithPadding_eq_extract (withdrawRehashMem I) 64
    (by rw [withdrawRehashMem_size])]
  exact withdrawRehashMem_read64 I

theorem withdrawRehashBoolReturnMem_mload64 (I : ExecutionEnv) (b : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          ((UInt256.toByteArray b).write 0 (withdrawRehashMem I) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (((UInt256.toByteArray b).write 0 (withdrawRehashMem I) 128 32).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawRehashBoolReturnMem_size]; decide) (by decide)
    (withdrawRehashBoolReturnMem_read64 I b)

theorem withdrawRehashBoolReturnMem_read128 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRehashMem I) 128 32).readWithPadding 128 32 =
      UInt256.toByteArray b := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [withdrawRehashBoolReturnMem_size])]
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRehashMem_size]; omega)
      (by rw [withdrawRehashMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (withdrawRehashMem I ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawRehashMem I).size)))
      (UInt256.toByteArray b) 128 160 (by
        rw [ByteArray.size_append, withdrawRehashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, withdrawRehashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact withdrawByteArray_extract_self _]

theorem withdrawRestoreHashMem_size (I : ExecutionEnv) : (withdrawRestoreHashMem I).size = 96 := by
  unfold withdrawRestoreHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
      norm_num),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
  norm_num

set_option maxHeartbeats 1000000 in
theorem withdrawRestoreHashMem_read0_64 (I : ExecutionEnv) :
    (withdrawRestoreHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (withdrawSenderWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [withdrawRestoreHashMem_size]; norm_num)]
  unfold withdrawRestoreHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
      rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
      norm_num)]
  let M := (UInt256.toByteArray (withdrawSenderWord I)).write 0 (withdrawRehashMem I) 0 32
  let S := UInt256.toByteArray (⟨4⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray (withdrawSenderWord I) ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [withdraw_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray (withdrawSenderWord I) := by
      dsimp [M]
      rw [← readWithPadding_eq_extract _ 0 (by
        rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
        norm_num)]
      rw [write32_read_back _ _ 0 (by rw [toByteArray_size])
        (by rw [withdrawRehashMem_size]; omega)]
      rw [show 32 = (UInt256.toByteArray (withdrawSenderWord I)).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨4⟩ : UInt256)).size by rw [toByteArray_size]]
      exact withdrawByteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

theorem withdrawRestoreHashMem_read64 (I : ExecutionEnv) :
    (withdrawRestoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold withdrawRestoreHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
  · rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])]
    · exact withdrawRehashMem_read64 I
    · rw [withdrawRehashMem_size]; omega
    · omega
    · rw [withdrawRehashMem_size]
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
    norm_num
  · omega
  · rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [withdrawRehashMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, withdrawRehashMem_size, toByteArray_size]
    norm_num

theorem withdrawRestoreHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawRestoreHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((withdrawRestoreHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawRestoreHashMem_size]; decide) (by decide)
    (withdrawRestoreHashMem_read64 I)

theorem withdrawRestoreHashKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((withdrawRestoreHashMem I).readWithPadding 0 64)))
      = withdrawPendingSlot I := by
  rw [withdrawRestoreHashMem_read0_64, withdrawPendingSlot_eq]
  exact mappingSlot_single (withdrawSenderWord I) ⟨4⟩

theorem withdrawRestoreBoolReturnMem_size (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRestoreHashMem I) 128 32).size = 160 := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRestoreHashMem_size]; omega)
      (by rw [withdrawRestoreHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, withdrawRestoreHashMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem withdrawRestoreBoolReturnMem_read64 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRestoreHashMem I) 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRestoreHashMem_size]; omega)
      (by rw [withdrawRestoreHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, withdrawRestoreHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, withdrawRestoreHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    norm_num)]
  rw [extract_append_left (withdrawRestoreHashMem I)
      (ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawRestoreHashMem I).size))) 64 96
      (by rw [withdrawRestoreHashMem_size])]
  rw [← readWithPadding_eq_extract (withdrawRestoreHashMem I) 64
    (by rw [withdrawRestoreHashMem_size])]
  exact withdrawRestoreHashMem_read64 I

theorem withdrawRestoreBoolReturnMem_mload64 (I : ExecutionEnv) (b : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          ((UInt256.toByteArray b).write 0 (withdrawRestoreHashMem I) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (((UInt256.toByteArray b).write 0 (withdrawRestoreHashMem I) 128 32).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawRestoreBoolReturnMem_size]; decide) (by decide)
    (withdrawRestoreBoolReturnMem_read64 I b)

theorem withdrawRestoreBoolReturnMem_read128 (I : ExecutionEnv) (b : UInt256) :
    ((UInt256.toByteArray b).write 0 (withdrawRestoreHashMem I) 128 32).readWithPadding 128 32 =
      UInt256.toByteArray b := by
  rw [readWithPadding_eq_extract' _ 128 32 (by norm_num) (by norm_num)
      (by rw [withdrawRestoreBoolReturnMem_size])]
  rw [toByteArray_write_eq _ _ 128 (by rw [withdrawRestoreHashMem_size]; omega)
      (by rw [withdrawRestoreHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (withdrawRestoreHashMem I ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (withdrawRestoreHashMem I).size)))
      (UInt256.toByteArray b) 128 160 (by
        rw [ByteArray.size_append, withdrawRestoreHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, withdrawRestoreHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact withdrawByteArray_extract_self _]

theorem withdrawPendingKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((withdrawPendingHashMem I).readWithPadding 0 64)))
      = withdrawPendingSlot I := by
  rw [withdrawPendingHashMem_read0_64, withdrawPendingSlot_eq]
  exact mappingSlot_single (withdrawSenderWord I) ⟨4⟩

theorem withdrawCallStore_success_get (amount : UInt256) (success : Bool) (out : ByteArray) :
    (withdrawCallStore amount success out)["success"]? = some (.bool success) := by
  change (withdrawCallStore amount success out).get? "success" = some (.bool success)
  unfold withdrawCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem withdrawCallStore_amount_get (amount : UInt256) (success : Bool) (out : ByteArray) :
    (withdrawCallStore amount success out)["amount"]? =
      some (.int (Int.ofNat amount.toNat)) := by
  change (withdrawCallStore amount success out).get? "amount" =
    some (.int (Int.ofNat amount.toNat))
  unfold withdrawCallStore withdrawAmountStore
  rw [store_get_ne]
  · rw [store_get_ne]
    · exact store_get_self _ _ _
    · decide
  · decide

theorem withdrawAccountMapEquiv_balance {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) :
    (σ.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ, accountEquiv] at hστ ⊢
  exact hστ.2.1

theorem evalExpr_withdraw_sender (evm : EVM.State) (locals : Store) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := locals } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_withdraw_pendingReturns (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage (pendingReturnsRef sender)) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (withdrawPendingSlot evm.executionEnv)).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm (pendingReturnsRef sender) =
      .ok { base := "pendingReturns", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, pendingReturnsRef, sender,
      evalExpr?, envValue, EvalResult.bind, EvalResult.ofOption, pure, bind, valueToKey?]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "pendingReturns", steps := [.mindex (.address evm.executionEnv.source)] } :
        EvaledStorageRef) = some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, storageTypeStep?, simpleAuctionContract, storageDecls, uint256St]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_pendingReturns
      (.address evm.executionEnv.source))]
  rw [simpleAuctionStorageLocLoad_uint256]
  rfl

theorem evalExpr_withdraw_amount_gt_false (evm : EVM.State) (amount : UInt256)
    (hzero : amount = ⟨0⟩) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
      (.binary .gt (.var "amount") (.intLit 0)) = .ok (.bool false) := by
  subst hzero
  simp [withdrawAmountStore, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalBinaryOp?]

theorem evalExpr_withdraw_amount_gt_true (evm : EVM.State) (amount : UInt256)
    (hpos : amount ≠ ⟨0⟩) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
      (.binary .gt (.var "amount") (.intLit 0)) = .ok (.bool true) := by
  simp [withdrawAmountStore, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalBinaryOp?]
  have hnat : 0 < amount.toNat := by
    cases amount with
    | mk val =>
        cases val with
        | mk n hlt =>
            simp [UInt256.toNat] at hpos ⊢
            omega
  omega

theorem evalExpr_withdraw_success (evm : EVM.State) (amount : UInt256) (success : Bool)
    (out : ByteArray) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawCallStore amount success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawCallStore_success_get]

theorem evalExpr_withdraw_amount (evm : EVM.State) (amount : UInt256) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
      (.var "amount") = .ok (.int (Int.ofNat amount.toNat)) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawAmountStore]

theorem evalExpr_withdraw_amount_callStore (evm : EVM.State) (amount : UInt256)
    (success : Bool) (out : ByteArray) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawCallStore amount success out } evm
      (.var "amount") = .ok (.int (Int.ofNat amount.toNat)) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawCallStore_amount_get]

theorem evalExpr_withdraw_emptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := locals } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem evalExpr_withdraw_not_success_false (evm : EVM.State) (amount : UInt256)
    (out : ByteArray) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawCallStore amount true out } evm
      (.unary .not (.var "success")) = .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_withdraw_success]
  rfl

theorem evalExpr_withdraw_not_success_true (evm : EVM.State) (amount : UInt256)
    (out : ByteArray) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawCallStore amount false out } evm
      (.unary .not (.var "success")) = .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_withdraw_success]
  rfl

theorem withdrawAssignPending (evm : EVM.State) (locals : Store) (amount : UInt256)
    (hbase : locals.get? "pendingReturns" = none) :
    assignStorageRef? simpleAuctionConfig { contract := simpleAuctionContract, locals := locals } evm
      .storage (pendingReturnsRef sender) (.int (Int.ofNat amount.toNat)) =
        .ok ({ contract := simpleAuctionContract, locals := locals },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (withdrawPendingSlot evm.executionEnv) amount) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := hbase)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, pendingReturnsRef, sender,
          evalExpr?, envValue, EvalResult.bind, EvalResult.ofOption, pure, bind, valueToKey?])
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, simpleAuctionContract, storageDecls, uint256St])
      (hloc := simpleAuctionConfig_storage_pendingReturns (.address evm.executionEnv.source))
  rw [simpleAuctionStorageLocStore_uint256]
  rfl

theorem withdrawAssignZero (evm : EVM.State) (amount : UInt256) :
    assignStorageRef? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
      .storage (pendingReturnsRef sender) (.int 0) =
        .ok ({ contract := simpleAuctionContract, locals := withdrawAmountStore amount },
          withdrawZeroState evm) := by
  have hbase : (withdrawAmountStore amount).get? "pendingReturns" = none := by
    unfold withdrawAmountStore
    rw [store_get_ne]
    · simp
    · decide
  simpa [withdrawZeroState] using withdrawAssignPending evm (withdrawAmountStore amount) ⟨0⟩ hbase

theorem withdrawAssignRestore (evm : EVM.State) (amount : UInt256) (out : ByteArray) :
    assignStorageRef? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawCallStore amount false out } evm
      .storage (pendingReturnsRef sender) (.int (Int.ofNat amount.toNat)) =
        .ok (withdrawCallFrame amount false out, withdrawRestoreState evm amount) := by
  have hbase : (withdrawCallStore amount false out).get? "pendingReturns" = none := by
    unfold withdrawCallStore withdrawAmountStore
    rw [store_get_ne]
    · rw [store_get_ne]
      · rw [store_get_ne]
        · simp
        · decide
      · decide
    · decide
  simpa [withdrawRestoreState, withdrawCallFrame] using
    withdrawAssignPending evm (withdrawCallStore amount false out) amount hbase

theorem boolFalseReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool false) =
      some (UInt256.toByteArray (⟨0⟩ : UInt256)) :=
  scalarReturnEncoding (t := .bool) (w := ⟨0⟩) rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
        decide)
    (by simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256_false]; rfl)

theorem simpleAuctionWithdrawSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_withdraw {cd : ByteArray}
    (hsel : ((⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some withdrawTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩ : ByteArray) :=
    (simpleAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition])
    (post := [auctionEndTransition, beneficiaryGetter, auctionEndTimeGetter,
      highestBidderGetter, highestBidGetter])
    rfl ?_ (by rw [selectorOf, simpleAuctionWithdrawSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide

theorem simpleAuctionDecode_withdraw {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionX_withdraw_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd203⟩ := hreach
  exact evm_run rd203 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨214⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem simpleAuctionX_withdraw_entry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨809⟩ [⟨223⟩, simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd203⟩ := hreach
  exact ⟨_, _, evm_run rd203 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨214⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨223⟩, push2 ⟨809⟩, jump (by jump_dest)]⟩

theorem simpleAuctionX_withdraw_loadAmount {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨825⟩
      [withdrawAmountWord σ I, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawPendingHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd809⟩ := simpleAuctionX_withdraw_entry (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd814₀ := evm_run rd809 with [
    jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 ((UInt256.toByteArray (withdrawSenderWord I)).write 0 solcFreePtrMem 0 32)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        simp [withdrawSenderWord])
      (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (withdrawPendingHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        change (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (withdrawSenderWord I)).write 0 solcFreePtrMem 0 32) 32 32 =
          withdrawPendingHashMem I
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (withdrawPendingSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawPendingKeccak I) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd825₀⟩ := rd814₀.sload (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [withdrawAmountWord, initState] using rd825₀⟩

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_toCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩) :
    ∃ gasArg k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨862⟩
      [gasArg, withdrawSenderWord I, withdrawAmountWord σ I,
        ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        withdrawAmountWord σ I, withdrawSenderWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨_, _, rd825⟩ := simpleAuctionX_withdraw_loadAmount (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have hnez : UInt256.isZero (withdrawAmountWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hpos
  have rd831₀ := evm_run rd825 with [dup1, iszero]
  have rd831 := rd831₀
  rw [hnez] at rd831
  have rd849₀ := evm_run rd831 with [
    push2 ⟨948⟩, jumpiNT (by decide),
    caller, push0, dup2, dup2,
    raw mstore 0 ((UInt256.toByteArray (withdrawSenderWord I)).write 0
        (withdrawPendingHashMem I) 0 32) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (withdrawRehashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup3,
    raw keccak256 0 (withdrawPendingSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashKeccak I) (by decide) (by evm_ov),
    dup3, swap1]
  obtain ⟨_, _, rd849₀'⟩ := rd849₀.sstore hperm (by decide) (by evm_ov)
  have rd862₀ := evm_run rd849₀' with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMem_mload64 I) (by decide) (by evm_ov),
    swap1, swap2, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd862⟩ := rd862₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [withdrawZeroMap] using rd862⟩

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          (withdrawZeroMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (withdrawSenderWord I))
          (toExecute (withdrawZeroMap σ I) (AccountAddress.ofUInt256 (withdrawSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice)
          (withdrawAmountWord σ I) (withdrawAmountWord σ I)
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < 2 ^ 255
      ∧ RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨863⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩,
            withdrawAmountWord σ I, withdrawSenderWord I, ⟨0⟩,
            withdrawAmountWord σ I, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
          (withdrawRehashMem I) (UInt256.ofNat 3) o (cA', σ') k C := by
  obtain ⟨gasArg, _, _, rd862⟩ := simpleAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd863₀⟩ :=
    rd862.callValueMade (by decide) hperm hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (withdrawRehashMem I).readWithPadding (⟨128⟩ : UInt256).toNat
      (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact withdraw_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        (withdrawZeroMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (withdrawSenderWord I))
        (toExecute (withdrawZeroMap σ I) (AccountAddress.ofUInt256 (withdrawSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice)
        (withdrawAmountWord σ I) (withdrawAmountWord σ I)
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have ho255 : o.size < 2 ^ 255 := by
    rcases hΘ' with ⟨g'', A', hΘeq⟩
    have ho : o = (Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        (withdrawZeroMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (withdrawSenderWord I))
        (toExecute (withdrawZeroMap σ I) (AccountAddress.ofUInt256 (withdrawSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice)
        (withdrawAmountWord σ I) (withdrawAmountWord σ I)
        ByteArray.empty (I.depth + 1) I.header I.perm).2.2.2.2.2 :=
      congrArg (fun t => t.2.2.2.2.2) hΘeq
    rw [ho]
    exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, withdraw_write_len_zero, haw] at rd863₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ho255,
    by simpa [initState] using rd863₀⟩

-- PROMOTE -> Reasoning.Reach: value-parametric no-call-made branch for insufficient balance.
set_option maxHeartbeats 1000000 in
theorem withdrawRDCallValueInsufficientBalance {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target value inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False :=
      eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
      eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
    have hdepthLt : s.executionEnv.depth < 1024 := by
      rw [Fin.lt_def]; exact hdepth'
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hbalOpt :
        (value ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = False := by
      rw [hee, hσ]
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? σ ee.codeOwner) =
          (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Batteries.RBMap.find? σ ee.codeOwner <;> rfl]
      exact eq_false hbalance
    have hgtT :
        (value > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true (by
        show ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val < value.val.val
        exact Nat.lt_of_not_ge hbalance)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]
      intro hh
      rw [hh] at hdepth'
      exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtT,
      hdeqF] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) value gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hcA, hσ]
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_callDepth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨863⟩
      [⟨0⟩, ⟨128⟩, withdrawAmountWord σ I, withdrawSenderWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨gasArg, _, _, rd862⟩ := simpleAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨k', C', rd863₀⟩ := rd862.callValueDepthLimit hperm (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, withdraw_write_len_zero, haw] at rd863₀
  exact ⟨k', C', by simpa [withdrawZeroMap, initState] using rd863₀⟩

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_callInsufficient {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : ¬ withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨863⟩
      [⟨0⟩, ⟨128⟩, withdrawAmountWord σ I, withdrawSenderWord I, ⟨0⟩,
        withdrawAmountWord σ I, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, withdrawZeroMap σ I) k C := by
  obtain ⟨gasArg, _, _, rd862⟩ := simpleAuctionX_withdraw_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach hpos
  obtain ⟨k', C', rd863₀⟩ := withdrawRDCallValueInsufficientBalance rd862 hperm
    (by decide) hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, withdraw_write_len_zero, haw] at rd863₀
  exact ⟨k', C', by simpa [withdrawZeroMap, initState] using rd863₀⟩

theorem simpleAuctionX_withdraw_postCallEmpty_toBranch {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ} {z amount sender : UInt256}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨863⟩
      [z, ⟨128⟩, amount, sender, ⟨0⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [z, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop,
    returndatasize, dup1, push0, dup2, eq, push2 ⟨908⟩,
    jumpiT (by decide) (by jump_dest),
    jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

-- PROMOTE -> Reasoning.Reach: one-step RETURNDATACOPY with caller-provided memory shape.
set_option maxHeartbeats 1000000 in
theorem withdrawRDReturndatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hmemout : rdata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1) (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .RETURNDATACOPY = mcost := hmc s haw hstk
    have hmemok : ¬ b.toNat + c.toNat > s.machineState.returnData.size := by
      rw [hrdata]
      omega
    have st := returndatacopy_xstep hcode hpc hdec hstk hmemok hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg :
        g.toNat < C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stReturndatacopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stReturndatacopy]; exact hcode
      · simp only [stReturndatacopy]; rw [hpc]
      · rfl
      · simp only [stReturndatacopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stReturndatacopy]; rw [hmem, hrdata, hmemout]
      · simp only [stReturndatacopy]; rw [haw, hawout]
      · simp only [stReturndatacopy]; exact hrdata
      · simp only [stReturndatacopy]; exact hacc
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_postCallNonempty_toBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {z amount sender : UInt256} {o : ByteArray}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨863⟩
      [z, ⟨128⟩, amount, sender, ⟨0⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) o acc k C)
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255) :
    ∃ k' C', RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [z, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawReturnDataMem I o) (withdrawReturnDataActiveWords o) o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have houtsz : o.size < UInt256.size := by
    exact lt_size_of_lt_sign hosz
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtsz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd872₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd872 := rd872₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd872
  have rd876 := evm_run rd872 with [push2 ⟨908⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0 (withdrawRehashMem I) 64 32
  have rd894 := evm_run rd876 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMem_mload64 I) (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd897 := evm_run rd894 with [
    returndatasize, dup3,
    raw mstore (Cₘ (UInt256.ofNat 5) - Cₘ (UInt256.ofNat 3))
      mem3 (UInt256.ofNat 5) (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        decide)
      (by rfl) (by decide) (by evm_ov)]
  have rd903 := evm_run rd897 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyDest_toNat : copyDest.toNat = 160 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt houtsz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have hmem4 : mem4 = withdrawReturnDataMem I o := by
    simp [mem4, mem3, mem2, copyDest, copyLen, rdsz, rounded,
      withdrawReturnDataMem, withdrawReturnDataSizeMem, withdrawReturnDataPtrMem,
      withdrawReturnDataPtr, withdrawReturnDataRounded, hcopyDest_toNat, hcopyLen_toNat]
    rfl
  have haw4 :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat copyDest.toNat copyLen.toNat) =
        withdrawReturnDataActiveWords o := by
    simp [withdrawReturnDataActiveWords, copyDest, copyLen, hcopyDest_toNat,
      hcopyLen_toNat]
  have rd904 := withdrawRDReturndatacopy
    (Cₘ (withdrawReturnDataActiveWords o) - Cₘ (UInt256.ofNat 5))
    mem4
    (withdrawReturnDataActiveWords o)
    rd903 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        withdrawReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd913 := evm_run rd904 with [push2 ⟨913⟩, jump (by jump_dest), jumpdest]
  have rd918 := evm_run rd913 with [pop, pop, swap1, pop]
  have hpc918 :
      ((((((⟨913⟩ : UInt256) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        ⟨918⟩ := by
    decide
  rw [hpc918] at rd918
  rw [hmem4] at rd918
  exact ⟨_, _, rd918⟩

theorem simpleAuctionX_withdraw_successEmpty_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {amount : UInt256}
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [⟨1⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have rd223 := evm_run rd with [
    dup1, push2 ⟨946⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop,
    jumpdest, push1 ⟨1⟩, swap2, pop, pop, swap1, jump (by jump_dest)]
  have rd235 := evm_run rd223 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRehashMem_mload64 I) (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
        (withdrawRehashMem I) 128 32) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact evm_run rd235 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (withdrawRehashBoolReturnMem_mload64 I ⟨1⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide]
        exact withdrawRehashBoolReturnMem_read128 I ⟨1⟩)
        (by evm_ov) ]

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_successNonempty_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {amount : UInt256} {o : ByteArray}
    (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255)
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [⟨1⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawReturnDataMem I o) (withdrawReturnDataActiveWords o) o acc k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have rd223 := evm_run rd with [
    dup1, push2 ⟨946⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop,
    jumpdest, push1 ⟨1⟩, swap2, pop, pop, swap1, jump (by jump_dest)]
  have rd225 := evm_run rd223 with [jumpdest, push1 ⟨64⟩]
  have rd226 := RD.mload 0 (withdrawReturnDataPtr o) (withdrawReturnDataActiveWords o)
    rd225 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [withdrawReturnDataActiveWords_mem64_same o hosz]
      simp)
    (withdrawReturnDataMem_mload64 I o ho0 hosz)
    (withdrawReturnDataActiveWords_mem64_same o hosz)
    (by evm_ov)
  have rdBeforeMstore := evm_run rd226 with [swap1, iszero, iszero, dup2]
  have rdMstore := RD.mstore
    (Cₘ (withdrawReturnDataBoolActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawReturnDataBoolMem I o ⟨1⟩)
    (withdrawReturnDataBoolActiveWords o)
    rdBeforeMstore (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        withdrawReturnDataBoolActiveWords])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd235 := evm_run rdMstore with [push1 ⟨32⟩, add, push2 ⟨194⟩,
    jump (by jump_dest), jumpdest, push1 ⟨64⟩]
  have rd236 := RD.mload 0 (withdrawReturnDataPtr o) (withdrawReturnDataBoolActiveWords o)
    rd235 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [withdrawReturnDataBoolActiveWords_mem64_same o hosz]
      simp)
    (withdrawReturnDataBoolMem_mload64 I o ⟨1⟩ ho0 hosz)
    (withdrawReturnDataBoolActiveWords_mem64_same o hosz)
    (by evm_ov)
  have rdBeforeRet := evm_run rd236 with [dup1, swap2, sub, swap1]
  exact RD.ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) rdBeforeRet (by decide)
    (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [withdrawReturnDataPtr_add_sub o hosz]
        rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          withdrawReturnDataBoolActiveWords_ptr32_same o hosz]
        simp)
    (by
      rw [withdrawReturnDataPtr_add_sub o hosz]
      exact withdrawReturnDataBoolMem_readPtr I o ⟨1⟩ ho0 hosz)
    (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_failureEmpty_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {k C : ℕ}
    {amount : UInt256}
    (hperm : I.perm = true)
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [⟨0⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawRehashMem I) (UInt256.ofNat 3) ByteArray.empty (cAx, σx) k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAx, sstoreAccountMap I.codeOwner σx (withdrawPendingSlot I) amount)
      (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  have rd941₀ := evm_run rd with [
    dup1, push2 ⟨946⟩, jumpiNT (by decide), pop,
    caller, push0, swap1, dup2,
    raw mstore 0 ((UInt256.toByteArray (withdrawSenderWord I)).write 0
        (withdrawRehashMem I) 0 32) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (withdrawRestoreHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (withdrawPendingSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRestoreHashKeccak I) (by decide) (by evm_ov),
    swap2, swap1, swap2]
  obtain ⟨_, _, rd942₀⟩ := rd941₀.sstore hperm (by decide) (by evm_ov)
  have rd223 := evm_run rd942₀ with [swap2, swap1, pop, jump (by jump_dest)]
  have rd235 := evm_run rd223 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawRestoreHashMem_mload64 I) (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 ((UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
        (withdrawRestoreHashMem I) 128 32) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact evm_run rd235 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (withdrawRestoreBoolReturnMem_mload64 I ⟨0⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨0⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide]
        exact withdrawRestoreBoolReturnMem_read128 I ⟨0⟩)
      (by evm_ov) ]

set_option maxHeartbeats 1000000 in
theorem simpleAuctionX_withdraw_failureNonempty_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {k C : ℕ}
    {amount : UInt256} {o : ByteArray}
    (hperm : I.perm = true) (ho0 : o.size ≠ 0) (hosz : o.size < 2 ^ 255)
    (rd : RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨918⟩
      [⟨0⟩, amount, ⟨0⟩, ⟨223⟩, simpleAuctionSelWord I]
      (withdrawReturnDataMem I o) (withdrawReturnDataActiveWords o) o (cAx, σx) k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
        (cAx, sstoreAccountMap I.codeOwner σx (withdrawPendingSlot I) amount)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  have rdBeforeStoreKey := evm_run rd with [
    dup1, push2 ⟨946⟩, jumpiNT (by decide), pop,
    caller, push0, swap1, dup2]
  have rdStoreKey := RD.mstore
    (Cₘ (withdrawReturnDataActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawReturnDataRestoreKeyMem I o)
    (withdrawReturnDataActiveWords o) rdBeforeStoreKey (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [withdrawReturnDataActiveWords_mstore0_same o hosz]
      simp)
    (by rfl)
    (withdrawReturnDataActiveWords_mstore0_same o hosz)
    (by evm_ov)
  have rdBeforeStoreHash := evm_run rdStoreKey with [push1 ⟨4⟩, push1 ⟨32⟩]
  have rdStoreHash := RD.mstore
    (Cₘ (withdrawReturnDataActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawReturnDataRestoreHashMem I o)
    (withdrawReturnDataActiveWords o) rdBeforeStoreHash (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        withdrawReturnDataActiveWords_mstore32_same o hosz]
      simp)
    (by rfl)
    (withdrawReturnDataActiveWords_mstore32_same o hosz)
    (by evm_ov)
  have rdBeforeKeccak := evm_run rdStoreHash with [push1 ⟨64⟩, dup2]
  have rdKeccak := RD.keccak256
    (Cₘ (withdrawReturnDataActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawPendingSlot I)
    (withdrawReturnDataActiveWords o) rdBeforeKeccak (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        withdrawReturnDataActiveWords_keccak0_64_same o hosz]
      simp)
    (withdrawReturnDataRestoreHashKeccak I o ho0)
    (withdrawReturnDataActiveWords_keccak0_64_same o hosz)
    (by evm_ov)
  have rd941₀ := evm_run rdKeccak with [swap2, swap1, swap2]
  obtain ⟨_, _, rd942₀⟩ := rd941₀.sstore hperm (by decide) (by evm_ov)
  have rd223 := evm_run rd942₀ with [swap2, swap1, pop, jump (by jump_dest)]
  have rd225 := evm_run rd223 with [jumpdest, push1 ⟨64⟩]
  have rd226 := RD.mload
    (Cₘ (withdrawReturnDataActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawReturnDataPtr o) (withdrawReturnDataActiveWords o)
    rd225 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        withdrawReturnDataActiveWords_mem64_same o hosz]
      simp)
    (withdrawReturnDataRestoreHashMem_mload64 I o ho0 hosz)
    (withdrawReturnDataActiveWords_mem64_same o hosz)
    (by evm_ov)
  have rdBeforeMstore := evm_run rd226 with [swap1, iszero, iszero, dup2]
  have rdMstore := RD.mstore
    (Cₘ (withdrawReturnDataBoolActiveWords o) - Cₘ (withdrawReturnDataActiveWords o))
    (withdrawReturnDataRestoreBoolMem I o ⟨0⟩)
    (withdrawReturnDataBoolActiveWords o)
    rdBeforeMstore (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        withdrawReturnDataBoolActiveWords])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd235 := evm_run rdMstore with [push1 ⟨32⟩, add, push2 ⟨194⟩,
    jump (by jump_dest), jumpdest, push1 ⟨64⟩]
  have rd236 := RD.mload
    (Cₘ (withdrawReturnDataBoolActiveWords o) - Cₘ (withdrawReturnDataBoolActiveWords o))
    (withdrawReturnDataPtr o) (withdrawReturnDataBoolActiveWords o)
    rd235 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        withdrawReturnDataBoolActiveWords_mem64_same o hosz]
      simp)
    (withdrawReturnDataRestoreBoolMem_mload64 I o ⟨0⟩ ho0 hosz)
    (withdrawReturnDataBoolActiveWords_mem64_same o hosz)
    (by evm_ov)
  have rdBeforeRet := evm_run rd236 with [dup1, swap2, sub, swap1]
  exact RD.ret
    (Cₘ (withdrawReturnDataBoolActiveWords o) - Cₘ (withdrawReturnDataBoolActiveWords o))
    (UInt256.toByteArray (⟨0⟩ : UInt256)) rdBeforeRet (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [withdrawReturnDataPtr_add_sub o hosz]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        withdrawReturnDataBoolActiveWords_ptr32_same o hosz]
      simp)
    (by
      rw [withdrawReturnDataPtr_add_sub o hosz]
      exact withdrawReturnDataRestoreBoolMem_readPtr I o ⟨0⟩ ho0 hosz)
    (by evm_ov)

theorem simpleAuctionX_withdraw_callDepth_returnFalse {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, withdrawRestoreMap σ I) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  obtain ⟨_, _, rd863⟩ := simpleAuctionX_withdraw_callDepth (g := g) hperm hwv hreach
    hpos hdepth
  obtain ⟨_, _, rd918⟩ := simpleAuctionX_withdraw_postCallEmpty_toBranch rd863
  simpa [withdrawRestoreMap] using
    simpleAuctionX_withdraw_failureEmpty_return (g := g) hperm rd918

theorem simpleAuctionX_withdraw_callInsufficient_returnFalse {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : withdrawAmountWord σ I ≠ ⟨0⟩)
    (hbalance : ¬ withdrawAmountWord σ I ≤
      (withdrawZeroMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, withdrawRestoreMap σ I) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  obtain ⟨_, _, rd863⟩ := simpleAuctionX_withdraw_callInsufficient (g := g) hperm hwv
    hreach hpos hbalance hdepth
  obtain ⟨_, _, rd918⟩ := simpleAuctionX_withdraw_postCallEmpty_toBranch rd863
  simpa [withdrawRestoreMap] using
    simpleAuctionX_withdraw_failureEmpty_return (g := g) hperm rd918

theorem simpleAuctionX_withdraw_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨203⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : withdrawAmountWord σ I = ⟨0⟩) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd825⟩ := simpleAuctionX_withdraw_loadAmount (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd827₀ := evm_run rd825 with [dup1, iszero]
  have rd827 := rd827₀
  rw [hzero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd827
  have rd948 := evm_run rd827 with [push2 ⟨948⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd223 := evm_run rd948 with [
    jumpdest, push1 ⟨1⟩, swap2, pop, pop, swap1, jump (by jump_dest)]
  have rd235 := evm_run rd223 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (withdrawPendingHashMem_mload64 I) (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
        (withdrawPendingHashMem I) 128 32) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact evm_run rd235 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (withdrawBoolReturnMem_mload64 I ⟨1⟩) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide]
        exact withdrawBoolReturnMem_read128 I ⟨1⟩)
      (by evm_ov) ]

theorem simpleAuctionWithdrawBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals
      withdrawTransition.body .reverted := by
  dsimp [withdrawTransition]
  exact bodyReverts_nonPayable h

theorem simpleAuctionWithdrawBodyReturns_callSuccess
    (evm evm' : EVM.State) (amount : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hamount :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (withdrawPendingSlot evm.executionEnv) =
        amount)
    (hpos : amount ≠ ⟨0⟩)
    (hcall :
      callViaEVM (withdrawZeroState evm) (EVM.address (withdrawZeroState evm).executionEnv.source)
        (Int.ofNat amount.toNat) ByteArray.empty (true, evm', out)) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ withdrawTransition.body
      (.returned { contract := simpleAuctionContract, locals := withdrawCallStore amount true out }
        evm' (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hamountEval :
      evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
        (.storage (pendingReturnsRef sender)) =
          .ok (.int (Int.ofNat amount.toNat)) := by
    simpa [hamount] using evalExpr_withdraw_pendingReturns evm
  refine ExecBlock.consNormal (ExecStmt.letDecl hamountEval) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok
        { contract := simpleAuctionContract, locals := withdrawCallStore amount true out } evm')
      (evalExpr_withdraw_amount_gt_true evm amount hpos) ?_) ?_
  · show ExecBlock simpleAuctionConfig
      { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
      [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
        .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
        .ite (.unary .not (.var "success"))
          [ .assign .storage (pendingReturnsRef sender) (.var "amount"),
            .return (.boolLit false) ]
          [] ]
      (.ok { contract := simpleAuctionContract, locals := withdrawCallStore amount true out } evm')
    refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (withdrawAssignZero evm amount)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallSuccess
        (evalExpr_withdraw_sender (withdrawZeroState evm) (withdrawAmountStore amount))
        (evalExpr_withdraw_amount (withdrawZeroState evm) amount)
        (evalExpr_withdraw_emptyBytes (withdrawZeroState evm) (withdrawAmountStore amount))
        hcall) ?_
    exact ExecBlock.consNormal
      (ExecStmt.iteFalse (evalExpr_withdraw_not_success_false evm' amount out) ExecBlock.nil)
      ExecBlock.nil
  · exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem simpleAuctionWithdrawBodyReturns_callFailure
    (evm evm' : EVM.State) (amount : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hamount :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (withdrawPendingSlot evm.executionEnv) =
        amount)
    (hpos : amount ≠ ⟨0⟩)
    (hcall :
      callViaEVM (withdrawZeroState evm) (EVM.address (withdrawZeroState evm).executionEnv.source)
        (Int.ofNat amount.toNat) ByteArray.empty (false, evm', out)) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ withdrawTransition.body
      (.returned { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
        (withdrawRestoreState evm' amount) (some (.bool false))) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hamountEval :
      evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
        (.storage (pendingReturnsRef sender)) =
          .ok (.int (Int.ofNat amount.toNat)) := by
    simpa [hamount] using evalExpr_withdraw_pendingReturns evm
  refine ExecBlock.consNormal (ExecStmt.letDecl hamountEval) ?_
  refine ExecBlock.consReturn
    (ExecStmt.iteTrue
      (result := .returned
        { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
        (withdrawRestoreState evm' amount) (some (.bool false)))
      (evalExpr_withdraw_amount_gt_true evm amount hpos) ?_)
  show ExecBlock simpleAuctionConfig
    { contract := simpleAuctionContract, locals := withdrawAmountStore amount } evm
    [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
      .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
      .ite (.unary .not (.var "success"))
        [ .assign .storage (pendingReturnsRef sender) (.var "amount"),
          .return (.boolLit false) ]
        [] ]
    (.returned { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
      (withdrawRestoreState evm' amount) (some (.bool false)))
  refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (withdrawAssignZero evm amount)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_withdraw_sender (withdrawZeroState evm) (withdrawAmountStore amount))
      (evalExpr_withdraw_amount (withdrawZeroState evm) amount)
      (evalExpr_withdraw_emptyBytes (withdrawZeroState evm) (withdrawAmountStore amount))
      hcall) ?_
  refine ExecBlock.consReturn ?_
  refine ExecStmt.iteTrue
    (result := .returned
      { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
      (withdrawRestoreState evm' amount) (some (.bool false)))
    (evalExpr_withdraw_not_success_true evm' amount out) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_withdraw_amount_callStore evm' amount false out)
      (withdrawAssignRestore evm' amount out)) ?_
  show ExecBlock simpleAuctionConfig
    { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
    (withdrawRestoreState evm' amount) [.return (.boolLit false)]
    (.returned { contract := simpleAuctionContract, locals := withdrawCallStore amount false out }
      (withdrawRestoreState evm' amount) (some (.bool false)))
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem simpleAuctionWithdrawBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨203⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have _hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm := hOriginalAccounts
  have hsz := simpleAuctionWithdrawSelector_size hsel
  have hd := simpleAuctionDispatch_withdraw (cd := I.calldata) hsel
  have hdec := simpleAuctionDecode_withdraw (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hzero : withdrawAmountWord σ_evm I = ⟨0⟩
    · have hword : withdrawAmountWord σ_evm I = withdrawAmountWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (withdrawPendingSlot I) ⟨0⟩
      have hzeroS : withdrawAmountWord σ_solm I = ⟨0⟩ := by
        rw [← hword, hzero]
      let evmS := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          evmS ∅
          withdrawTransition.body
          (.returned
            { contract := simpleAuctionContract
              locals := withdrawAmountStore (withdrawAmountWord σ_solm I) }
            evmS (some (.bool true))) := by
        refine ExecFuncBody.execBlockRet ?_
        unfold withdrawTransition
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evmS, initState, hwv])
        have hamount :
            evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evmS
              (.storage (pendingReturnsRef sender)) =
                .ok (.int (Int.ofNat (withdrawAmountWord σ_solm I).toNat)) := by
          simpa [evmS, initState, withdrawAmountWord, Solm.EVM.storageLoad, State.lookupAccount]
            using evalExpr_withdraw_pendingReturns evmS
        refine ExecBlock.consNormal (ExecStmt.letDecl hamount) ?_
        refine ExecBlock.consNormal
          (ExecStmt.iteFalse
            (evalExpr_withdraw_amount_gt_false evmS (withdrawAmountWord σ_solm I) hzeroS)
            ExecBlock.nil) ?_
        exact ExecBlock.consReturn (ExecStmt.return (by rw [evalExpr?]; rfl))
      exact (simpleAuctionX_withdraw_zero (g := Sat256.ofUInt256 g) hwv hreach hzero)
        |>.reEquivExecution hcode hd hdec hbody hAccounts
          (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
    · have hword : withdrawAmountWord σ_evm I = withdrawAmountWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (withdrawPendingSlot I) ⟨0⟩
      have hnonzero : withdrawAmountWord σ_evm I ≠ ⟨0⟩ := hzero
      have hposS : withdrawAmountWord σ_solm I ≠ ⟨0⟩ := by
        intro hz
        exact hnonzero (by rw [hword]; exact hz)
      let evmS := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
      let evmSZero := withdrawZeroState evmS
      have hamountS :
          Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner
              (withdrawPendingSlot evmS.executionEnv) =
            withdrawAmountWord σ_solm I := by
        simp [evmS, initState, withdrawAmountWord, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage]
      have hZeroMap :
          accountMapEquiv (withdrawZeroMap σ_evm I) (withdrawZeroMap σ_solm I) := by
        unfold withdrawZeroMap
        exact accountMapEquiv_sstoreAccountMap I.codeOwner (withdrawPendingSlot I) ⟨0⟩
          hAccounts
      have hRestoreMap :
          accountMapEquiv (withdrawRestoreMap σ_evm I) (withdrawRestoreMap σ_solm I) := by
        unfold withdrawRestoreMap
        rw [hword]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner (withdrawPendingSlot I)
          (withdrawAmountWord σ_solm I) hZeroMap
      by_cases hdepthEq : I.depth = 1024
      · let evmSFail : EVM.State :=
          { evmSZero with
            substate := (evmSZero.addAccessedAccount
              (EVM.address evmSZero.executionEnv.source)).substate }
        have hcall :
            callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
              (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
              (false, evmSFail, ByteArray.empty) := by
          apply callViaEVM.callNotMade
          · rfl
          · rfl
          · rintro ⟨_, hdepthNe⟩
            exact hdepthNe (by
              simpa [evmSZero, withdrawZeroState, evmS, initState,
                storageStore_executionEnv] using hdepthEq)
        have hbody :
            ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
              withdrawTransition.body
              (.returned
                { contract := simpleAuctionContract
                  locals := withdrawCallStore (withdrawAmountWord σ_solm I) false ByteArray.empty }
                (withdrawRestoreState evmSFail (withdrawAmountWord σ_solm I))
                (some (.bool false))) :=
          simpleAuctionWithdrawBodyReturns_callFailure evmS evmSFail
            (withdrawAmountWord σ_solm I) ByteArray.empty
            (by simpa [evmS, initState] using hwv) hamountS hposS
            (by simpa [evmSZero] using hcall)
        exact (simpleAuctionX_withdraw_callDepth_returnFalse (g := Sat256.ofUInt256 g)
            hperm hwv hreach hnonzero hdepthEq)
          |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
            (by
              simp [evmSFail, evmSZero, withdrawRestoreState, withdrawZeroState, evmS,
                initState, simpleAuctionStorageStore_createdAccounts])
              (by
                simpa [evmSFail, evmSZero, withdrawRestoreState, withdrawRestoreMap,
                  withdrawZeroState, evmS, initState, simpleAuctionStorageStore_accountMap,
                  storageStore_executionEnv]
                  using hRestoreMap)
            (returnEquiv_of_encode (by simpa [boolTy] using boolFalseReturnEncoding))
      · have hdepthLt : I.depth.val < 1024 := by
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          have hneVal : I.depth.val ≠ 1024 := by
            intro hv
            apply hdepthEq
            exact Fin.ext hv
          omega
        by_cases hbalance : withdrawAmountWord σ_evm I ≤
            (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
        · obtain ⟨cA', σ', z, out, A_in, callGas, kCall, CCall, hTheta, hout255, rd863⟩ :=
            simpleAuctionX_withdraw_callMade (g := Sat256.ofUInt256 g) hperm hwv hreach
              hzero hbalance hdepthLt
          obtain ⟨g'', A', hThetaEq⟩ := hTheta
          let evmEZero : EVM.State :=
            { initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I with
              accountMap := withdrawZeroMap σ_evm I }
          let evmECall : EVM.State :=
            { evmEZero with accountMap := σ', substate := A', createdAccounts := cA' }
          let targetE : EVM.Address := AccountAddress.ofUInt256 (withdrawSenderWord I)
          let valueE : ℤ := Int.ofNat (withdrawAmountWord σ_evm I).toNat
          have hcallE :
              callViaEVM evmEZero targetE valueE ByteArray.empty (z, evmECall, out) := by
            refine callViaEVM.callMade
              (valueWord := withdrawAmountWord σ_evm I)
              (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
              ?_ ?_ ?_ ?_ ?_
            · exact (simpleAuctionWordOfInt_ofNat_toNat (withdrawAmountWord σ_evm I)).symm
            · refine ⟨callGas, A_in, ?_⟩
              simpa [evmEZero, targetE, valueE, initState, hperm, accountAddress_roundtrip,
                withdrawSenderWord] using hThetaEq
            · simp [evmECall]
            · simpa [evmEZero, initState] using hbalance
            · intro hd'
              exact hdepthEq (by simpa [evmEZero, initState] using hd')
          obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
            callViaEVM_accountMapEquiv (storage := simpleAuctionConfig.storage)
              (evm_solm := evmSZero) hcallE
              (by
                simpa [evmEZero, evmSZero, withdrawZeroState, evmS, initState,
                  simpleAuctionStorageStore_accountMap, storageStore_executionEnv] using hZeroMap)
              (by
                simpa [evmEZero, evmSZero, evmS, initState,
                  withdrawZeroState_originalMap] using hOriginalAccounts)
              (by
                simp [evmEZero, evmSZero, withdrawZeroState, evmS, initState,
                  simpleAuctionStorageStore_createdAccounts])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_genesisBlockHeader])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_blocks])
              (by simp [evmEZero, evmSZero, evmS, initState,
                withdrawZeroState_substate])
              (by
                simp [evmEZero, evmSZero, withdrawZeroState, evmS, initState,
                  storageStore_executionEnv])
          let evmSCall : EVM.State :=
            { evmSZero with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evmECall.createdAccounts }
          have hAddressId (a : AccountAddress) : EVM.address a = a := by
            apply Fin.ext
            simp [EVM.address, EVM.uintN]
            exact Nat.mod_eq_of_lt a.isLt
          have hTargetEq : targetE = EVM.address evmSZero.executionEnv.source := by
            calc
              targetE = I.source := by
                simpa [targetE, withdrawSenderWord] using accountAddress_roundtrip I.source
              _ = EVM.address evmSZero.executionEnv.source := by
                simp [evmSZero, withdrawZeroState, evmS, initState, storageStore_executionEnv,
                  hAddressId]
          have hValueEq : valueE = Int.ofNat (withdrawAmountWord σ_solm I).toNat := by
            simp [valueE, hword]
          have hcallS :
              callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
                (z, evmSCall, out) := by
            simpa [evmSCall, hTargetEq, hValueEq] using hcallSRaw
          by_cases hout0 : out.size = 0
          · have houtEmpty : out = ByteArray.empty :=
              withdrawByteArray_eq_empty_of_size_eq_zero out hout0
            subst out
            obtain ⟨_, _, rd918⟩ := simpleAuctionX_withdraw_postCallEmpty_toBranch rd863
            cases z
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    withdrawTransition.body
                    (.returned
                      { contract := simpleAuctionContract
                        locals := withdrawCallStore (withdrawAmountWord σ_solm I) false
                          ByteArray.empty }
                      (withdrawRestoreState evmSCall (withdrawAmountWord σ_solm I))
                      (some (.bool false))) :=
                simpleAuctionWithdrawBodyReturns_callFailure evmS evmSCall
                  (withdrawAmountWord σ_solm I) ByteArray.empty
                  (by simpa [evmS, initState] using hwv) hamountS hposS
                  (by simpa [evmSZero] using hcallS)
              have hret : RDret simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                  (cA',
                    sstoreAccountMap I.codeOwner σ' (withdrawPendingSlot I)
                      (withdrawAmountWord σ_evm I))
                  (UInt256.toByteArray (⟨0⟩ : UInt256)) :=
                simpleAuctionX_withdraw_failureEmpty_return (g := Sat256.ofUInt256 g) hperm
                  (by simpa using rd918)
              have hPostRestore :
                  accountMapEquiv
                    (sstoreAccountMap I.codeOwner σ' (withdrawPendingSlot I)
                      (withdrawAmountWord σ_evm I))
                    (sstoreAccountMap I.codeOwner σ'_solm (withdrawPendingSlot I)
                      (withdrawAmountWord σ_solm I)) := by
                rw [hword]
                exact accountMapEquiv_sstoreAccountMap I.codeOwner (withdrawPendingSlot I)
                  (withdrawAmountWord σ_solm I) hPostAccounts
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by
                  simp [evmSCall, evmECall, withdrawRestoreState,
                    simpleAuctionStorageStore_createdAccounts])
                (by
                  simpa [evmSCall, withdrawRestoreState, evmSZero, withdrawZeroState, evmS,
                    initState, simpleAuctionStorageStore_accountMap, storageStore_executionEnv]
                    using hPostRestore)
                (returnEquiv_of_encode (by simpa [boolTy] using boolFalseReturnEncoding))
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    withdrawTransition.body
                    (.returned
                      { contract := simpleAuctionContract
                        locals := withdrawCallStore (withdrawAmountWord σ_solm I) true
                          ByteArray.empty }
                      evmSCall (some (.bool true))) :=
                simpleAuctionWithdrawBodyReturns_callSuccess evmS evmSCall
                  (withdrawAmountWord σ_solm I) ByteArray.empty
                  (by simpa [evmS, initState] using hwv) hamountS hposS
                  (by simpa [evmSZero] using hcallS)
              have hret : RDret simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                  (cA', σ') (UInt256.toByteArray (⟨1⟩ : UInt256)) :=
                simpleAuctionX_withdraw_successEmpty_return (g := Sat256.ofUInt256 g)
                  (by simpa using rd918)
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by simp [evmSCall, evmECall])
                (by simpa [evmSCall, evmECall] using hPostAccounts)
                (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
          · obtain ⟨_, _, rd918⟩ :=
              simpleAuctionX_withdraw_postCallNonempty_toBranch (g := Sat256.ofUInt256 g)
                rd863 hout0 hout255
            cases z
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    withdrawTransition.body
                    (.returned
                      { contract := simpleAuctionContract
                        locals := withdrawCallStore (withdrawAmountWord σ_solm I) false out }
                      (withdrawRestoreState evmSCall (withdrawAmountWord σ_solm I))
                      (some (.bool false))) :=
                simpleAuctionWithdrawBodyReturns_callFailure evmS evmSCall
                  (withdrawAmountWord σ_solm I) out
                  (by simpa [evmS, initState] using hwv) hamountS hposS
                  (by simpa [evmSZero] using hcallS)
              have hret : RDret simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                  (cA',
                    sstoreAccountMap I.codeOwner σ' (withdrawPendingSlot I)
                      (withdrawAmountWord σ_evm I))
                  (UInt256.toByteArray (⟨0⟩ : UInt256)) :=
                simpleAuctionX_withdraw_failureNonempty_return (g := Sat256.ofUInt256 g)
                  hperm hout0 hout255 (by simpa using rd918)
              have hPostRestore :
                  accountMapEquiv
                    (sstoreAccountMap I.codeOwner σ' (withdrawPendingSlot I)
                      (withdrawAmountWord σ_evm I))
                    (sstoreAccountMap I.codeOwner σ'_solm (withdrawPendingSlot I)
                      (withdrawAmountWord σ_solm I)) := by
                rw [hword]
                exact accountMapEquiv_sstoreAccountMap I.codeOwner (withdrawPendingSlot I)
                  (withdrawAmountWord σ_solm I) hPostAccounts
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by
                  simp [evmSCall, evmECall, withdrawRestoreState,
                    simpleAuctionStorageStore_createdAccounts])
                (by
                  simpa [evmSCall, withdrawRestoreState, evmSZero, withdrawZeroState, evmS,
                    initState, simpleAuctionStorageStore_accountMap, storageStore_executionEnv]
                    using hPostRestore)
                (returnEquiv_of_encode (by simpa [boolTy] using boolFalseReturnEncoding))
            · have hbody :
                  ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                    withdrawTransition.body
                    (.returned
                      { contract := simpleAuctionContract
                        locals := withdrawCallStore (withdrawAmountWord σ_solm I) true out }
                      evmSCall (some (.bool true))) :=
                simpleAuctionWithdrawBodyReturns_callSuccess evmS evmSCall
                  (withdrawAmountWord σ_solm I) out
                  (by simpa [evmS, initState] using hwv) hamountS hposS
                  (by simpa [evmSZero] using hcallS)
              have hret : RDret simpleAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
                  (cA', σ') (UInt256.toByteArray (⟨1⟩ : UInt256)) :=
                simpleAuctionX_withdraw_successNonempty_return (g := Sat256.ofUInt256 g)
                  hout0 hout255 (by simpa using rd918)
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by simp [evmSCall, evmECall])
                (by simpa [evmSCall, evmECall] using hPostAccounts)
                (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
        · let evmSFail : EVM.State :=
            { evmSZero with
              substate := (evmSZero.addAccessedAccount
                (EVM.address evmSZero.executionEnv.source)).substate }
          have hBalEq :
              (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) =
                (withdrawZeroMap σ_solm I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
            withdrawAccountMapEquiv_balance hZeroMap I.codeOwner
          have hcall :
              callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawAmountWord σ_solm I).toNat) ByteArray.empty
                (false, evmSFail, ByteArray.empty) := by
            apply callViaEVM.callNotMade
            · rfl
            · rfl
            · rintro ⟨hvalueBal, _⟩
              rw [simpleAuctionWordOfInt_ofNat_toNat] at hvalueBal
              have hvalueBalS :
                    withdrawAmountWord σ_solm I ≤
                      (withdrawZeroMap σ_solm I |>.find? I.codeOwner |>.elim ⟨0⟩
                        (·.balance)) := by
                  simpa [evmSZero, withdrawZeroState, evmS, initState, withdrawZeroMap,
                    simpleAuctionStorageStore_accountMap, storageStore_executionEnv] using hvalueBal
              have hvalueBalE :
                  withdrawAmountWord σ_evm I ≤
                    (withdrawZeroMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩
                      (·.balance)) := by
                simpa [hword, hBalEq] using hvalueBalS
              exact hbalance hvalueBalE
          have hbody :
              ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                withdrawTransition.body
                (.returned
                  { contract := simpleAuctionContract
                    locals := withdrawCallStore (withdrawAmountWord σ_solm I) false ByteArray.empty }
                  (withdrawRestoreState evmSFail (withdrawAmountWord σ_solm I))
                  (some (.bool false))) :=
            simpleAuctionWithdrawBodyReturns_callFailure evmS evmSFail
              (withdrawAmountWord σ_solm I) ByteArray.empty
              (by simpa [evmS, initState] using hwv) hamountS hposS
              (by simpa [evmSZero] using hcall)
          exact (simpleAuctionX_withdraw_callInsufficient_returnFalse (g := Sat256.ofUInt256 g)
              hperm hwv hreach hzero hbalance hdepthLt)
            |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
              (by
                simp [evmSFail, evmSZero, withdrawRestoreState, withdrawZeroState, evmS,
                  initState, simpleAuctionStorageStore_createdAccounts])
                (by
                  simpa [evmSFail, evmSZero, withdrawRestoreState, withdrawRestoreMap,
                    withdrawZeroState, evmS, initState, simpleAuctionStorageStore_accountMap,
                    storageStore_executionEnv]
                    using hRestoreMap)
              (returnEquiv_of_encode (by simpa [boolTy] using boolFalseReturnEncoding))
  · have hrev := simpleAuctionX_withdraw_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    have hbody : ExecTransitionBody simpleAuctionConfig simpleAuctionContract
        (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
        withdrawTransition.body .reverted := by
      exact simpleAuctionWithdrawBodyReverts_nonpayable
        (by simp only [initState]; exact hwv)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
