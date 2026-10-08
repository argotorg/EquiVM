import Reasoning.Storage
import Reasoning.SolmBody
import Solm.TransientStorage

/-!
# Transient storage reasoning

Scalar read and write helpers for the executing account's transient slot map. The pure
Solidity encoding and word lemmas are shared with persistent storage.
-/

open Ethereum Ethereum.EVM Solm ABI

namespace Reasoning.Theory

/-- The executing account's transient word in an account map. -/
abbrev codeOwnerTransientWord (ee : ExecutionEnv) (σ : AccountMap)
    (slot : UInt256) : UInt256 :=
  σ.get? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.tstorage.getD slot ⟨0⟩)

theorem codeOwnerTransientWord_initState {σ σ₀ A I} {g : Sat256}
    (slot : UInt256) :
    Solm.EVM.transientLoad (initState σ σ₀ g A I) I.codeOwner slot =
      codeOwnerTransientWord I σ slot := by
  simp [Solm.EVM.transientLoad, initState, State.lookupAccount,
    Account.lookupTransientStorage, codeOwnerTransientWord]

theorem transientLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (uint256Loc slot) =
      .int (Int.ofNat (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htakeNat :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32 =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    apply List.take_of_length_le
    rw [(EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2]
  have htakeFin :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.extract 0
            (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1 := by
    exact htakeNat
  unfold transientLocLoad uint256Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  rw [normalizeInt_uint_eq_self]
  · congr
    rw [htakeFin, fromBytes'_toBytesLEWithSizeProof]
    rfl
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 32) <
        EVM.twoPow 256
    rw [htakeNat]
    have hle := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1)
    rw [(EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2] at hle
    exact hle

theorem transientLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    transientLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot val) := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]


theorem transientLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (bytes32Loc slot) =
      .fixedBytes ⟨31, by decide⟩
        (EVM.Word.toBytesBE (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold transientLocLoad bytes32Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem transientLocStore_bytes32 (evm : EVM.State) (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    transientLocStore evm (bytes32Loc slot) v =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot word) := by
  unfold transientLocStore storageLocWriteWord bytes32Loc
  simp only [hval, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof word).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = word.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]


theorem transientLocLoad_uint_offset0 (evm : EVM.State) (slot : UInt256)
    (size : Fin 33) (width : ABI.BitWidth)
    {hbound : (0 : Fin 32).val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val) (hbits : 8 * size.val ≤ 256) :
    transientLocLoad evm
        { slot := slot, offset := 0, size := size, hbound := hbound,
          type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ (8 * size.val) - 1))).toNat) := by
  unfold transientLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  rw [normalizeInt_uint_eq_self]
  · change Value.int (Int.ofNat (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 size.val))) = _
    rw [List.extract_eq_take_drop, List.drop_zero]
    simpa [Nat.sub_zero] using
      fromBytes'_take_wordLE_land_mask
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) size.val hbits
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 size.val) <
        EVM.twoPow width.val
    rw [List.extract_eq_take_drop, List.drop_zero, hwidth]
    have hle := EVM.fromBytes'_le (bs := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.take size.val)
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2,
      Nat.min_eq_left (by omega)] at hle
    exact hle

theorem transientLocLoad_uint_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val)
    (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    transientLocLoad evm
        { slot := slot, offset := offset, size := size, hbound := hbound,
          type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val)))
          (UInt256.ofNat (256 ^ size.val - 1))).toNat) := by
  unfold transientLocLoad wordToElem
  change Value.int (normalizeInt (.uint width) (Int.ofNat (fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.extract
        offset.val (offset.val + size.val))))) = _
  rw [normalizeInt_uint_eq_self]
  · rw [List.extract_eq_take_drop]
    simpa [Nat.add_sub_cancel_left] using
      fromBytes'_drop_take_wordLE_land_div_mask
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) offset.val size.val hoff hsize
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    change fromBytes' (((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1).extract
        offset.val (offset.val + size.val)) < EVM.twoPow width.val
    rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left, hwidth]
    have hle := EVM.fromBytes'_le (bs := ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.drop offset.val).take
        size.val)
    rw [List.length_take, List.length_drop, (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2,
      Nat.min_eq_left (by omega)] at hle
    exact hle

theorem transientLocStore_int_some (evm : EVM.State) (loc : StorageLoc) (n : Int) :
    ∃ evm', transientLocStore evm loc (.int n) = some evm' := by
  unfold transientLocStore
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩


theorem transientLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (addressOffset0Loc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  unfold transientLocLoad addressOffset0Loc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take20_wordLE_solcAddrMask]


theorem transientLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    transientLocStore evm (addressOffset0Loc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  unfold transientLocStore storageLocWriteWord addressOffset0Loc
  simp only [valueToWord_address_ofNat_canonical addr hcanon, bind, Option.bind]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof addr).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (setAddressOffset0Word
          (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) addr).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_drop_wordLE]
  have hclean : (UInt256.land addr solcAddrMask).toNat = addr.toNat := by
    simpa using congrArg UInt256.toNat (solcAddrMask_clean hcanon)
  rw [hclean]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof addr).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ hcanon]
  ring


theorem transientLocLoad_address_offset1 (evm : EVM.State) (slot : UInt256)
    {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32} :
    transientLocLoad evm
        { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address } =
      .address (AccountAddress.ofNat
        (UInt256.land
          (UInt256.div (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
          solcAddrMask).toNat) := by
  unfold transientLocLoad wordToElem
  simp only [Fin.val_one]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1).extract 1 21))) = _
  rw [List.extract_eq_take_drop, fromBytes'_drop1_take20_wordLE_solcAddrMask]


theorem transientLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    transientLocLoad evm (boolOffset0Loc slot) =
      wordToElem .bool
        (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold transientLocLoad boolOffset0Loc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [fromBytes'_take_wordLE_land_mask (n := 1) _ (by decide)]
  rfl

theorem transientLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    transientLocLoad evm (boolOffset0Loc slot) = .bool false := by
  rw [transientLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem transientLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    transientLocLoad evm (boolOffset0Loc slot) = .bool true := by
  rw [transientLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]


theorem transientLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (boolOffset0Loc slot) (.bool true) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  unfold transientLocStore storageLocWriteWord boolOffset0Loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.lor
          (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)).1 =
      [1] by
        change List.take 1 (Ethereum.toBytes' 1 ++
          List.replicate (32 - (Ethereum.toBytes' 1).length) 0) = [1]
        simp [Ethereum.toBytes']
        decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetTrueWord_toNat]

theorem transientLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    transientLocStore evm (boolOffset0Loc slot) (.bool false) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩))) := by
  unfold transientLocStore storageLocWriteWord boolOffset0Loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 =
      [0] by
        change List.take 1 (Ethereum.toBytes' 0 ++
          List.replicate (32 - (Ethereum.toBytes' 0).length) 0) = [0]
        simp [Ethereum.toBytes']]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [packedSetFalseWord_toNat]

theorem transientLocStore_bool_word_offset0 (evm : EVM.State) (slot word : UInt256) :
    transientLocStore evm (boolOffset0Loc slot) (wordToElem .bool word) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (setBoolOffset0Word (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot) word)) := by
  by_cases hzero : word = ⟨0⟩
  · subst hzero
    have hbool : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by
      decide
    simp only [wordToElem, beq_self_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hbool, u256_lor_zero] using
      transientLocStore_bool_false_offset0 evm slot
  · have hbeq : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply hzero
      apply u256_inj
      simpa [UInt256.toNat] using hval
    have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    simp only [wordToElem, hbeq, Bool.false_eq_true, ↓reduceIte]
    simpa [setBoolOffset0Word, hiszero] using transientLocStore_bool_true_offset0 evm slot


theorem transientLocStore_uint256_int (evm : EVM.State) (slot : UInt256) (n : Int) :
    transientLocStore evm (uint256Loc slot) (.int n) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt n)) := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (EVM.wordOfInt n).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]


theorem transientLocStore_uint8 (evm : EVM.State) (slot value : UInt256)
    (hc : value.toNat < 256) :
    transientLocStore evm
      { slot := slot, offset := 0, size := 1, hbound := by decide,
        type := .int (.uint ⟨8, by decide⟩) }
      (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) value)) := by
  unfold transientLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof value).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).1.drop 1) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask value 1 (by decide),
    fromBytes'_drop_wordLE]
  rw [u256_lor_toNat, packedSetFalseWord_toNat]
  rw [nat_lor_comm]
  rw [show 256 = 2 ^ 8 by decide, Nat.mul_comm (2 ^ 8)]
  rw [nat_lor_shift_add value.toNat _ 8 hc]
  have hbound := (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [Nat.mod_eq_of_lt (show value.toNat +
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 8 * 2 ^ 8 <
        UInt256.size from by
      change _ < 2 ^ 256
      change (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256
        at hbound
      omega)]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof value).2]
  change (UInt256.land value ⟨255⟩).toNat +
    256 * ((Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat / 256) = _
  rw [lowByteClean hc]
  omega


theorem transientLocStore_uint256_pred (evm : EVM.State) (slot len : UInt256)
    (hpos : 0 < len.toNat) :
    transientLocStore evm (uint256Loc slot) (.int (Int.ofNat len.toNat - 1)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (len.toNat - 1))) := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_natCast_pred_of_pos len hpos, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat (len.toNat - 1))).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (UInt256.ofNat (len.toNat - 1)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem transientLocStore_uint256_succ (evm : EVM.State) (slot val : UInt256) :
    transientLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat + 1)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot (val + ⟨1⟩)) := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, wordOfInt_natCast_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (val + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (val + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem transientLocStore_uint256_ofNat (evm : EVM.State) (slot : UInt256) (n : Nat) :
    transientLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot
        (EVM.word (Int.ofNat n).toNat)) := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [wordOfInt_nonneg]
  · have hslen := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.word (Int.ofNat n).toNat)).2
    congr 2
    apply u256_inj
    show fromBytes'
        (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
          ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (EVM.word (Int.ofNat n).toNat).toNat
    rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
      List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]
  · simp


theorem transientLocStore_word_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', transientLocStore evm (uint256Loc slot) (.int n) = some evm' := by
  unfold transientLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩


theorem tstoreAccountMap_absent_same {owner : AccountAddress} {τ : AccountMap}
    {slot val : UInt256} (hmissing : τ.get? owner = none) :
    tstoreAccountMap owner τ slot val = τ := by
  unfold tstoreAccountMap
  rw [hmissing]
  rfl


theorem transientStore_executionEnv (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.transientStore evm addr slot val).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.transientStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount, Account.updateTransientStorage]

theorem transientStore_eq_accountMap_update (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    {evm with accountMap := (Solm.EVM.transientStore evm addr slot val).accountMap} =
      Solm.EVM.transientStore evm addr slot val := by
  unfold Solm.EVM.transientStore
  cases evm.lookupAccount addr <;> simp [Option.option, State.setAccount]

theorem transientStore_accountMap (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.transientStore evm addr slot val).accountMap =
      tstoreAccountMap addr evm.accountMap slot val := by
  unfold Solm.EVM.transientStore tstoreAccountMap State.lookupAccount
  cases h : evm.accountMap.get? addr with
  | none => simp [Option.option]
  | some acc => simp [Option.option, State.setAccount, Account.updateTransientStorage]


theorem transientStore_absent (evm : EVM.State) (addr : AccountAddress)
    (hmissing : evm.accountMap.get? addr = none) (slot val : UInt256) :
    Solm.EVM.transientStore evm addr slot val = evm := by
  simp [Solm.EVM.transientStore, State.lookupAccount,
    -Std.ExtTreeMap.get?_eq_getElem?, hmissing, Option.option]


theorem transientLoad_transientStore_same_present (evm : EVM.State) (addr : AccountAddress)
    {acc : Account} (hacc : evm.accountMap.get? addr = some acc) (slot val : UInt256) :
    Solm.EVM.transientLoad (Solm.EVM.transientStore evm addr slot val) addr slot = val := by
  unfold Solm.EVM.transientLoad Solm.EVM.transientStore State.lookupAccount
  rw [hacc]
  simp only [Option.option]
  unfold State.setAccount
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
  unfold Account.updateTransientStorage Account.lookupTransientStorage
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
    rfl
  · simp [hzero]


theorem transientLoad_transientStore_ne (evm : EVM.State) (addr : AccountAddress)
    {readSlot writeSlot val : UInt256} (hne : readSlot ≠ writeSlot) :
    Solm.EVM.transientLoad (Solm.EVM.transientStore evm addr writeSlot val) addr readSlot =
      Solm.EVM.transientLoad evm addr readSlot := by
  simp only [Solm.EVM.transientLoad, Solm.EVM.transientStore, State.lookupAccount]
  cases hacc : evm.accountMap.get? addr with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option]
  | some acc =>
      simp only [Option.option]
      unfold State.setAccount
      simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
      unfold Account.updateTransientStorage Account.lookupTransientStorage
      by_cases hzero : (val == (default : UInt256)) = true
      · have hval : val = (default : UInt256) := eq_of_beq hzero
        subst val
        simp [storage_getD_erase_ne acc.tstorage readSlot writeSlot ⟨0⟩ hne]
      · simp [hzero, storage_getD_insert_ne acc.tstorage readSlot writeSlot val ⟨0⟩ hne]


theorem tstoreAccountMap_tstorage_getD_ne (σ : AccountMap) (a : AccountAddress)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    (((tstoreAccountMap a σ writeSlot val).get? a).option (default : UInt256)
        (fun acc => acc.tstorage.getD readSlot (default : UInt256))) =
      ((σ.get? a).option (default : UInt256)
        (fun acc => acc.tstorage.getD readSlot (default : UInt256))) := by
  unfold tstoreAccountMap
  cases hσ : σ.get? a with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, hσ, Option.option]
  | some acc =>
      simp [Option.option]
      by_cases hzero : val = (default : UInt256)
      · simpa [hzero] using storage_getD_update_ne acc.tstorage readSlot writeSlot val default hne
      · simpa [hzero] using storage_getD_update_ne acc.tstorage readSlot writeSlot val default hne


theorem tstoreAccountMap_tstorage_getD_self_present
    (σ : AccountMap) (a : AccountAddress) {acc : Account}
    (hacc : σ.get? a = some acc) (slot val : UInt256) :
    (((tstoreAccountMap a σ slot val).get? a).option (default : UInt256)
        (fun acc => acc.tstorage.getD slot (default : UInt256))) = val := by
  unfold tstoreAccountMap
  rw [hacc]
  simp only [Option.option]
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    subst val
    simp
  · simp [hzero]


theorem tstoreAccountMap_get?_owner_some_of_some
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    ∃ acc', (tstoreAccountMap a σ slot val).get? a = some acc' := by
  unfold tstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  exact ⟨if val == (default : UInt256) then { acc with tstorage := acc.tstorage.erase slot }
    else { acc with tstorage := acc.tstorage.insert slot val }, rfl⟩

theorem tstoreAccountMap_tstorage_getD_self_zero_present
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    (((tstoreAccountMap a σ slot val).get? a).option (⟨0⟩ : UInt256)
        (fun acc => acc.tstorage.getD slot ⟨0⟩)) = val := by
  unfold tstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (⟨0⟩ : UInt256) := by
      simpa using eq_of_beq hzero
    subst val
    simp [hzero]
  · have hfalse : (val == (default : UInt256)) = false := by
      cases h : (val == (default : UInt256)) <;> simp [h] at hzero ⊢
    simp [hfalse]


theorem transientStore_σ₀ (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.transientStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.transientStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem transientStore_substate (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.transientStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.transientStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

namespace EVMStateEquiv

theorem transientLoad {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256) :
    Solm.EVM.transientLoad evm₁ addr₁ slot = Solm.EVM.transientLoad evm₂ addr₂ slot := by
  subst addr₂
  simp [Solm.EVM.transientLoad, State.lookupAccount,
    Account.lookupTransientStorage, h.accountMap]

theorem transientLoad_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) :
    Solm.EVM.transientLoad evm₁ evm₁.executionEnv.codeOwner slot =
      Solm.EVM.transientLoad evm₂ evm₂.executionEnv.codeOwner slot := by
  rw [h.executionEnv]
  simp [Solm.EVM.transientLoad, State.lookupAccount,
    Account.lookupTransientStorage, h.accountMap]

theorem transientStore {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    {addr₁ addr₂ : AccountAddress} (haddr : addr₁ = addr₂) (slot : UInt256)
    {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv (Solm.EVM.transientStore evm₁ addr₁ slot val₁)
      (Solm.EVM.transientStore evm₂ addr₂ slot val₂) := by
  subst addr₂
  subst val₂
  refine ⟨?_, ?_⟩
  · rw [transientStore_executionEnv, transientStore_executionEnv]
    exact h.executionEnv
  · simpa [transientStore_accountMap] using
      congrArg (fun accounts => tstoreAccountMap addr₁ accounts slot val₁) h.accountMap

theorem transientStore_codeOwner {evm₁ evm₂ : EVM.State} (h : EVMStateEquiv evm₁ evm₂)
    (slot : UInt256) {val₁ val₂ : UInt256} (hval : val₁ = val₂) :
    EVMStateEquiv
      (Solm.EVM.transientStore evm₁ evm₁.executionEnv.codeOwner slot val₁)
      (Solm.EVM.transientStore evm₂ evm₂.executionEnv.codeOwner slot val₂) :=
  h.transientStore (congrArg ExecutionEnv.codeOwner h.executionEnv) slot hval

end EVMStateEquiv


/-- Resolve a transient reference from the transient declarations. -/
theorem resolveTransientStorageRef?_ok {cfg : Config} {solm : Frame} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some ty) :
    resolveTransientStorageRef? cfg solm evm slot = .ok (er, ty) := by
  simp [resolveTransientStorageRef?, her, hty, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

/-- A transient backend reads an elementary leaf through its physical location. -/
theorem readTransientStorage?_elem {cfg : Config} {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc)) :
    cfg.transientBackend.read er (.elem t) evm = .ok (transientLocLoad evm loc) := by
  rw [hbackend]
  exact solidityTransientStorageBackend_read_elem layout er t evm loc hloc

/-- A scalar transient read collapses to a single `transientLocLoad`. -/
theorem evalExpr_transient_scalar {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some (.elem t))
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc)) :
    evalExpr? cfg solm evm (.transient slot) = .ok (transientLocLoad evm loc) := by
  rw [evalExpr?]
  simp only [resolveTransientStorageRef?_ok her hty, bind, EvalResult.bind,
    readTransientStorage?_elem hbackend hloc]

/-- A scalar transient read with an already-normalized value. -/
theorem evalExpr_transient_scalar_value {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc} {value : Value}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some (.elem t))
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hload : transientLocLoad evm loc = value) :
    evalExpr? cfg solm evm (.transient slot) = .ok value := by
  rw [evalExpr_transient_scalar her hty hbackend hloc]
  exact congrArg EvalResult.ok hload

/-- A scalar transient assignment collapses to a single `transientLocStore`. -/
theorem assignStorageRef_transient_scalar_value {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {value : Value}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some ty)
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : transientLocStore evm loc value = some evm') :
    assignStorageRef? cfg solm evm .transient slot value = .ok (solm, evm') := by
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  · simp [assignStorageRef?, resolveTransientStorageRef?_ok her hty, hbackend,
      solidityTransientStorageBackend, transientSolidityWriteStorage?,
      transientSolidityLeafLoc?, hloc, hstore, EvalResult.ofOption,
      EvalResult.bind, bind, pure]
  · simp [assignStorageRef?, resolveTransientStorageRef?_ok her hty, hbackend,
      solidityTransientStorageBackend, transientSolidityWriteStorage?,
      transientSolidityLeafLoc?, hloc, hstore, EvalResult.ofOption,
      EvalResult.bind, bind, pure]

theorem assignStorageRef_transient_scalar {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {n : Int}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some ty)
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : transientLocStore evm loc (.int n) = some evm') :
    assignStorageRef? cfg solm evm .transient slot (.int n) = .ok (solm, evm') := by
  exact assignStorageRef_transient_scalar_value her hty hbackend hloc hleaf hstore

theorem assignStorageRef_transient_bool_word {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {word : UInt256}
    (her : evalTransientStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.transient er = some ty)
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : transientLocStore evm loc (wordToElem .bool word) = some evm') :
    assignStorageRef? cfg solm evm .transient slot (wordToElem .bool word) =
      .ok (solm, evm') := by
  exact assignStorageRef_transient_scalar_value her hty hbackend hloc hleaf hstore

/-- Clear an elementary transient leaf using its packed location. -/
theorem clearTransientStorage_elem {cfg : Config} {layout : StorageLayout}
    {evm evm' : EVM.State} {er : EvaledStorageRef} {t : ABI.ElemType}
    {loc : StorageLoc}
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hstore : transientLocStore evm loc (.int 0) = some evm') :
    cfg.transientBackend.clear er (.elem t) evm = .ok evm' := by
  simp [hbackend, solidityTransientStorageBackend, transientSolidityClearStorage?,
    transientSolidityLeafLoc?, hloc, hstore, EvalResult.ofOption,
    EvalResult.bind, bind]

theorem deleteTransientStorage_elem {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {ref : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hkind : usesTransientStorage solm ref = true)
    (hresolve : resolveTransientStorageRef? cfg solm evm ref = .ok (er, .elem t))
    (hbackend : cfg.transientBackend = solidityTransientStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hstore : transientLocStore evm loc (.int 0) = some evm') :
    deleteStorage? cfg solm evm ref = .ok evm' := by
  simp only [deleteStorage?, hkind, ↓reduceIte, hresolve, EvalResult.bind, bind]
  exact clearTransientStorage_elem hbackend hloc hstore

end Reasoning.Theory
