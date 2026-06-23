import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.ERC6909.Approve
import Examples.OpenZeppelinBench.Pausable.Storage
import Examples.ERC20.Approve
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `setOperator(address,bool)` -/

/-- The raw ABI word for `setOperator`'s `spender` argument. -/
abbrev setOperatorSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `setOperator`'s `approved` argument. -/
abbrev setOperatorApprovedWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev setOperatorSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat)

abbrev setOperatorApprovedValue (I : ExecutionEnv) : Value :=
  wordToElem .bool (setOperatorApprovedWord I)

theorem erc6909WordToElem_bool_scalar (word : UInt256) :
    match wordToElem .bool word with
    | .struct _ _ => False
    | .array _ => False
    | _ => True := by
  change
    match
        (if (word.val == 0) = true then
          Value.bool false
        else
          Value.bool true) with
    | .struct _ _ => False
    | .array _ => False
    | _ => True
  by_cases h : (word.val == 0) = true <;> simp [h]

theorem assignStorageRef_storage_bool_word {cfg : Config} {solm : Frame}
    {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {ty : StorageType} {loc : StorageLoc} {word : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hstore : storageLocStore evm loc (wordToElem .bool word) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (wordToElem .bool word) =
      .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc
    (erc6909WordToElem_bool_scalar word) hstore

abbrev setOperatorStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (setOperatorSpenderValue I)).insert "approved"
    (setOperatorApprovedValue I)

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWord_bool_ok_zero {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hzero : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨0⟩) :
    decodeScalarWord? (.elem .bool) bytes start = some (.bool false, start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp [hzero]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWord_bool_ok_one {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hone : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨1⟩) :
    decodeScalarWord? (.elem .bool) bytes start = some (.bool true, start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  simp [hone, UInt256.size]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWord_bool_none_noncanon {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32)
    (hnz : ABI.bytesToWord ((bytes.drop start).take 32) ≠ ⟨0⟩)
    (hno : ABI.bytesToWord ((bytes.drop start).take 32) ≠ ⟨1⟩) :
    decodeScalarWord? (.elem .bool) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_pos hlen]
  have hnzNat : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = 0 := by
    intro h
    exact hnz (uint256_toNat_eq_zero h)
  have hnoNat : ¬ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat = 1 := by
    intro h
    apply hno
    apply u256_inj
    simpa [UInt256.toNat] using h
  simp only [Option.bind, bind]
  rw [if_neg (by simpa [UInt256.toNat] using hnzNat),
    if_neg (by simpa [UInt256.toNat] using hnoNat)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWord_bool_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem .bool) bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := .elem .bool) (bytes := bytes)
    (start := start) (by decide)]
  simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
  rw [if_neg hshort]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_bool_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hbool :
      ABI.bytesToWord ((bytes.drop 32).take 32) = ⟨0⟩ ∨
      ABI.bytesToWord ((bytes.drop 32).take 32) = ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord ((bytes.drop 32).take 32))] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rcases hbool with hzero | hone
  · rw [decodeScalarWord_bool_ok_zero (start := 32) hlen32 hzero]
    simp [wordToElem, hzero]
  · rw [decodeScalarWord_bool_ok_one (start := 32) hlen32 hone]
    simp [wordToElem, hone]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_bool_none_noncanon_addr {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_bool_none_noncanon_bool {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnz : ABI.bytesToWord ((bytes.drop 32).take 32) ≠ ⟨0⟩)
    (hno : ABI.bytesToWord ((bytes.drop 32).take 32) ≠ ⟨1⟩) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_bool_none_noncanon (start := 32) hlen32 hnz hno]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_bool_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [.elem .address, .elem .bool] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    by_cases hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]
      rw [decodeScalarWord_bool_none_short (start := 32) htake32n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_bool_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hbool : calldataWord cd 36 = ⟨0⟩ ∨ calldataWord cd 36 = ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd =
      some (((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (wordToElem .bool (calldataWord cd 36))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_ok (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon) (by
      rcases hbool with hzero | hone
      · left
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
        exact hzero
      · right
        rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
            simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
        exact hone)]
  change decodeCalldata.insertValues [x, y]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        wordToElem .bool (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32))] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (wordToElem .bool (calldataWord cd 36)))
  simp [decodeCalldata.insertValues]
  rw [hword4]
  rw [hword36]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_bool_none_noncanon_addr {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_noncanon_addr (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_bool_none_noncanon_bool {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnz : calldataWord cd 36 ≠ ⟨0⟩) (hno : calldataWord cd 36 ≠ ⟨1⟩) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_noncanon_bool (bytes := cd.toList.drop 4)
    htake4 htake36' (by rw [hword4]; exact hcanon)]
  · rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
    exact hnz
  · rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
    exact hno

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_bool_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_bool_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_bool_none_huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [.elem .address, .elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [.elem .address, .elem .bool]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem erc6909Decode_setOperator_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hbool : setOperatorApprovedWord I = ⟨0⟩ ∨ setOperatorApprovedWord I = ⟨1⟩) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata =
        some (setOperatorStore I) := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata =
    some (setOperatorStore I)
  simpa [addr, boolTy, setOperatorStore, setOperatorSpenderValue, setOperatorApprovedValue,
    setOperatorSpenderWord, setOperatorApprovedWord, calldataWord]
    using decodeCalldata_addr_bool_ok
      (cd := I.calldata) (x := "spender") (y := "approved")
      hsz68 hbig (by simpa [setOperatorSpenderWord, calldataWord] using hcanon)
      (by simpa [setOperatorApprovedWord, calldataWord] using hbool)

theorem erc6909Decode_setOperator_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy] using
    decodeCalldata_addr_bool_none_short
      (cd := I.calldata) (x := "spender") (y := "approved") hsz4 hshort

theorem erc6909Decode_setOperator_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (setOperatorSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy, setOperatorSpenderWord, calldataWord] using
    decodeCalldata_addr_bool_none_noncanon_addr
      (cd := I.calldata) (x := "spender") (y := "approved")
      hsz68 hbig (by simpa [setOperatorSpenderWord, calldataWord] using hnc)

theorem erc6909Decode_setOperator_none_noncanon_approved {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (setOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hnz : setOperatorApprovedWord I ≠ ⟨0⟩) (hno : setOperatorApprovedWord I ≠ ⟨1⟩) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy, setOperatorSpenderWord, setOperatorApprovedWord, calldataWord] using
    decodeCalldata_addr_bool_none_noncanon_bool
      (cd := I.calldata) (x := "spender") (y := "approved") hsz68 hbig
      (by simpa [setOperatorSpenderWord, calldataWord] using hcanon)
      (by simpa [setOperatorApprovedWord, calldataWord] using hnz)
      (by simpa [setOperatorApprovedWord, calldataWord] using hno)

theorem erc6909Decode_setOperator_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setOperatorTransition.params.map Param.name)
      (transitionSignature setOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "approved"] [addr, boolTy] I.calldata = none
  simpa [addr, boolTy] using
    decodeCalldata_addr_bool_none_huge
      (cd := I.calldata) (x := "spender") (y := "approved") hbig

abbrev setOperatorOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def setOperatorSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address evm.executionEnv.source)
    (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))

def setOperatorSlotI (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address I.source)
    (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))

def setOperatorBoolWord (old approved : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩))
    (UInt256.isZero (UInt256.isZero approved))

theorem erc6909U256_lor_zero (a : UInt256) :
    UInt256.lor a ⟨0⟩ = a := by
  apply u256_inj
  change Nat.lor a.toNat 0 % UInt256.size = a.toNat
  have hlor : Nat.lor a.toNat 0 = a.toNat := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    change Nat.testBit (a.toNat ||| 0) i = Nat.testBit a.toNat i
    rw [Nat.testBit_lor]
    simp
  have hlt : a.toNat < UInt256.size := by
    simpa [UInt256.toNat] using a.val.isLt
  rw [hlor, Nat.mod_eq_of_lt hlt]

def setOperatorPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm I)
    (setOperatorBoolWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setOperatorSlot evm I))
      (setOperatorApprovedWord I))

-- PROMOTE -> Storage.lean
-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0 for an arbitrary
-- source bool value represented by a decoded ABI word.
theorem erc6909StorageLocStore_bool_word_offset0 (evm : EVM.State) (slot word : UInt256) :
    storageLocStore evm (boolLoc slot) (wordToElem .bool word) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setOperatorBoolWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) word)) := by
  by_cases hzero : word = ⟨0⟩
  · subst hzero
    have hbool : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by
      native_decide
    simp only [wordToElem, beq_self_eq_true, ↓reduceIte]
    simpa [boolLoc, OpenZeppelinBench.Pausable.boolLoc, setOperatorBoolWord,
      OpenZeppelinBench.Pausable.pausedSetFalseWord, hbool, erc6909U256_lor_zero] using
      OpenZeppelinBench.Pausable.pausableStorageLocStore_bool_false_offset0 evm slot
  · have hbeq : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hval
      apply hzero
      apply u256_inj
      simpa [UInt256.toNat] using hval
    have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hzero
    simp only [wordToElem, hbeq, Bool.false_eq_true, ↓reduceIte]
    simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc, setOperatorBoolWord, hiszero] using
      SimpleAuction.simpleAuctionStorageLocStore_bool_true_offset0 evm slot

theorem setOperatorOwnerWord_toNat (I : ExecutionEnv) :
    (setOperatorOwnerWord I).toNat = I.source.val := by
  unfold setOperatorOwnerWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem setOperatorOwnerWord_canonical (I : ExecutionEnv) :
    (setOperatorOwnerWord I).toNat < EVM.addressModulus := by
  rw [setOperatorOwnerWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem setOperatorOwner_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (setOperatorOwnerWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [setOperatorOwnerWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem setOperatorStore_spender (I : ExecutionEnv) :
    (setOperatorStore I).get? "spender" = some (setOperatorSpenderValue I) := by
  rw [setOperatorStore, store_get_ne _ _ (by decide), store_get_self]

theorem setOperatorStore_approved (I : ExecutionEnv) :
    (setOperatorStore I).get? "approved" = some (setOperatorApprovedValue I) := by
  rw [setOperatorStore, store_get_self]

theorem setOperatorStore_operatorApprovals (I : ExecutionEnv) :
    (setOperatorStore I).get? "_operatorApprovals" = none := by
  rw [setOperatorStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_setOperator_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.var "spender") = .ok (setOperatorSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setOperatorStore_spender]

theorem evalExpr_setOperator_approved (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.var "approved") = .ok (setOperatorApprovedValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setOperatorStore_approved]

theorem evalExpr_setOperator_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setOperator_zeroAddr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure,
    bind]

def setOperatorEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_operatorApprovals",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat))] }

theorem evalStorageRef_setOperator_operatorApproval (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := setOperatorStore I } evm
      (operatorApprovalRef sender (.var "spender")) =
        EvalResult.ok (setOperatorEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, operatorApprovalRef, sender,
    envValue, evalExpr_setOperator_spender, setOperatorEvaledRef, setOperatorSpenderValue,
    valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem setOperatorAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := setOperatorStore I } evm
      .storage (operatorApprovalRef sender (.var "spender")) (setOperatorApprovedValue I) =
        .ok ({ contract := contract, locals := setOperatorStore I },
          setOperatorPostState evm I) := by
  apply assignStorageRef_storage_bool_word
      (er := setOperatorEvaledRef evm I) (ty := boolSt)
      (loc := boolLoc (setOperatorSlot evm I))
      (word := setOperatorApprovedWord I)
      (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm I)
        (setOperatorBoolWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setOperatorSlot evm I))
          (setOperatorApprovedWord I)))
      (hbase := by
        simpa [operatorApprovalRef] using setOperatorStore_operatorApprovals I)
      (her := evalStorageRef_setOperator_operatorApproval evm I)
      (hty := by
        simp [storageTypeAt?, setOperatorEvaledRef, contract, storageDecls, boolSt,
          storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, setOperatorEvaledRef, setOperatorSlot])
      (hstore := by
        exact erc6909StorageLocStore_bool_word_offset0 evm (setOperatorSlot evm I)
          (setOperatorApprovedWord I))

theorem evalExpr_setOperator_sender_ne_zero_true (evm : EVM.State)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool true) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        false := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_setOperator_sender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_sender_ne_zero_false (evm : EVM.State)
    (hsource : evm.executionEnv.source = AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool false) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        true := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_setOperator_sender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_spender_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat ≠ AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool true) := by
  have hbeq : (setOperatorSpenderValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [setOperatorSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_setOperator_spender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_setOperator_spender_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (setOperatorSpenderWord I).toNat = AccountAddress.ofNat 0) :
    evalExpr? config { contract := contract, locals := setOperatorStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool false) := by
  have hbeq : (setOperatorSpenderValue I == Value.address (AccountAddress.ofNat 0)) = true := by
    simp [setOperatorSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_setOperator_spender, evalExpr_setOperator_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem erc6909SetOperatorBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (setOperatorSpenderWord evm.executionEnv).toNat ≠
        AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body
      (.returned { contract := contract, locals := setOperatorStore evm.executionEnv }
        (setOperatorPostState evm evm.executionEnv) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setOperator_sender_ne_zero_true evm hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setOperator_spender_ne_zero_true evm evm.executionEnv hspender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_setOperator_approved evm evm.executionEnv)
      (setOperatorAssign evm evm.executionEnv)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909SetOperatorBodyReverts_sender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_setOperator_sender_ne_zero_false evm hsource))

theorem erc6909SetOperatorBodyReverts_spender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (setOperatorSpenderWord evm.executionEnv).toNat =
        AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (setOperatorStore evm.executionEnv)
      setOperatorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setOperator_sender_ne_zero_true evm hsource)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_setOperator_spender_ne_zero_false evm evm.executionEnv hspender))

theorem erc6909SetOperatorSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 4)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 4).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_setOperator {cd : ByteArray}
    (hsel : (erc6909SelBytes 4 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some setOperatorTransition := by
  have hcd : cd.extract 0 4 = erc6909SelBytes 4 := (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition])
    (post := [supportsInterfaceTransition, transferTransition, transferFromTransition])
    rfl ?_ (by
      rw [selectorOf, erc6909SetOperatorSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]
    decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]
    decide

def setOperatorStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (setOperatorSlotI I) ⟨0⟩)

def setOperatorStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setOperatorBoolWord (setOperatorStorageWord σ I) (setOperatorApprovedWord I)

theorem setOperatorAccountAddress_ofNat_zero_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0 ↔ w = ⟨0⟩ := by
  exact approveAccountAddress_ofNat_zero_iff hcanon

theorem setOperatorSource_zero_iff (I : ExecutionEnv) :
    I.source = AccountAddress.ofNat 0 ↔ setOperatorOwnerWord I = ⟨0⟩ := by
  constructor
  · intro h
    apply u256_inj
    rw [setOperatorOwnerWord_toNat, h]
    rfl
  · intro h
    rw [← setOperatorOwner_ofNat I, h]
    rfl

theorem setOperatorBoolCanonJump {word : UInt256}
    (hbool : word = ⟨0⟩ ∨ word = ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) ≠ ⟨0⟩ := by
  rcases hbool with rfl | rfl <;> native_decide

theorem setOperatorBoolNoncanonJump {word : UInt256}
    (hnz : word ≠ ⟨0⟩) (hno : word ≠ ⟨1⟩) :
    UInt256.eq word (UInt256.isZero (UInt256.isZero word)) = ⟨0⟩ := by
  rw [isZero_eq_zero_of_ne hnz]
  have hone : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by native_decide
  rw [hone]
  exact u256_eq_of_ne hno

noncomputable def setOperatorOwnerHashMem (owner : UInt256) : ByteArray :=
  approveTwoWordHashMem owner ⟨1⟩ solcFreePtrMem

noncomputable def setOperatorOwnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((setOperatorOwnerHashMem owner).readWithPadding 0 64)))

noncomputable def setOperatorSpenderHashMem (owner spender : UInt256) : ByteArray :=
  approveTwoWordHashMem spender (setOperatorOwnerSlot owner) (setOperatorOwnerHashMem owner)

noncomputable def setOperatorSpenderSlot (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((setOperatorSpenderHashMem owner spender).readWithPadding 0 64)))

noncomputable def setOperatorEventMem (owner spender approved : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero approved))).write 0
    (setOperatorSpenderHashMem owner spender) 128 32

noncomputable def setOperatorReturnMem (owner spender approved : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (setOperatorEventMem owner spender approved) 128 32

theorem setOperatorOwnerHashMem_size (owner : UInt256) :
    (setOperatorOwnerHashMem owner).size = 96 := by
  unfold setOperatorOwnerHashMem
  exact approveTwoWordHashMem_size owner ⟨1⟩ solcFreePtrMem_size

theorem setOperatorSpenderHashMem_size (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).size = 96 := by
  unfold setOperatorSpenderHashMem
  exact approveTwoWordHashMem_size spender (setOperatorOwnerSlot owner)
    (setOperatorOwnerHashMem_size owner)

theorem setOperatorOwnerHashMem_read0_64 (owner : UInt256) :
    (setOperatorOwnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setOperatorOwnerHashMem
  exact approveTwoWordHashMem_read0_64 owner ⟨1⟩ solcFreePtrMem_size

theorem setOperatorSpenderHashMem_read0_64 (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (setOperatorOwnerSlot owner) := by
  unfold setOperatorSpenderHashMem
  exact approveTwoWordHashMem_read0_64 spender (setOperatorOwnerSlot owner)
    (setOperatorOwnerHashMem_size owner)

theorem setOperatorSpenderHashMem_read64 (owner spender : UInt256) :
    (setOperatorSpenderHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorSpenderHashMem setOperatorOwnerHashMem
  apply approveTwoWordHashMem_read64
  · exact approveTwoWordHashMem_size owner ⟨1⟩ solcFreePtrMem_size
  · exact approveTwoWordHashMem_read64 owner ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem setOperatorSpenderHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorSpenderHashMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorSpenderHashMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorSpenderHashMem_size]; decide) (by decide)
    (setOperatorSpenderHashMem_read64 owner spender)

theorem setOperatorEventMem_size (owner spender approved : UInt256) :
    (setOperatorEventMem owner spender approved).size = 160 := by
  unfold setOperatorEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [setOperatorSpenderHashMem_size]; omega)
      (by rw [setOperatorSpenderHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, setOperatorSpenderHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem setOperatorEventMem_read64 (owner spender approved : UInt256) :
    (setOperatorEventMem owner spender approved).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [setOperatorSpenderHashMem_size]; omega)
      (by rw [setOperatorSpenderHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, setOperatorSpenderHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, setOperatorSpenderHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [setOperatorSpenderHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [setOperatorSpenderHashMem_size]),
    setOperatorSpenderHashMem_read64]

theorem setOperatorEventMem_mload64 (owner spender approved : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorEventMem owner spender approved).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorEventMem owner spender approved).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorEventMem_size]; decide) (by decide)
    (setOperatorEventMem_read64 owner spender approved)

theorem setOperatorReturnMem_size (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).size = 160 := by
  unfold setOperatorReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, setOperatorEventMem_size, toByteArray_size]
  omega

theorem setOperatorReturnMem_read64 (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setOperatorReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega) (by omega),
    setOperatorEventMem_read64]

theorem setOperatorReturnMem_mload64 (owner spender approved : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setOperatorReturnMem owner spender approved).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setOperatorReturnMem owner spender approved).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [setOperatorReturnMem_size]; decide) (by decide)
    (setOperatorReturnMem_read64 owner spender approved)

theorem setOperatorReturnMem_read128 (owner spender approved : UInt256) :
    (setOperatorReturnMem owner spender approved).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setOperatorReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [setOperatorEventMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem setOperatorOwnerKeccakSlot (I : ExecutionEnv) :
    setOperatorOwnerSlot (setOperatorOwnerWord I) =
      mapSlot (keyValueToWord (.address I.source)) ⟨1⟩ := by
  have hownerKey : keyValueToWord (.address I.source) = setOperatorOwnerWord I := by
    rw [← setOperatorOwner_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (setOperatorOwnerWord_canonical I)
  unfold setOperatorOwnerSlot mapSlot
  rw [setOperatorOwnerHashMem_read0_64, hownerKey]
  exact mappingSlot_single (setOperatorOwnerWord I) ⟨1⟩

theorem setOperatorFinalKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (setOperatorSpenderWord I).toNat < EVM.addressModulus) :
    setOperatorSpenderSlot (setOperatorOwnerWord I) (setOperatorSpenderWord I) =
      setOperatorSlotI I := by
  have hownerKey : keyValueToWord (.address I.source) = setOperatorOwnerWord I := by
    rw [← setOperatorOwner_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (setOperatorOwnerWord_canonical I)
  have hspenderKey :
      keyValueToWord (.address (AccountAddress.ofNat (setOperatorSpenderWord I).toNat)) =
        setOperatorSpenderWord I :=
    erc6909ApproveKeyValueToWord_address_of_canonical _ hcanonSpender
  unfold setOperatorSpenderSlot setOperatorSlotI operatorApprovalSlot mapSlot
  rw [setOperatorSpenderHashMem_read0_64, setOperatorOwnerKeccakSlot I]
  rw [hownerKey, hspenderKey]
  exact mappingSlot_single (setOperatorSpenderWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (setOperatorOwnerWord I) ++
      UInt256.toByteArray (⟨1⟩ : UInt256))))

end OpenZeppelinBench.ERC6909
