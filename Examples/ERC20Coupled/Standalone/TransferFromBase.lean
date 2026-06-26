import Examples.ERC20Coupled.Standalone.Transfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace ERC20Standalone

/-! ## Source-level body for `transferFrom(address,address,uint256)` -/

/-- The raw ABI word for `transferFrom`'s `from` argument. -/
abbrev transferFromFromWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `to` argument. -/
abbrev transferFromToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `value` argument. -/
abbrev transferFromValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)

abbrev transferFromFromValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromFromWord I).toNat)

abbrev transferFromToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromToWord I).toNat)

abbrev transferFromValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromValueWord I).toNat)

abbrev transferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from" (transferFromFromValue I)).insert "to"
    (transferFromToValue I)).insert "value" (transferFromValueValue I)

def transferFromAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot
    (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (.address evm.executionEnv.source)

def transferFromAllowanceSlotI (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot
    (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (.address I.source)

def transferFromCurrentAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

abbrev transferFromCurrentAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat)

abbrev transferFromStoreCurrentAllowance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStore I).insert "currentAllowance" (transferFromCurrentAllowanceValue evm I)

def transferFromFromSlot (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))

def transferFromFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromFromSlot I)

abbrev transferFromFromBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromFromBalanceWord evm I).toNat)

abbrev transferFromStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreCurrentAllowance evm I).insert "fromBalance"
    (transferFromFromBalanceValue evm I)

def transferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat)

def transferFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromFromBalanceWord evm I).toNat - (transferFromValueWord I).toNat)

def transferFromAfterAllowanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)
    (transferFromAllowanceDebitWord evm I)

theorem transferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterAllowanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterAllowanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferFromAfterBalanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterAllowanceState evm I) evm.executionEnv.codeOwner
    (transferFromFromSlot I) (transferFromBalanceDebitWord evm I)

theorem transferFromAfterBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterBalanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterBalanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases (transferFromAfterAllowanceState evm I).accountMap.find? evm.executionEnv.codeOwner with
  | none => exact transferFromAfterAllowance_codeOwner evm I
  | some acc =>
      simp only [Option.option, State.setAccount, Account.updateStorage,
        transferFromAfterAllowance_codeOwner]

def transferFromToSlot (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address (AccountAddress.ofNat (transferFromToWord I).toNat))

def transferFromToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromAfterBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I)

abbrev transferFromToBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromToBalanceWord evm I).toNat)

abbrev transferFromStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreFromBalance evm I).insert "toBalance"
    (transferFromToBalanceValue evm I)

def transferFromNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromToBalanceWord evm I).toNat + (transferFromValueWord I).toNat

def transferFromNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromNewToNat evm I)

abbrev transferFromNewToValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromNewToNat evm I))

abbrev transferFromStoreNewToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreToBalance evm I).insert "newToBalance" (transferFromNewToValue evm I)

def transferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromToSlot I) (transferFromNewToWord evm I)

theorem transferFromNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    (transferFromNewToWord evm I).toNat = transferFromNewToNat evm I := by
  unfold transferFromNewToWord
  exact ulit_toNat' _ hfit

theorem decodeScalarWords_address_address_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
      .address (Ethereum.AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
      .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rfl

theorem decodeScalarWords_address_address_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_address_uint256_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

theorem decodeScalarWords_address_address_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · by_cases hcanon32 :
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
        · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
          rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]

theorem decodeCalldata_address_address_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, addr, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hcanon1)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]
  rw [hword68]

theorem decodeCalldata_address_address_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, addr, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_noncanon0 (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc0)]

theorem decodeCalldata_address_address_uint256_none_noncanon1 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, addr, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_noncanon1 (bytes := cd.toList.drop 4)
    htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hword36]; exact hnc1)]

theorem decodeCalldata_address_address_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, addr, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

theorem decodeCalldata_address_address_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, addr, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem erc20Decode_transferFrom_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferFromStore, transferFromFromValue,
    transferFromToValue, transferFromValueValue, transferFromFromWord, transferFromToWord,
    transferFromValueWord, calldataWord]
    using decodeCalldata_address_address_uint256_ok
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hcanonFrom hcanonTo

theorem erc20Decode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort

theorem erc20Decode_transferFrom_none_noncanon_from {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromFromWord]
    using decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hnc

theorem erc20Decode_transferFrom_none_noncanon_to {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromFromWord, transferFromToWord]
    using decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hcanonFrom hnc

theorem erc20Decode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hbig

theorem transferFromStore_from (I : ExecutionEnv) :
    (transferFromStore I).get? "from" = some (transferFromFromValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem transferFromStore_to (I : ExecutionEnv) :
    (transferFromStore I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_value (I : ExecutionEnv) :
    (transferFromStore I).get? "value" = some (transferFromValueValue I) := by
  rw [transferFromStore, store_get_self]

theorem transferFromStore_allowance (I : ExecutionEnv) :
    (transferFromStore I).get? "allowance" = none := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem transferFromStore_balanceOf (I : ExecutionEnv) :
    (transferFromStore I).get? "balanceOf" = none := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem transferFromStoreCurrentAllowance_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "currentAllowance" =
      some (transferFromCurrentAllowanceValue evm I) := by
  rw [transferFromStoreCurrentAllowance, store_get_self]

theorem transferFromStoreCurrentAllowance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "value" =
      some (transferFromValueValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_value]

theorem transferFromStoreCurrentAllowance_from (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "from" =
      some (transferFromFromValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_from]

theorem transferFromStoreCurrentAllowance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_to]

theorem transferFromStoreCurrentAllowance_allowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "allowance" = none := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
    transferFromStore_allowance]

theorem transferFromStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromFromBalanceValue evm I) := by
  rw [transferFromStoreFromBalance, store_get_self]

theorem transferFromStoreFromBalance_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "currentAllowance" =
      some (transferFromCurrentAllowanceValue evm I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_currentAllowance]

theorem transferFromStoreFromBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "value" =
      some (transferFromValueValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_value]

theorem transferFromStoreFromBalance_from (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "from" =
      some (transferFromFromValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_from]

theorem transferFromStoreFromBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "to" = some (transferFromToValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_to]

theorem transferFromStoreFromBalance_allowance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "allowance" = none := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_allowance]

theorem transferFromStoreFromBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance]
  rw [store_get_ne _ _ (by decide), transferFromStore_balanceOf]

theorem transferFromStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "toBalance" =
      some (transferFromToBalanceValue evm I) := by
  rw [transferFromStoreToBalance, store_get_self]

theorem transferFromStoreToBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "value" =
      some (transferFromValueValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_value]

theorem transferFromStoreToBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "to" =
      some (transferFromToValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_to]

theorem transferFromStoreToBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_balanceOf]

theorem transferFromStoreNewToBalance_newToBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreNewToBalance evm I).get? "newToBalance" =
      some (transferFromNewToValue evm I) := by
  rw [transferFromStoreNewToBalance, store_get_self]

theorem transferFromStoreNewToBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreNewToBalance evm I).get? "to" =
      some (transferFromToValue I) := by
  rw [transferFromStoreNewToBalance, store_get_ne _ _ (by decide),
    transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_to]

theorem transferFromStoreNewToBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreNewToBalance evm I).get? "balanceOf" = none := by
  rw [transferFromStoreNewToBalance, store_get_ne _ _ (by decide),
    transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_balanceOf]

theorem evalExpr_transferFrom_from (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_from]

theorem evalExpr_transferFrom_from_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_from]

theorem evalExpr_transferFrom_from_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_from]

theorem evalExpr_transferFrom_to_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_to]

theorem evalExpr_transferFrom_to_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreNewToBalance_to]

theorem evalExpr_transferFrom_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.var "value") = .ok (transferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_value]

def transferFromAllowanceEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)),
      .mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (allowanceRef (.var "from") sender) =
        .ok (transferFromAllowanceEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, evalExpr?,
    transferFromAllowanceEvaledRef, transferFromFromValue, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from]

theorem evalExpr_transferFrom_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (transferFromCurrentAllowanceValue evm I) := by
  conv_lhs => unfold evalExpr?
  rw [evalStorageRef_transferFrom_allowance]
  simp [transferFromAllowanceEvaledRef, transferFromAllowanceSlot,
    transferFromCurrentAllowanceWord, EvalResult.bind, EvalResult.ofOption, bind, pure,
    erc20StorageLocLoad_uint256]

theorem evalExpr_transferFrom_require_allowance_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_value]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, transferFromValueValue]
  exact henough

theorem evalExpr_transferFrom_require_allowance_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_value]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, transferFromValueValue]
  omega

def transferFromFromBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))] }

theorem evalStorageRef_transferFrom_from_balance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromFromBalanceEvaledRef,
    transferFromFromValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from_currentAllowance]

theorem evalStorageRef_transferFrom_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromFromBalanceEvaledRef,
    transferFromFromValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from_fromBalance]

theorem evalExpr_transferFrom_from_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue evm I) := by
  conv_lhs => unfold evalExpr?
  rw [evalStorageRef_transferFrom_from_balance_currentAllowance]
  simp [transferFromFromBalanceEvaledRef, transferFromFromSlot, transferFromFromBalanceWord,
    EvalResult.bind, EvalResult.ofOption, bind, pure, erc20StorageLocLoad_uint256]

theorem evalExpr_transferFrom_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromFromBalanceValue, transferFromValueValue]
  exact henough

theorem evalExpr_transferFrom_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromFromBalanceValue, transferFromValueValue]
  omega

theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (.binary .sub (.var "currentAllowance") (.var "value")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat
          ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromCurrentAllowanceWord evm I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromCurrentAllowanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_currentAllowance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, transferFromValueValue, hsub, htoNat]
  exact hsub

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterAllowanceState evm I) := by
  unfold assignStorageRef?
  simp only [allowanceRef]
  rw [transferFromStoreFromBalance_allowance]
  have href : evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      { base := "allowance", steps := [.mindex (.var "from"), .mindex sender] } =
        .ok (transferFromAllowanceEvaledRef evm I) := by
    simp [evalStorageRef, evalStorageRefStep, sender, envValue, evalExpr?,
      transferFromAllowanceEvaledRef, transferFromFromValue, valueToKey?,
      EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
      evalExpr_transferFrom_from_fromBalance]
  rw [href]
  simp [transferFromAfterAllowanceState, transferFromAllowanceEvaledRef,
    transferFromAllowanceSlot, EvalResult.bind, EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore evm (erc20Uint256Loc (transferFromAllowanceSlot evm I))
          (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I } :
          Frame), evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I } :
        Frame),
        transferFromAfterAllowanceState evm I)
  rw [erc20StorageLocStore_uint256]
  simp [transferFromAfterAllowanceState]

theorem evalExpr_transferFrom_balance_debit (evm evm' : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromFromBalanceWord evm I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat
          ((transferFromFromBalanceWord evm I).toNat - (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromBalanceDebitWord evm I).toNat =
      (transferFromFromBalanceWord evm I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromBalanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromFromBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromFromBalanceValue, transferFromValueValue, hsub, htoNat]
  exact hsub

theorem transferFromAssignFrom (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) (balanceOfRef (.var "from"))
      (.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterBalanceState evm I) := by
  unfold assignStorageRef?
  simp only [balanceOfRef]
  rw [transferFromStoreFromBalance_balanceOf]
  have href := evalStorageRef_transferFrom_from_balance_fromBalance evm
    (transferFromAfterAllowanceState evm I) I
  simp only [balanceOfRef] at href
  rw [href]
  simp [transferFromAfterBalanceState, transferFromFromBalanceEvaledRef,
    transferFromFromSlot, EvalResult.bind, EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore (transferFromAfterAllowanceState evm I)
          (erc20Uint256Loc (transferFromFromSlot I))
          (.int (Int.ofNat (transferFromBalanceDebitWord evm I).toNat)) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I } :
          Frame), evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I } :
        Frame),
        transferFromAfterBalanceState evm I)
  rw [erc20StorageLocStore_uint256]
  simp [transferFromAfterBalanceState, transferFromAfterAllowance_codeOwner]

def transferFromToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromToWord I).toNat))] }

theorem evalStorageRef_transferFrom_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromToEvaledRef,
    transferFromToValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_fromBalance]

theorem evalStorageRef_transferFrom_to_balance_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromToEvaledRef,
    transferFromToValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_newToBalance]

theorem evalExpr_transferFrom_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterBalanceState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferFromToBalanceValue evm I) := by
  conv_lhs => unfold evalExpr?
  rw [evalStorageRef_transferFrom_to_balance_fromBalance]
  simp [transferFromToEvaledRef, transferFromToSlot, transferFromToBalanceWord,
    EvalResult.bind, EvalResult.ofOption, bind, pure, erc20StorageLocLoad_uint256,
    transferFromAfterBalance_codeOwner]

theorem evalExpr_transferFrom_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferFromNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, transferFromToBalanceValue, transferFromValueValue,
    transferFromNewToValue, transferFromNewToNat, uint256Int, hlt]
  constructor
  · omega
  · have hfitNat :
        (transferFromToBalanceWord evm I).toNat + (transferFromValueWord I).toNat < 2 ^ 256 := by
      simpa [transferFromNewToNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, transferFromToBalanceValue, transferFromValueValue,
    transferFromNewToValue, transferFromNewToNat, uint256Int]
  intro _
  simpa [transferFromNewToNat] using hge

theorem evalExpr_transferFrom_newToBalance_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
      (transferFromAfterBalanceState evm I) (.var "newToBalance") =
        .ok (transferFromNewToValue evm I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreNewToBalance_newToBalance]

theorem transferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
      (transferFromAfterBalanceState evm I) (balanceOfRef (.var "to"))
      (transferFromNewToValue evm I) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreNewToBalance evm I },
          transferFromPostState evm I) := by
  unfold assignStorageRef?
  simp only [balanceOfRef]
  rw [transferFromStoreNewToBalance_balanceOf]
  have href := evalStorageRef_transferFrom_to_balance_newToBalance evm
    (transferFromAfterBalanceState evm I) I
  simp only [balanceOfRef] at href
  rw [href]
  simp [transferFromPostState, transferFromToEvaledRef, transferFromToSlot,
    transferFromNewToValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore (transferFromAfterBalanceState evm I)
          (erc20Uint256Loc (transferFromToSlot I))
          (.int (Int.ofNat (transferFromNewToNat evm I))) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } :
          Frame), evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } :
        Frame),
        transferFromPostState evm I)
  rw [← transferFromNewToWord_toNat evm I hfit]
  rw [erc20StorageLocStore_uint256]
  simp [transferFromPostState, transferFromAfterBalance_codeOwner]

/-! ## EVM trace for `transferFrom(address,address,uint256)` -/

abbrev transferFromSenderWord (I : ExecutionEnv) : UInt256 :=
  approveOwnerWord I

theorem transferFromSenderWord_canonical (I : ExecutionEnv) :
    (transferFromSenderWord I).toNat < EVM.addressModulus :=
  approveOwnerWord_canonical I

theorem transferFromSender_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (transferFromSenderWord I).toNat = I.source :=
  approveOwner_ofNat I

theorem transferFromAllowanceKeccakSlot (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOuterHashMem (transferFromFromWord I)
          (transferFromSenderWord I)).readWithPadding 0 64)))
      = transferFromAllowanceSlotI I := by
  rw [allowanceOuterKeccakSlot_word (transferFromFromWord I) (transferFromSenderWord I)
    hcanonFrom (transferFromSenderWord_canonical I)]
  unfold transferFromAllowanceSlotI transferFromSenderWord
  rw [approveOwner_ofNat]

theorem transferFromFromKeccakSlot (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (transferFromFromWord I)).readWithPadding 0 64)))
      = transferFromFromSlot I := by
  rw [balanceOfKeccakSlot_word (transferFromFromWord I) hcanonFrom]
  rfl

theorem transferFromToKeccakSlot (I : ExecutionEnv)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (transferFromToWord I)).readWithPadding 0 64)))
      = transferFromToSlot I := by
  rw [balanceOfKeccakSlot_word (transferFromToWord I) hcanonTo]
  rfl

/-- ERC20-specific storage-layout separation: `allowance[from][msg.sender]` and
    `balanceOf[from]` occupy distinct Solidity mapping slots. This is the only
    contract-layout fact needed because the compiled bytecode reloads
    `balanceOf[from]` after storing the allowance debit, while the source body keeps
    the old `fromBalance` in a local variable. -/
theorem transferFromAllowanceSlot_ne_fromSlot (I : ExecutionEnv) :
    transferFromFromSlot I ≠ transferFromAllowanceSlotI I := by
  unfold transferFromFromSlot transferFromAllowanceSlotI
  exact erc20BalanceOfSlot_ne_allowanceSlot _ _

/-- Writing `allowance[from][msg.sender]` leaves the `balanceOf[from]` lookup untouched. -/
theorem transferFromAllowanceStore_preservesFromBalance
    (σ : AccountMap) (I : ExecutionEnv) (v : UInt256) :
    ((sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I) v).find? I.codeOwner
        |>.option ⟨0⟩ (fun acc => acc.storage.findD (transferFromFromSlot I) ⟨0⟩)) =
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (transferFromFromSlot I) ⟨0⟩)) := by
  unfold sstoreAccountMap
  cases hacc : σ.find? I.codeOwner with
  | none =>
      simp only [Option.option]
      rw [hacc]
  | some acc =>
      simp only [Option.option]
      rw [erc20AccountMap_find_insert_self]
      by_cases hzero : (v == default) = true
      · simpa [hzero] using erc20Storage_findD_update_ne acc.storage (transferFromFromSlot I)
          (transferFromAllowanceSlotI I) v default (transferFromAllowanceSlot_ne_fromSlot I)
      · simpa [hzero] using erc20Storage_findD_update_ne acc.storage (transferFromFromSlot I)
          (transferFromAllowanceSlotI I) v default (transferFromAllowanceSlot_ne_fromSlot I)

theorem allowanceOuterHashMem_extract64_eq_solcFreePtrMem (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).extract 64 (allowanceOuterHashMem owner spender).size =
      solcFreePtrMem.extract 64 96 := by
  have hallow := allowanceOuterHashMem_read64 owner spender
  rw [readWithPadding_eq_extract _ 64 (by rw [allowanceOuterHashMem_size])] at hallow
  have hsolc := solcFreePtrMem_read64
  rw [readWithPadding_eq_extract _ 64 (by rw [solcFreePtrMem_size])] at hsolc
  rw [allowanceOuterHashMem_size]
  exact hallow.trans hsolc.symm

theorem allowanceOuterHashMem_writeBalanceSlot (owner spender : UInt256) :
    (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
      ((UInt256.toByteArray owner).write 0 (allowanceOuterHashMem owner spender) 0 32)
      32 32 = balanceOfHashMem owner := by
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hzeroFull :
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hallow0 : (allowanceOuterHashMem owner spender).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hmidSize :
      ((UInt256.toByteArray owner).write 0 (allowanceOuterHashMem owner spender) 0 32).size =
        96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [allowanceOuterHashMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, allowanceOuterHashMem_size,
      toByteArray_size]
    omega
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hmidSize]; omega)]
  have hhead :
      ((UInt256.toByteArray owner).write 0
        (allowanceOuterHashMem owner spender) 0 32).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [allowanceOuterHashMem_size]; omega)]
    rw [hallow0, hownerFull, ByteArray.empty_append]
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  have htail :
      ((UInt256.toByteArray owner).write 0
        (allowanceOuterHashMem owner spender) 0 32).extract 64
          ((UInt256.toByteArray owner).write 0
            (allowanceOuterHashMem owner spender) 0 32).size =
        solcFreePtrMem.extract 64 96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [allowanceOuterHashMem_size]; omega)]
    rw [hallow0, hownerFull, ByteArray.empty_append]
    have htail' :
        (UInt256.toByteArray owner ++
            (allowanceOuterHashMem owner spender).extract 32
              (allowanceOuterHashMem owner spender).size).extract 64
            (UInt256.toByteArray owner ++
              (allowanceOuterHashMem owner spender).extract 32
                (allowanceOuterHashMem owner spender).size).size =
          (allowanceOuterHashMem owner spender).extract 64
            (allowanceOuterHashMem owner spender).size := by
      rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
      rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract,
        allowanceOuterHashMem_size]
      rw [extract_extract_BA]
      rfl
    rw [htail']
    exact allowanceOuterHashMem_extract64_eq_solcFreePtrMem owner spender
  rw [hhead, htail, hzeroFull]
  have hsolc0 : solcFreePtrMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hsolcMidSize :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).size = 96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega
  have hsolcHead :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [hsolc0, hownerFull, ByteArray.empty_append]
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  have hsolcTail :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).extract 64
          ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).size =
        solcFreePtrMem.extract 64 96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [hsolc0, hownerFull, ByteArray.empty_append]
    have htail' :
        (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 solcFreePtrMem.size).extract 64
            (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 solcFreePtrMem.size).size =
          solcFreePtrMem.extract 64 96 := by
      rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
      rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, solcFreePtrMem_size]
      rw [extract_extract_BA]
      rfl
    exact htail'
  rw [← transferBalanceOwnerMem_writeSlot owner]
  unfold transferBalanceOwnerMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hsolcMidSize]; omega)]
  rw [hsolcHead, hsolcTail, hzeroFull]

theorem balanceOfHashMem_writeAllowanceSlot (owner : UInt256) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (balanceOfHashMem owner) 32 32 =
      allowanceInnerHashMem owner := by
  have honeFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hhead : (balanceOfHashMem owner).extract 0 32 = UInt256.toByteArray owner := by
    have h := balanceOfHashMem_read0 owner
    rw [readWithPadding_eq_extract _ 0 (by rw [balanceOfHashMem_size]; omega)] at h
    exact h
  have htail :
      (balanceOfHashMem owner).extract 64 (balanceOfHashMem owner).size =
        solcFreePtrMem.extract 64 96 := by
    have hbal := balanceOfHashMem_read64 owner
    rw [readWithPadding_eq_extract _ 64 (by rw [balanceOfHashMem_size])] at hbal
    have hsolc := solcFreePtrMem_read64
    rw [readWithPadding_eq_extract _ 64 (by rw [solcFreePtrMem_size])] at hsolc
    rw [balanceOfHashMem_size]
    exact hbal.trans hsolc.symm
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [balanceOfHashMem_size]; omega)]
  rw [hhead, htail, honeFull]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hsolc0 : solcFreePtrMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  have hsolcMidSize :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).size = 96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega
  have hsolcHead :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [hsolc0, hownerFull, ByteArray.empty_append]
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  have hsolcTail :
      ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).extract 64
          ((UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32).size =
        solcFreePtrMem.extract 64 96 := by
    rw [write32_eq _ _ 0 (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; omega)]
    rw [hsolc0, hownerFull, ByteArray.empty_append]
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, solcFreePtrMem_size]
    rw [extract_extract_BA]
    rfl
  rw [← approveInnerOwnerMem_writeSlot owner]
  unfold approveInnerOwnerMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hsolcMidSize]; omega)]
  rw [hsolcHead, hsolcTail, honeFull]

/-- Padded word for `"ERC20: insufficient allowance"`. -/
def transferFromInsufficientAllowanceWord : UInt256 :=
  ⟨31354931781638678538084197150757782427756587561754988975511141185730285404160⟩

noncomputable def transferFromInsufficientAllowanceSelectorMem
    (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray transferErrorSelector).write 0 (allowanceOuterHashMem owner spender) 128 32

noncomputable def transferFromInsufficientAllowanceOffsetMem
    (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (transferFromInsufficientAllowanceSelectorMem owner spender) 132 32

noncomputable def transferFromInsufficientAllowanceLengthMem
    (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨29⟩ : UInt256)).write 0
    (transferFromInsufficientAllowanceOffsetMem owner spender) 164 32

noncomputable def transferFromInsufficientAllowanceStringMem
    (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray transferFromInsufficientAllowanceWord).write 0
    (transferFromInsufficientAllowanceLengthMem owner spender) 196 32

theorem transferFromInsufficientAllowanceSelectorMem_size (owner spender : UInt256) :
    (transferFromInsufficientAllowanceSelectorMem owner spender).size = 160 := by
  unfold transferFromInsufficientAllowanceSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceOuterHashMem_size]; omega)
      (by rw [allowanceOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferFromInsufficientAllowanceOffsetMem_size (owner spender : UInt256) :
    (transferFromInsufficientAllowanceOffsetMem owner spender).size = 164 := by
  unfold transferFromInsufficientAllowanceOffsetMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceSelectorMem_size, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceLengthMem_size (owner spender : UInt256) :
    (transferFromInsufficientAllowanceLengthMem owner spender).size = 196 := by
  unfold transferFromInsufficientAllowanceLengthMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceOffsetMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceOffsetMem_size, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceStringMem_size (owner spender : UInt256) :
    (transferFromInsufficientAllowanceStringMem owner spender).size = 228 := by
  unfold transferFromInsufficientAllowanceStringMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceLengthMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceLengthMem_size, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceSelectorMem_read64 (owner spender : UInt256) :
    (transferFromInsufficientAllowanceSelectorMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceOuterHashMem_size]; omega)
      (by rw [allowanceOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [allowanceOuterHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [allowanceOuterHashMem_size])]
  exact allowanceOuterHashMem_read64 owner spender

theorem transferFromInsufficientAllowanceOffsetMem_read64 (owner spender : UInt256) :
    (transferFromInsufficientAllowanceOffsetMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceOffsetMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorMem_size]; omega) (by omega),
    transferFromInsufficientAllowanceSelectorMem_read64]

theorem transferFromInsufficientAllowanceLengthMem_read64 (owner spender : UInt256) :
    (transferFromInsufficientAllowanceLengthMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceLengthMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceOffsetMem_size]) (by omega),
    transferFromInsufficientAllowanceOffsetMem_read64]

theorem transferFromInsufficientAllowanceStringMem_read64 (owner spender : UInt256) :
    (transferFromInsufficientAllowanceStringMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceStringMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceLengthMem_size]) (by omega),
    transferFromInsufficientAllowanceLengthMem_read64]

theorem transferFromInsufficientAllowanceStringMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferFromInsufficientAllowanceStringMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferFromInsufficientAllowanceStringMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferFromInsufficientAllowanceStringMem_size]; decide)
    (by decide) (transferFromInsufficientAllowanceStringMem_read64 owner spender)

theorem standaloneTransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2098⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨204⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨199⟩, swap2, swap1, push2 ⟨2098⟩, jump erc20_jd ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem standaloneTransferFromX_dec1874_from {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨2134⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
          ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using solcCalldataStaticLenCheckOk (words := 3) hsz100 hszhi hsize
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨2134⟩, dup7, dup3, dup8, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `from` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2134` from chain. -/
theorem standaloneTransferFromX_dec2134 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2134⟩
        [transferFromFromWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec1874_from (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz100 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanonFrom (by jump_dest) (by evm_ov)

theorem standaloneTransferFromX_dec1874_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨2151⟩, ⟨32⟩, ⟨0⟩,
          ⟨0⟩, transferFromFromWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec2134 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨2151⟩, dup7, dup3, dup8,
    add, push2 ⟨1874⟩, jump erc20_jd ]⟩

/-- The `to` address decode (success): a second application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2151` to chain. -/
theorem standaloneTransferFromX_dec2151 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2151⟩
        [transferFromToWord I, ⟨32⟩, ⟨0⟩, ⟨0⟩, transferFromFromWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec1874_to (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.erc20DecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem standaloneTransferFromX_dec1925_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
        [⟨4⟩ + ⟨64⟩, UInt256.ofNat I.calldata.size, ⟨2168⟩, ⟨64⟩, ⟨0⟩,
          transferFromToWord I, transferFromFromWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec2151 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨2168⟩, dup7, dup3, dup8,
    add, push2 ⟨1925⟩, jump erc20_jd ]⟩

theorem standaloneTransferFromX_dec1903_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1903⟩
        [transferFromValueWord I, ⟨1939⟩, transferFromValueWord I, ⟨4⟩ + ⟨64⟩,
          UInt256.ofNat I.calldata.size, ⟨2168⟩, ⟨64⟩, ⟨0⟩, transferFromToWord I,
          transferFromFromWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨199⟩,
          ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec1925_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1939⟩, dup2,
    push2 ⟨1903⟩, jump erc20_jd ]⟩

theorem standaloneTransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨613⟩
        [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd1903⟩ := standaloneTransferFromX_dec1903_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have rd1894 := evm_run rd1903 with [
    jumpdest, push2 ⟨1912⟩, dup2, push2 ⟨1894⟩, jump erc20_jd ]
  have rd1912 := rd1894.erc20Routine0766 erc20_jd (by evm_ov)
  have hclean : UInt256.eq (transferFromValueWord I) (transferFromValueWord I) = ⟨1⟩ :=
    erc20Ueq_self (transferFromValueWord I)
  have rd1939 := evm_run rd1912 with [
    jumpdest, dup2, eq, push2 ⟨1922⟩, jumpiT (by rw [hclean]; decide) erc20_jd,
    jumpdest, pop, jump erc20_jd ]
  have rd2168 := evm_run rd1939 with [
    jumpdest, swap3, swap2, pop, pop, jump erc20_jd ]
  exact ⟨_, _, evm_run rd2168 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop, swap3, jump erc20_jd,
    jumpdest, push2 ⟨613⟩, jump erc20_jd ]⟩

/-- The `transferFrom` body loads `allowance[from][msg.sender]` and passes the allowance
    requirement, leaving the loaded allowance and a scratch zero on the stack. -/
theorem standaloneTransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 3) hsz4
      (by simpa using hshort) hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2120⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem standaloneTransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 3) hbig hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2120⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem standaloneTransferFromX_noncanon_from {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferFromFromWord I)
      (UInt256.land (transferFromFromWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec1874_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem standaloneTransferFromX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (transferFromToWord I)
      (UInt256.land (transferFromToWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := standaloneTransferFromX_dec1874_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20TransferFromSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (erc20ByteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [approveTransition, totalSupplyTransition, transferFromTransition, balanceOfTransition,
      transferTransition, allowanceTransition] cd = some transferFromTransition
  rw [dispatchList_cons, selectorOf, erc20ApproveSelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20TotalSupplySelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20TransferFromSelectorBytes]
  rw [if_pos (by rw [hcd]; decide)]

