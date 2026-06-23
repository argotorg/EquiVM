import Examples.OpenZeppelinBench.ERC6909.BalanceOf
import Examples.OpenZeppelinBench.ERC6909.Approve
import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.SolcDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `transfer(address,uint256,uint256)` -/

abbrev zeroAccountAddress : AccountAddress :=
  AccountAddress.ofNat 0

/-- The raw ABI word for `transfer`'s `receiver` argument. -/
abbrev transferReceiverWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transfer`'s `id` argument. -/
abbrev transferIdWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transfer`'s `amount` argument. -/
abbrev transferAmountWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)

abbrev transferReceiverValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferReceiverWord I).toNat)

abbrev transferIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferIdWord I).toNat)

abbrev transferAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferAmountWord I).toNat)

abbrev transferStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "receiver" (transferReceiverValue I)).insert "id"
    (transferIdValue I)).insert "amount" (transferAmountValue I)

abbrev transferSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem transferSenderWord_toNat (I : ExecutionEnv) :
    (transferSenderWord I).toNat = I.source.val := by
  unfold transferSenderWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem transferSenderWord_canonical (I : ExecutionEnv) :
    (transferSenderWord I).toNat < EVM.addressModulus := by
  rw [transferSenderWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem transferSender_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (transferSenderWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [transferSenderWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

def transferFromSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address evm.executionEnv.source) (.int (Int.ofNat (transferIdWord I).toNat))

def transferFromSlotI (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address I.source) (.int (Int.ofNat (transferIdWord I).toNat))

def transferToSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferReceiverWord I).toNat))
    (.int (Int.ofNat (transferIdWord I).toNat))

def transferFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromSlot evm I)

abbrev transferFromBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromBalanceWord evm I).toNat)

abbrev transferStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStore I).insert "fromBalance" (transferFromBalanceValue evm I)

def transferDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromBalanceWord evm I).toNat - (transferAmountWord I).toNat)

def transferAfterDebitState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromSlot evm I)
    (transferDebitWord evm I)

theorem transferAfterDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferAfterDebitState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferAfterDebitState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferAfterDebitState evm I) evm.executionEnv.codeOwner
    (transferToSlot I)

abbrev transferToBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferToBalanceWord evm I).toNat)

abbrev transferStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStoreFromBalance evm I).insert "toBalance" (transferToBalanceValue evm I)

def transferNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferToBalanceWord evm I).toNat + (transferAmountWord I).toNat

def transferNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferNewToNat evm I)

abbrev transferNewToValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferNewToNat evm I))

abbrev transferStoreNewToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStoreToBalance evm I).insert "newToBalance" (transferNewToValue evm I)

def transferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferAfterDebitState evm I) evm.executionEnv.codeOwner
    (transferToSlot I) (transferNewToWord evm I)

theorem transferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    (transferNewToWord evm I).toNat = transferNewToNat evm I := by
  unfold transferNewToWord
  exact ulit_toNat' _ hfit

/-! ### ABI decoding -/

-- PROMOTE -> Common.lean
theorem decodeScalarWords_address_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, uint256, uint256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
      .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
      .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) hlen32]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rfl

-- PROMOTE -> Common.lean
theorem decodeScalarWords_address_uint256_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

-- PROMOTE -> Common.lean
theorem decodeScalarWords_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none
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
        rw [decodeScalarWord_uint256_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_uint256_ok (start := 32) htake32]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]

-- PROMOTE -> Common.lean
theorem decodeCalldata_address_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
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
    (types := [addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68' (by rw [hword4]; exact hcanon0)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68]

-- PROMOTE -> Common.lean
theorem decodeCalldata_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_none_noncanon0 (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc0)]

-- PROMOTE -> Common.lean
theorem decodeCalldata_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_uint256_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]; omega)]

-- PROMOTE -> Common.lean
theorem decodeCalldata_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem erc6909Decode_transfer_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata =
        some (transferStore I) := by
  show decodeCalldata ["receiver", "id", "amount"] [addr, uint256, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferReceiverValue,
    transferIdValue, transferAmountValue, transferReceiverWord, transferIdWord,
    transferAmountWord, calldataWord]
    using decodeCalldata_address_uint256_uint256_ok
      (cd := I.calldata) (x := "receiver") (y := "id") (z := "amount")
      hsz100 hbig hcanonReceiver

theorem erc6909Decode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["receiver", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_uint256_uint256_none_short
      (cd := I.calldata) (x := "receiver") (y := "id") (z := "amount") hsz4 hshort

theorem erc6909Decode_transfer_none_noncanon_receiver {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["receiver", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferReceiverWord]
    using decodeCalldata_address_uint256_uint256_none_noncanon0
      (cd := I.calldata) (x := "receiver") (y := "id") (z := "amount")
      hsz100 hbig hnc

theorem erc6909Decode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["receiver", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_uint256_uint256_none_huge
      (cd := I.calldata) (x := "receiver") (y := "id") (z := "amount") hbig

theorem erc6909TransferSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 2)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 2).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_transfer {cd : ByteArray}
    (hsel : (erc6909SelBytes 2 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferTransition := by
  have hcd : cd.extract 0 4 = erc6909SelBytes 2 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition, supportsInterfaceTransition])
    (post := [transferFromTransition])
    rfl ?_ (by
      rw [selectorOf, erc6909TransferSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SetOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SupportsInterfaceSelectorBytes, hcd]; decide

/-! ### Source expression and storage facts -/

theorem transferStore_receiver (I : ExecutionEnv) :
    (transferStore I).get? "receiver" = some (transferReceiverValue I) := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem transferStore_id (I : ExecutionEnv) :
    (transferStore I).get? "id" = some (transferIdValue I) := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferStore_amount (I : ExecutionEnv) :
    (transferStore I).get? "amount" = some (transferAmountValue I) := by
  rw [transferStore, store_get_self]

theorem transferStore_balances (I : ExecutionEnv) :
    (transferStore I).get? "_balances" = none := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem transferStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromBalanceValue evm I) := by
  rw [transferStoreFromBalance, store_get_self]

theorem transferStoreFromBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "receiver" = some (transferReceiverValue I) := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_receiver]

theorem transferStoreFromBalance_id (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "id" = some (transferIdValue I) := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_id]

theorem transferStoreFromBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "amount" = some (transferAmountValue I) := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_amount]

theorem transferStoreFromBalance_balances (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "_balances" = none := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_balances]

theorem transferStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreToBalance evm I).get? "toBalance" =
      some (transferToBalanceValue evm I) := by
  rw [transferStoreToBalance, store_get_self]

theorem transferStoreToBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreToBalance evm I).get? "amount" = some (transferAmountValue I) := by
  rw [transferStoreToBalance, store_get_ne _ _ (by decide), transferStoreFromBalance_amount]

theorem transferStoreNewToBalance_newToBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "newToBalance" =
      some (transferNewToValue evm I) := by
  rw [transferStoreNewToBalance, store_get_self]

theorem transferStoreNewToBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "receiver" = some (transferReceiverValue I) := by
  rw [transferStoreNewToBalance, store_get_ne _ _ (by decide), transferStoreToBalance,
    store_get_ne _ _ (by decide), transferStoreFromBalance_receiver]

theorem transferStoreNewToBalance_balances (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "_balances" = none := by
  rw [transferStoreNewToBalance, store_get_ne _ _ (by decide), transferStoreToBalance,
    store_get_ne _ _ (by decide), transferStoreFromBalance_balances]

theorem evalExpr_transfer_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transfer_receiver (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.var "receiver") = .ok (transferReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_receiver]

theorem evalExpr_transfer_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.var "id") = .ok (transferIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_id]

theorem evalExpr_transfer_amount_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (.var "amount") = .ok (transferAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_amount]

theorem evalExpr_transfer_receiver_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (.var "receiver") = .ok (transferReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_receiver]

theorem evalExpr_transfer_id_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (.var "id") = .ok (transferIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_id]

theorem evalExpr_transfer_receiver_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreToBalance evm I } evm'
      (.var "receiver") = .ok (transferReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreToBalance, store_get_ne _ _ (by decide), transferStoreFromBalance_receiver]

theorem evalExpr_transfer_id_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreToBalance evm I } evm'
      (.var "id") = .ok (transferIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreToBalance, store_get_ne _ _ (by decide), transferStoreFromBalance_id]

theorem evalExpr_transfer_receiver_newToBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreNewToBalance evm I } evm'
      (.var "receiver") = .ok (transferReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_receiver]

theorem evalExpr_transfer_id_newToBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreNewToBalance evm I } evm'
      (.var "id") = .ok (transferIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance, store_get_ne _ _ (by decide), transferStoreToBalance,
    store_get_ne _ _ (by decide), transferStoreFromBalance_id]

theorem evalExpr_transfer_sender_nonzero_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : evm.executionEnv.source ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.binary .ne sender zeroAddr) = .ok (.bool true) := by
  simp only [sender, zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, envValue]
  have hne : ((.address evm.executionEnv.source : Value) ==
      .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, hne]

theorem evalExpr_transfer_sender_nonzero_false (evm : EVM.State) (I : ExecutionEnv)
    (hz : evm.executionEnv.source = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.binary .ne sender zeroAddr) = .ok (.bool false) := by
  simp only [sender, zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, envValue]
  rw [hz]
  simp [zeroAccountAddress, evalBinaryOp?]

theorem evalExpr_transfer_receiver_nonzero_true (evm : EVM.State) (I : ExecutionEnv)
    (hnz : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [transferStore_receiver]
  have hne :
      ((transferReceiverValue I : Value) == .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferReceiverValue, Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, transferReceiverValue, hne]

theorem evalExpr_transfer_receiver_nonzero_false (evm : EVM.State) (I : ExecutionEnv)
    (hz : AccountAddress.ofNat (transferReceiverWord I).toNat = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [transferStore_receiver]
  simp [evalBinaryOp?, transferReceiverValue, zeroAccountAddress, hz]

def transferFromEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.int (Int.ofNat (transferIdWord I).toNat))] }

theorem evalStorageRef_transfer_from_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStore I } evm
      (balanceRef sender (.var "id")) = .ok (transferFromEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, sender, envValue,
    evalExpr_transfer_id, transferFromEvaledRef, transferIdValue, valueToKey?,
    EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transfer_from_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.storage (balanceRef sender (.var "id"))) =
        .ok (transferFromBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSlot evm I))
    (hbase := by simpa [balanceRef] using transferStore_balances I)
    (her := evalStorageRef_transfer_from_balance evm I)
    (hty := by
      simp [storageTypeAt?, transferFromEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromEvaledRef, transferFromSlot])]
  simp [transferFromEvaledRef, transferFromSlot, transferFromBalanceWord,
    erc6909StorageLocLoad_uint256]

theorem evalExpr_transfer_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferAmountWord I).toNat ≤ (transferFromBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_amount]
  simp [evalBinaryOp?, transferFromBalanceValue, transferAmountValue]
  exact henough

theorem evalExpr_transfer_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromBalanceWord evm I).toNat < (transferAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_amount]
  simp [evalBinaryOp?, transferFromBalanceValue, transferAmountValue]
  omega

theorem evalExpr_transfer_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferAmountWord I).toNat ≤ (transferFromBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromBalanceWord evm I).toNat -
          Int.ofNat (transferAmountWord I).toNat =
        Int.ofNat ((transferFromBalanceWord evm I).toNat - (transferAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferDebitWord evm I).toNat =
      (transferFromBalanceWord evm I).toNat - (transferAmountWord I).toNat := by
    unfold transferDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_amount]
  simp [evalBinaryOp?, transferFromBalanceValue, transferAmountValue, hsub, htoNat]
  exact hsub

theorem evalStorageRef_transfer_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (balanceRef sender (.var "id")) = .ok (transferFromEvaledRef evm' I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, sender, envValue,
    evalExpr_transfer_id_fromBalance, transferFromEvaledRef, transferIdValue,
    valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem transferAssignFrom (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferStoreFromBalance evm I } evm
      .storage (balanceRef sender (.var "id"))
      (.int (Int.ofNat (transferDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferStoreFromBalance evm I },
          transferAfterDebitState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSlot evm I))
      (hbase := by simpa [balanceRef] using transferStoreFromBalance_balances evm I)
      (her := by
        simpa [balanceRef] using evalStorageRef_transfer_from_balance_fromBalance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromEvaledRef, transferFromSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferAfterDebitState, transferFromSlot]

def transferToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferReceiverWord I).toNat)),
      .mindex (.int (Int.ofNat (transferIdWord I).toNat))] }

theorem evalStorageRef_transfer_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, transferToEvaledRef,
    evalExpr_transfer_receiver_fromBalance, evalExpr_transfer_id_fromBalance,
    transferReceiverValue, transferIdValue, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_transfer_to_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferStoreToBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, transferToEvaledRef,
    evalExpr_transfer_receiver_toBalance, evalExpr_transfer_id_toBalance,
    transferReceiverValue, transferIdValue, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_transfer_to_balance_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferStoreNewToBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, transferToEvaledRef,
    transferReceiverValue, transferIdValue, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_transfer_receiver_newToBalance,
    evalExpr_transfer_id_newToBalance]

theorem evalExpr_transfer_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreFromBalance evm I }
      (transferAfterDebitState evm I) (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferToBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferToSlot I))
    (hbase := by simpa [balanceRef] using transferStoreFromBalance_balances evm I)
    (her := evalStorageRef_transfer_to_balance_fromBalance evm (transferAfterDebitState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferToEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferToEvaledRef, transferToSlot])]
  simp [transferToEvaledRef, transferToSlot, transferToBalanceWord,
    erc6909StorageLocLoad_uint256, transferAfterDebit_codeOwner]

theorem evalExpr_transfer_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_amount]
  simp [evalBinaryOp?, transferToBalanceValue, transferAmountValue, transferNewToValue,
    transferNewToNat, uint256Int, hlt]
  constructor
  · omega
  · have hfitNat :
        (transferToBalanceWord evm I).toNat + (transferAmountWord I).toNat < 2 ^ 256 := by
      simpa [transferNewToNat, UInt256.size] using hfit
    omega

theorem evalExpr_transfer_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_amount]
  simp [evalBinaryOp?, transferToBalanceValue, transferAmountValue, transferNewToValue,
    transferNewToNat, uint256Int]
  intro _
  simpa [transferNewToNat] using hge

theorem evalExpr_transfer_newToBalance_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferStoreNewToBalance evm I }
      (transferAfterDebitState evm I) (.var "newToBalance") =
        .ok (transferNewToValue evm I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_newToBalance]

theorem transferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I) .storage (balanceRef (.var "receiver") (.var "id"))
      (transferNewToValue evm I) =
        .ok ({ contract := contract, locals := transferStoreToBalance evm I },
          transferPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferToSlot I))
      (hbase := by
        simp [balanceRef, transferStoreToBalance, transferStoreFromBalance, transferStore])
      (her := evalStorageRef_transfer_to_balance_toBalance evm
        (transferAfterDebitState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferToEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferToEvaledRef, transferToSlot])
  rw [← transferNewToWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferPostState, transferToSlot, transferAfterDebit_codeOwner]

theorem erc6909TransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsender : evm.executionEnv.source ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferAmountWord I).toNat ≤ (transferFromBalanceWord evm I).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body
      (.returned { contract := contract, locals := transferStoreToBalance evm I }
        (transferPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_sender_nonzero_true evm I hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_receiver_nonzero_true evm I hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_newToBalance evm I hfit)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909TransferBodyCore (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsender : evm.executionEnv.source ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferAmountWord I).toNat ≤ (transferFromBalanceWord evm I).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body
      (.returned { contract := contract, locals := transferStoreToBalance evm I }
        (transferPostState evm I) (some (.bool true))) :=
  erc6909TransferBodyReturns evm I hwv hsender hreceiver henough hfit

theorem erc6909TransferBodyReverts_sender_zero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hz : evm.executionEnv.source = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_sender_nonzero_false evm I hz))

theorem erc6909TransferBodyReverts_receiver_zero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsender : evm.executionEnv.source ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_sender_nonzero_true evm I hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_receiver_nonzero_false evm I hz))

theorem erc6909TransferBodyReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsender : evm.executionEnv.source ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromBalanceWord evm I).toNat < (transferAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_sender_nonzero_true evm I hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_receiver_nonzero_true evm I hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_from_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem erc6909TransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsender : evm.executionEnv.source ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferAmountWord I).toNat ≤ (transferFromBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_sender_nonzero_true evm I hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_receiver_nonzero_true evm I hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transfer_newToBalance_revert evm I hover))

/-! ## EVM ABI decode trace for `transfer(address,uint256,uint256)` -/

theorem erc6909TransferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1742⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨223⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨223⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1742⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨499⟩
      [transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 3) (by simpa using hsz100) hszhi hsize
  obtain ⟨_, _, rd1742⟩ := erc6909TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1769⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd1769⟩ := erc6909DecodeAddrOk rd1629 hcanonReceiver (by jump_dest)
    (by evm_ov)
  have rd1770 := evm_run rd1769 with [jumpdest]
  have rd1771 := RD.erc6909Swap6 rd1770 (by decide) (by simp)
  have rd1777 := evm_run rd1771 with [push1 ⟨32⟩, dup6, add, calldataload]
  have rd1778 := RD.erc6909Swap6 rd1777 (by decide) (by simp)
  have rd1781 := evm_run rd1778 with [pop, push1 ⟨64⟩, swap1]
  have rd1782 := RD.erc6909Swap5 rd1781 (by decide) (by simp)
  have rd223 := evm_run rd1782 with [
    add, calldataload, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have rd499 := evm_run rd223 with [jumpdest, push2 ⟨499⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [transferReceiverWord, transferIdWord, transferAmountWord, calldataWord] using rd499⟩

theorem erc6909TransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 3) hsz4 hshort hsize
      (by norm_num)
  obtain ⟨_, _, rd1742⟩ := erc6909TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 3) hbig hsize (by norm_num)
  obtain ⟨_, _, rd1742⟩ := erc6909TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferX_noncanon_receiver {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferReceiverWord I)
      (UInt256.land (transferReceiverWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 3) (by simpa using hsz100) hszhi hsize
  obtain ⟨_, _, rd1742⟩ := erc6909TransferX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1769⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]
  simpa [transferReceiverWord, calldataWord] using erc6909DecodeAddrRevert rd1629 hnc
    (by evm_ov)

end OpenZeppelinBench.ERC6909
