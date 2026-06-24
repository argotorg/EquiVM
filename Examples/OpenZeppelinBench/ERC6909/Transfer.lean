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
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_ok
    hlen0 hlen32 hlen64 hcanon0

theorem decodeScalarWords_address_uint256_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_none_noncanon0
    hlen0 hnc0

theorem decodeScalarWords_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_none_short hshort

theorem decodeCalldata_address_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  change decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_ok
    hsz100 hbig hcanon0

theorem decodeCalldata_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  change decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_noncanon0
    hsz100 hbig hnc0

theorem decodeCalldata_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  change decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_short hsz4 hshort

theorem decodeCalldata_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [addr, uint256, uint256] cd = none := by
  change decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_huge hbig

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

theorem erc6909TransferBodySourceCore (evm : EVM.State) (I : ExecutionEnv)
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

/-! ## EVM body trace for `transfer(address,uint256,uint256)` -/

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `DUP10` xstep.
theorem erc6909Dup10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h i j l : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (l :: a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup10 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t).length - 10 + 11 >
      1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.erc6909Dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (l :: a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Dup10_xstep hc hp hdec hs hov)

noncomputable def transferInnerHashMem (owner : UInt256) : ByteArray :=
  approveTwoWordHashMem owner ⟨0⟩ solcFreePtrMem

noncomputable def transferInnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((transferInnerHashMem owner).readWithPadding 0 64)))

noncomputable def transferOuterHashMem (owner id : UInt256) : ByteArray :=
  approveTwoWordHashMem id (transferInnerSlot owner) (transferInnerHashMem owner)

noncomputable def transferOuterSlot (owner id : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((transferOuterHashMem owner id).readWithPadding 0 64)))

noncomputable def transferEventFromMem (from_ to_ id : UInt256) : ByteArray :=
  (UInt256.toByteArray from_).write 0 (transferOuterHashMem to_ id) 128 32

noncomputable def transferEventMem (from_ to_ id amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0 (transferEventFromMem from_ to_ id) 160 32

noncomputable def transferReturnMem (from_ to_ id amount : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (transferEventMem from_ to_ id amount) 128 32

theorem transferInnerHashMem_size (owner : UInt256) :
    (transferInnerHashMem owner).size = 96 := by
  unfold transferInnerHashMem
  exact approveTwoWordHashMem_size owner ⟨0⟩ solcFreePtrMem_size

theorem transferOuterHashMem_size (owner id : UInt256) :
    (transferOuterHashMem owner id).size = 96 := by
  unfold transferOuterHashMem
  exact approveTwoWordHashMem_size id (transferInnerSlot owner)
    (transferInnerHashMem_size owner)

theorem transferInnerHashMem_read0_64 (owner : UInt256) :
    (transferInnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferInnerHashMem
  exact approveTwoWordHashMem_read0_64 owner ⟨0⟩ solcFreePtrMem_size

theorem transferOuterHashMem_read0_64 (owner id : UInt256) :
    (transferOuterHashMem owner id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (transferInnerSlot owner) := by
  unfold transferOuterHashMem
  exact approveTwoWordHashMem_read0_64 id (transferInnerSlot owner)
    (transferInnerHashMem_size owner)

theorem transferOuterHashMem_read64 (owner id : UInt256) :
    (transferOuterHashMem owner id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferOuterHashMem transferInnerHashMem
  apply approveTwoWordHashMem_read64
  · exact approveTwoWordHashMem_size owner ⟨0⟩ solcFreePtrMem_size
  · exact approveTwoWordHashMem_read64 owner ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem transferOuterHashMem_mload64 (owner id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferOuterHashMem owner id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferOuterHashMem owner id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferOuterHashMem_size]; decide) (by decide)
    (transferOuterHashMem_read64 owner id)

noncomputable def transferMapScratchMem (base : ByteArray) (owner id : UInt256) : ByteArray :=
  approveTwoWordHashMem id (transferInnerSlot owner) (approveTwoWordHashMem owner ⟨0⟩ base)

theorem transferMapScratchMem_size {base : ByteArray} (owner id : UInt256)
    (hbase : base.size = 96) :
    (transferMapScratchMem base owner id).size = 96 := by
  unfold transferMapScratchMem
  exact approveTwoWordHashMem_size id (transferInnerSlot owner)
    (approveTwoWordHashMem_size owner ⟨0⟩ hbase)

theorem transferMapScratchMem_read0_64 {base : ByteArray} (owner id : UInt256)
    (hbase : base.size = 96) :
    (transferMapScratchMem base owner id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (transferInnerSlot owner) := by
  unfold transferMapScratchMem
  exact approveTwoWordHashMem_read0_64 id (transferInnerSlot owner)
    (approveTwoWordHashMem_size owner ⟨0⟩ hbase)

theorem transferMapScratchMem_read64 {base : ByteArray} (owner id : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferMapScratchMem base owner id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferMapScratchMem
  apply approveTwoWordHashMem_read64
  · exact approveTwoWordHashMem_size owner ⟨0⟩ hbase
  · exact approveTwoWordHashMem_read64 owner ⟨0⟩ hbase hread64

theorem transferMapScratchMem_mload64 {base : ByteArray} (owner id : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferMapScratchMem base owner id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferMapScratchMem base owner id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferMapScratchMem_size owner id hbase]; decide)
    (by decide) (transferMapScratchMem_read64 owner id hbase hread64)

theorem transferEventFromMem_size (from_ to_ id : UInt256) :
    (transferEventFromMem from_ to_ id).size = 160 := by
  unfold transferEventFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferOuterHashMem_size]; omega)
      (by rw [transferOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, transferOuterHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferEventMem_size (from_ to_ id amount : UInt256) :
    (transferEventMem from_ to_ id amount).size = 192 := by
  unfold transferEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferEventFromMem_size])
      (by rw [transferEventFromMem_size]; norm_num [USize.size]),
    ByteArray.size_append, ByteArray.size_append, transferEventFromMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferEventFromMem_read64 (from_ to_ id : UInt256) :
    (transferEventFromMem from_ to_ id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferEventFromMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferOuterHashMem_size]; omega)
      (by rw [transferOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, transferOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, transferOuterHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [transferOuterHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [transferOuterHashMem_size]),
    transferOuterHashMem_read64]

theorem transferEventFromMem_mload64 (from_ to_ id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferEventFromMem from_ to_ id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferEventFromMem from_ to_ id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferEventFromMem_size]; decide) (by decide)
    (transferEventFromMem_read64 from_ to_ id)

theorem transferEventMem_read64 (from_ to_ id amount : UInt256) :
    (transferEventMem from_ to_ id amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [transferEventFromMem_size]) (by omega),
    transferEventFromMem_read64]

theorem transferEventMem_mload64 (from_ to_ id amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferEventMem from_ to_ id amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferEventMem from_ to_ id amount).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferEventMem_size]; decide) (by decide)
    (transferEventMem_read64 from_ to_ id amount)

theorem transferReturnMem_size (from_ to_ id amount : UInt256) :
    (transferReturnMem from_ to_ id amount).size = 192 := by
  unfold transferReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferEventMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferEventMem_size, toByteArray_size]
  omega

theorem transferReturnMem_read64 (from_ to_ id amount : UInt256) :
    (transferReturnMem from_ to_ id amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [transferEventMem_size]; omega) (by omega),
    transferEventMem_read64]

theorem transferReturnMem_mload64 (from_ to_ id amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferReturnMem from_ to_ id amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferReturnMem from_ to_ id amount).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferReturnMem_size]; decide) (by decide)
    (transferReturnMem_read64 from_ to_ id amount)

theorem transferReturnMem_read128 (from_ to_ id amount : UInt256) :
    (transferReturnMem from_ to_ id amount).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [transferEventMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

noncomputable def transferEventFromBaseMem (base : ByteArray) (from_ : UInt256) :
    ByteArray :=
  (UInt256.toByteArray from_).write 0 base 128 32

noncomputable def transferEventBaseMem (base : ByteArray) (from_ amount : UInt256) :
    ByteArray :=
  (UInt256.toByteArray amount).write 0 (transferEventFromBaseMem base from_) 160 32

noncomputable def transferReturnBaseMem (base : ByteArray) (from_ amount : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (transferEventBaseMem base from_ amount) 128 32

theorem transferEventFromBaseMem_size {base : ByteArray} (from_ : UInt256)
    (hbase : base.size = 96) :
    (transferEventFromBaseMem base from_).size = 160 := by
  unfold transferEventFromBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferEventBaseMem_size {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96) :
    (transferEventBaseMem base from_ amount).size = 192 := by
  unfold transferEventBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferEventFromBaseMem_size from_ hbase])
      (by rw [transferEventFromBaseMem_size from_ hbase]; norm_num [USize.size]),
    ByteArray.size_append, ByteArray.size_append, transferEventFromBaseMem_size from_ hbase,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferEventFromBaseMem_read64 {base : ByteArray} (from_ : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferEventFromBaseMem base from_).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferEventFromBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem transferEventBaseMem_read64 {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferEventBaseMem base from_ amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferEventBaseMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [transferEventFromBaseMem_size from_ hbase]) (by omega),
    transferEventFromBaseMem_read64 from_ hbase hread64]

theorem transferEventBaseMem_mload64 {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferEventBaseMem base from_ amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferEventBaseMem base from_ amount).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferEventBaseMem_size from_ amount hbase]; decide)
    (by decide) (transferEventBaseMem_read64 from_ amount hbase hread64)

theorem transferReturnBaseMem_size {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96) :
    (transferReturnBaseMem base from_ amount).size = 192 := by
  unfold transferReturnBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferEventBaseMem_size from_ amount hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferEventBaseMem_size from_ amount hbase,
    toByteArray_size]
  omega

theorem transferReturnBaseMem_read64 {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferReturnBaseMem base from_ amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferReturnBaseMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [transferEventBaseMem_size from_ amount hbase]; omega) (by omega),
    transferEventBaseMem_read64 from_ amount hbase hread64]

theorem transferReturnBaseMem_mload64 {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferReturnBaseMem base from_ amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferReturnBaseMem base from_ amount).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferReturnBaseMem_size from_ amount hbase]; decide)
    (by decide) (transferReturnBaseMem_read64 from_ amount hbase hread64)

theorem transferReturnBaseMem_read128 {base : ByteArray} (from_ amount : UInt256)
    (hbase : base.size = 96) :
    (transferReturnBaseMem base from_ amount).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferReturnBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [transferEventBaseMem_size from_ amount hbase]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem transferInnerKeccakSlot (owner : UInt256)
    (hcanon : owner.toNat < EVM.addressModulus) :
    transferInnerSlot owner =
      mapSlot (keyValueToWord (.address (AccountAddress.ofNat owner.toNat))) ⟨0⟩ := by
  unfold transferInnerSlot mapSlot
  rw [transferInnerHashMem_read0_64]
  rw [balanceOfKeyValueToWord_address_of_canonical owner hcanon]
  exact mappingSlot_single owner ⟨0⟩

theorem transferOuterKeccakSlot (owner id : UInt256)
    (hcanon : owner.toNat < EVM.addressModulus) :
    transferOuterSlot owner id =
      balanceSlot (.address (AccountAddress.ofNat owner.toNat))
        (.int (Int.ofNat id.toNat)) := by
  unfold transferOuterSlot balanceSlot mapSlot
  rw [transferOuterHashMem_read0_64, transferInnerKeccakSlot owner hcanon]
  rw [balanceOfKeyValueToWord_address_of_canonical owner hcanon,
    balanceOfKeyValueToWord_uint256 id]
  exact mappingSlot_single id
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray owner ++
      UInt256.toByteArray (⟨0⟩ : UInt256))))

theorem transferFromKeccakSlot (I : ExecutionEnv) :
    transferOuterSlot (transferSenderWord I) (transferIdWord I) = transferFromSlotI I := by
  rw [transferOuterKeccakSlot _ _ (transferSenderWord_canonical I), transferSender_ofNat]
  rfl

theorem transferToKeccakSlot (I : ExecutionEnv)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus) :
    transferOuterSlot (transferReceiverWord I) (transferIdWord I) = transferToSlot I := by
  rw [transferOuterKeccakSlot _ _ hcanonReceiver]
  rfl

def transferTransferTopic : UInt256 :=
  ⟨0x1b3d7edb2e9c0b0e7c525b20aaaef0f5940d2ed71663c7d39266ecafac728859⟩

def transferInvalidSenderSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x01486a41⟩ ⟨231⟩

def transferInvalidReceiverSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x0b8bbd61⟩ ⟨228⟩

def transferPanicSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x4e487b71⟩ ⟨224⟩

def transferInsufficientBalanceSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x02c6d3fb⟩ ⟨230⟩

noncomputable def transferInsufficientBalanceSelectorMem (owner id : UInt256) : ByteArray :=
  (UInt256.toByteArray transferInsufficientBalanceSelectorWord).write 0
    (transferOuterHashMem owner id) 128 32

noncomputable def transferInsufficientBalanceSenderMem (owner id : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0
    (transferInsufficientBalanceSelectorMem owner id) 132 32

noncomputable def transferInsufficientBalanceBalanceMem
    (owner id balance : UInt256) : ByteArray :=
  (UInt256.toByteArray balance).write 0
    (transferInsufficientBalanceSenderMem owner id) 164 32

noncomputable def transferInsufficientBalanceAmountMem
    (owner id balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (transferInsufficientBalanceBalanceMem owner id balance) 196 32

noncomputable def transferInsufficientBalanceIdMem
    (owner id balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0
    (transferInsufficientBalanceAmountMem owner id balance amount) 228 32

theorem transferInsufficientBalanceSelectorMem_size (owner id : UInt256) :
    (transferInsufficientBalanceSelectorMem owner id).size = 160 := by
  unfold transferInsufficientBalanceSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferOuterHashMem_size]; omega)
      (by rw [transferOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, transferOuterHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferInsufficientBalanceSenderMem_size (owner id : UInt256) :
    (transferInsufficientBalanceSenderMem owner id).size = 164 := by
  unfold transferInsufficientBalanceSenderMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientBalanceSelectorMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceBalanceMem_size
    (owner id balance : UInt256) :
    (transferInsufficientBalanceBalanceMem owner id balance).size = 196 := by
  unfold transferInsufficientBalanceBalanceMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientBalanceSenderMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceAmountMem_size
    (owner id balance amount : UInt256) :
    (transferInsufficientBalanceAmountMem owner id balance amount).size = 228 := by
  unfold transferInsufficientBalanceAmountMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientBalanceBalanceMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceIdMem_size
    (owner id balance amount : UInt256) :
    (transferInsufficientBalanceIdMem owner id balance amount).size = 260 := by
  unfold transferInsufficientBalanceIdMem
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientBalanceAmountMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceSelectorMem_read64 (owner id : UInt256) :
    (transferInsufficientBalanceSelectorMem owner id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferOuterHashMem_size]; omega)
      (by rw [transferOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, transferOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, transferOuterHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [transferOuterHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [transferOuterHashMem_size])]
  exact transferOuterHashMem_read64 owner id

theorem transferInsufficientBalanceSenderMem_read64 (owner id : UInt256) :
    (transferInsufficientBalanceSenderMem owner id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSenderMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorMem_size]; omega) (by omega),
    transferInsufficientBalanceSelectorMem_read64]

theorem transferInsufficientBalanceBalanceMem_read64
    (owner id balance : UInt256) :
    (transferInsufficientBalanceBalanceMem owner id balance).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceBalanceMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderMem_size]) (by omega),
    transferInsufficientBalanceSenderMem_read64]

theorem transferInsufficientBalanceAmountMem_read64
    (owner id balance amount : UInt256) :
    (transferInsufficientBalanceAmountMem owner id balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceAmountMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceMem_size]) (by omega),
    transferInsufficientBalanceBalanceMem_read64]

theorem transferInsufficientBalanceIdMem_read64
    (owner id balance amount : UInt256) :
    (transferInsufficientBalanceIdMem owner id balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceIdMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountMem_size]) (by omega),
    transferInsufficientBalanceAmountMem_read64]

theorem transferInsufficientBalanceIdMem_mload64
    (owner id balance amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferInsufficientBalanceIdMem owner id balance amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferInsufficientBalanceIdMem owner id balance amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferInsufficientBalanceIdMem_size]; decide)
    (by decide) (transferInsufficientBalanceIdMem_read64 owner id balance amount)

noncomputable def transferPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferPanicSelectorWord).write 0 mem 0 32

noncomputable def transferPanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (transferPanicMem0 mem) 4 32

theorem transferU256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, Nat.add_comm]

theorem RD.erc6909PanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨2029⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev erc6909BenchBytecode g s0 := by
  have rd2038 := evm_run h with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0,
    raw mstore 0 (transferPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩ ]
  have rd2046 := evm_run rd2038 with [
    raw mstore 0 (transferPanicMem mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0 ]
  exact rd2046.rev 0 (by decide) mem_cost (by evm_ov)

theorem erc6909RoutineCheckedAdd {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨2017⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J erc6909BenchBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD erc6909BenchBytecode ee g s0 ret ((a + b) :: R) mem aw rdata acc k' C' := by
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt a (a + b) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [haddNat]; omega)
  have rd2023 := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3 ]
  have rd2024₀ := evm_run rd2023 with [ gt ]
  have rd2024 := rd2024₀
  rw [transferU256_add_comm b a] at rd2024
  rw [hgt] at rd2024
  have rd2025₀ := evm_run rd2024 with [ iszero ]
  have rd2025 := rd2025₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2025
  have rd441 := evm_run rd2025 with [
    push2 ⟨441⟩, jumpiT one_ne_zero_uint (by jump_dest) ]
  exact ⟨_, _, evm_run rd441 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

theorem erc6909RoutineCheckedAdd_overflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨2017⟩ (a :: b :: ret :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev erc6909BenchBytecode g s0 := by
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hgt : UInt256.gt a (a + b) = ⟨1⟩ := by
    show UInt256.fromBool (decide (a > a + b)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show a.toNat > (a + b).toNat
      rw [haddNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd2023 := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3 ]
  have rd2024₀ := evm_run rd2023 with [ gt ]
  have rd2024 := rd2024₀
  rw [transferU256_add_comm b a] at rd2024
  rw [hgt] at rd2024
  have rd2025₀ := evm_run rd2024 with [ iszero ]
  have rd2025 := rd2025₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2025
  have rd2029 := evm_run rd2025 with [
    push2 ⟨441⟩, jumpiNT (by decide) ]
  exact RD.erc6909PanicOverflowRevert rd2029 (by evm_ov)

theorem erc6909TransferX_toUpdate {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferAmountWord I, transferIdWord I, transferReceiverWord I, transferSenderWord I,
        ⟨512⟩, ⟨0⟩, transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩,
        sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd499⟩ := erc6909TransferX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hreach
  exact ⟨_, _, by
    simpa [transferSenderWord] using evm_run rd499 with [
      jumpdest, push0, push2 ⟨512⟩, caller, dup6, dup6, dup6, push2 ⟨661⟩,
      jump (by jump_dest) ]⟩

theorem erc6909TransferX_toUpdateHelper {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferAmountWord I, transferIdWord I, transferReceiverWord I, transferSenderWord I,
        ⟨760⟩, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨512⟩, ⟨0⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferX_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hreach
  have hsenderWordNZ : transferSenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((transferSender_ofNat I).symm.trans (by
      rw [hzero]
      rfl))
  have hreceiverWordNZ : transferReceiverWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hreceiver (by
      rw [hzero]
      rfl)
  exact ⟨_, _, evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (transferSenderWord_canonical I)]
      exact hsenderWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact hreceiverWordNZ)
      (by jump_dest),
    jumpdest, push2 ⟨760⟩, dup5, dup5, dup5, dup5, push2 ⟨1323⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferX_revert_sender_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferX_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hreach
  have hsenderZero : transferSenderWord I = ⟨0⟩ := by
    unfold transferSenderWord
    rw [hsource]
    decide
  have rd676 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hsenderZero]
      decide) ]
  exact evm_run rd676 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferInvalidSenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferX_revert_receiver_zero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferX_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hreach
  have hsenderWordNZ : transferSenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((transferSender_ofNat I).symm.trans (by
      rw [hzero]
      rfl))
  have hreceiverZeroWord : transferReceiverWord I = ⟨0⟩ := by
    apply u256_inj
    have hval : (transferReceiverWord I).toNat % AccountAddress.size = 0 := by
      simpa [AccountAddress.ofNat, zeroAccountAddress] using congrArg Fin.val hreceiver
    have hcanonReceiver' : (transferReceiverWord I).toNat < AccountAddress.size := by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanonReceiver
    rw [Nat.mod_eq_of_lt hcanonReceiver'] at hval
    exact hval
  have rd722 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (transferSenderWord_canonical I)]
      exact hsenderWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hreceiverZeroWord]
      decide) ]
  exact evm_run rd722 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferInvalidReceiverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferX_afterRequire {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1323⟩ := erc6909TransferX_toUpdateHelper (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hsource hreceiver hreach
  have hsenderWordNZ : transferSenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((transferSender_ofNat I).symm.trans (by
      rw [hzero]
      rfl))
  have hslot := transferFromKeccakSlot I
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (transferSenderWord_canonical I)]
      exact isZero_eq_zero_of_ne hsenderWordNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferSenderWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferSenderWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (transferInnerHashMem (transferSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferIdWord I)
        (transferInnerHashMem (transferSenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  have rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1 C1 := by
    simpa [transferFromBalanceWord, transferFromSlot, transferFromSlotI,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀
  have hlt : UInt256.lt (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferX_insufficientTail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (hlt : (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferOuterHashMem_mload64 (transferSenderWord I) (transferIdWord I))
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorMem (transferSenderWord I)
        (transferIdWord I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderMem (transferSenderWord I)
        (transferIdWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferSenderWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceMem (transferSenderWord I)
        (transferIdWord I) (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountMem (transferSenderWord I)
        (transferIdWord I) (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdMem (transferSenderWord I)
        (transferIdWord I) (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdMem_mload64 (transferSenderWord I) (transferIdWord I)
        (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I) (transferAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferX_afterLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1323⟩ := erc6909TransferX_toUpdateHelper (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hsource hreceiver hreach
  have hsenderWordNZ : transferSenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((transferSender_ofNat I).symm.trans (by
      rw [hzero]
      rfl))
  have hslot := transferFromKeccakSlot I
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (transferSenderWord_canonical I)]
      exact isZero_eq_zero_of_ne hsenderWordNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferSenderWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferSenderWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (transferInnerHashMem (transferSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferIdWord I)
        (transferInnerHashMem (transferSenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromBalanceWord, transferFromSlot, transferFromSlotI,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferX_insufficient {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (hlt : (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferX_afterLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hsource hreceiver hreach
  exact erc6909TransferX_insufficientTail hlt rd1373

theorem erc6909TransferX_afterDebit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferMapScratchMem (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
        (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferX_afterRequire (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonReceiver hsource hreceiver henough hreach
  have hslot := transferFromKeccakSlot I
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferSenderWord I)
        (transferOuterHashMem (transferSenderWord I) (transferIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferSenderWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferSenderWord I) ⟨0⟩
        (transferOuterHashMem (transferSenderWord I) (transferIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferSenderWord I) ⟨0⟩
                    (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferSenderWord I) ⟨0⟩
          (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I)),
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferIdWord I)
        (approveTwoWordHashMem (transferSenderWord I) ⟨0⟩
          (transferOuterHashMem (transferSenderWord I) (transferIdWord I))))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem
        (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
        (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferSenderWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem
                    (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
                    (transferSenderWord I) (transferIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferSenderWord I) (transferIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferSenderWord I) (transferIdWord I)
          (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I)),
          transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferAmountWord I) =
        transferDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferAmountWord I).toNat)
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, rd1476⟩

theorem erc6909TransferX_toCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I, transferAmountWord I,
        ⟨1539⟩, ⟨0⟩, transferToSlot I, transferAmountWord I, transferSenderWord I,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, transferSenderWord I,
        ⟨760⟩, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨512⟩, ⟨0⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
          (transferSenderWord I) (transferIdWord I))
        (transferReceiverWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferX_afterDebit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonReceiver hsource hreceiver henough hreach
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (transferSenderWord I) (transferIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferSenderWord I) (transferIdWord I)
      (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferSenderWord I) (transferIdWord I)
      (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I))
      (transferOuterHashMem_read64 (transferSenderWord I) (transferIdWord I))
  have hreceiverWordNZ : transferReceiverWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hreceiver (by
      rw [hzero]
      rfl)
  have hslot := transferToKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverWordNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferReceiverWord I) ⟨0⟩ hdebitMemSize,
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferIdWord I)
        (approveTwoWordHashMem (transferReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferReceiverWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferReceiverWord I) (transferIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferReceiverWord I) (transferIdWord I)
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferReceiverWord I) (transferIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferReceiverWord I) (transferIdWord I)
          hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I, transferToSlot I, ⟨0⟩,
        transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩, transferAmountWord I,
        transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferReceiverWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferToBalanceWord, transferAfterDebitState, transferFromSlot, transferFromSlotI,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, evm_run rd1526 with [
    dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferX_afterCredit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferSenderWord I, transferAmountWord I, transferIdWord I, transferReceiverWord I,
        transferSenderWord I, ⟨760⟩, transferAmountWord I, transferIdWord I,
        transferReceiverWord I, transferSenderWord I, ⟨512⟩, ⟨0⟩,
        transferAmountWord I, transferIdWord I, transferReceiverWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
          (transferSenderWord I) (transferIdWord I))
        (transferReceiverWord I) (transferIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferX_toCheckedAdd (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonReceiver hsource hreceiver henough hreach
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferNewToNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I + transferAmountWord I =
        transferNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [transferNewToNat] using hfit)]
    unfold transferNewToWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤ transferNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferX_toCheckedAdd (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonReceiver hsource hreceiver henough hreach
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferNewToNat] using hover) (by evm_ov)

theorem erc6909X_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hreceiver : AccountAddress.ofNat (transferReceiverWord I).toNat ≠ AccountAddress.ofNat 0)
    (henough : (transferAmountWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨209⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferX_afterCredit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonReceiver hsource hreceiver henough hfit hreach
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferSenderWord I) (transferIdWord I))
      (transferSenderWord I) (transferIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferReceiverWord I) (transferIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferSenderWord I) (transferIdWord I)
      (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferSenderWord I) (transferIdWord I)
      (transferOuterHashMem_size (transferSenderWord I) (transferIdWord I))
      (transferOuterHashMem_read64 (transferSenderWord I) (transferIdWord I))
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferReceiverWord I) (transferIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferReceiverWord I) (transferIdWord I)
      hdebitMemSize hdebitMemRead64
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (transferMapScratchMem_mload64 (transferReceiverWord I) (transferIdWord I)
        hdebitMemSize hdebitMemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferSenderWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferSenderWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferSenderWord I)
        rw [solcAddrMask_clean_left (transferSenderWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferSenderWord I) (transferAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean (transferSenderWord_canonical I),
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferSenderWord I) (transferAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd512 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd193 := evm_run rd512 with [
    jumpdest, pop, push1 ⟨1⟩, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferSenderWord I) (transferAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferSenderWord I) (transferAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferSenderWord I) (transferAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferSenderWord I) (transferAmountWord I)
          hcreditMemSize)
      (by evm_ov) ]

theorem erc6909TransferBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 2))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨209⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc6909TransferSelector_size hsel
  have hd := erc6909Dispatch_transfer (cd := I.calldata) hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g)
      hAccounts
  have hFromBalance : transferFromBalanceWord evmE I = transferFromBalanceWord evmS I := by
    unfold transferFromBalanceWord transferFromSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner
      (balanceSlot (.address evmS.executionEnv.source)
        (.int (Int.ofNat (transferIdWord I).toNat)))
  have hDebit : transferDebitWord evmE I = transferDebitWord evmS I := by
    simp [transferDebitWord, hFromBalance]
  have hσDebit : EVMStateEquiv (transferAfterDebitState evmE I)
      (transferAfterDebitState evmS I) := by
    unfold transferAfterDebitState transferFromSlot
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner
      (balanceSlot (.address evmS.executionEnv.source)
        (.int (Int.ofNat (transferIdWord I).toNat))) rfl
  have hToBalance : transferToBalanceWord evmE I = transferToBalanceWord evmS I := by
    unfold transferToBalanceWord
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I)
  have hNewToNat : transferNewToNat evmE I = transferNewToNat evmS I := by
    simp [transferNewToNat, hToBalance]
  have hNewToWord : transferNewToWord evmE I = transferNewToWord evmS I := by
    simp [transferNewToWord, hNewToNat]
  have hσPost : EVMStateEquiv (transferPostState evmE I) (transferPostState evmS I) := by
    unfold transferPostState
    exact hσDebit.storageStore
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I) hNewToWord
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonReceiver : (transferReceiverWord I).toNat < EVM.addressModulus
      · have hdec := erc6909Decode_transfer_ok (I := I) hsz100 hbig hcanonReceiver
        by_cases hsource : I.source = AccountAddress.ofNat 0
        · have hbody := erc6909TransferBodyReverts_sender_zero evmS I
            (by simp only [evmS, initState]; exact hwv)
            (by simpa [evmS, initState, zeroAccountAddress] using hsource)
          exact (erc6909TransferX_revert_sender_zero (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonReceiver hsource hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · by_cases hreceiver :
            AccountAddress.ofNat (transferReceiverWord I).toNat = AccountAddress.ofNat 0
          · have hbody := erc6909TransferBodyReverts_receiver_zero evmS I
              (by simp only [evmS, initState]; exact hwv)
              (by simpa [evmS, initState, zeroAccountAddress] using hsource)
              (by simpa [zeroAccountAddress] using hreceiver)
            exact (erc6909TransferX_revert_receiver_zero (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonReceiver hsource hreceiver hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
          · by_cases henough : (transferAmountWord I).toNat ≤
              (transferFromBalanceWord
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat
            · by_cases hfit :
                transferNewToNat
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
                  UInt256.size
              · have henoughS :
                    (transferAmountWord I).toNat ≤ (transferFromBalanceWord evmS I).toNat := by
                  simpa [evmE, hFromBalance] using henough
                have hfitS : transferNewToNat evmS I < UInt256.size := by
                  simpa [evmE, hNewToNat] using hfit
                have hbody := erc6909TransferBodyReturns evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  (by simpa [evmS, initState, zeroAccountAddress] using hsource)
                  (by simpa [zeroAccountAddress] using hreceiver) henoughS hfitS
                exact (erc6909X_transfer (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonReceiver hsource hreceiver henough hfit
                    hreach)
                  |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                    (by simp [evmE, initState, transferPostState, transferAfterDebitState,
                      transferFromSlot, transferFromSlotI, storageStore_createdAccounts])
                    (accountMapEquiv.of_eq (by
                      simp [evmE, initState, transferPostState, transferAfterDebitState,
                        transferFromSlot, transferFromSlotI, storageStore_accountMap]))
                    hσPost
                    (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
              · have hover :
                    UInt256.size ≤
                      transferNewToNat
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I := by
                  omega
                have henoughS :
                    (transferAmountWord I).toNat ≤ (transferFromBalanceWord evmS I).toNat := by
                  simpa [evmE, hFromBalance] using henough
                have hoverS : UInt256.size ≤ transferNewToNat evmS I := by
                  simpa [evmE, hNewToNat] using hover
                have hbody := erc6909TransferBodyReverts_overflow evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  (by simpa [evmS, initState, zeroAccountAddress] using hsource)
                  (by simpa [zeroAccountAddress] using hreceiver) henoughS hoverS
                exact (erc6909TransferX_overflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonReceiver hsource hreceiver henough hover
                    hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hlt :
                  (transferFromBalanceWord
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
                    (transferAmountWord I).toNat := by
                omega
              have hltS :
                  (transferFromBalanceWord evmS I).toNat < (transferAmountWord I).toNat := by
                simpa [evmE, hFromBalance] using hlt
              have hbody := erc6909TransferBodyReverts_insufficient evmS I
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [evmS, initState, zeroAccountAddress] using hsource)
                (by simpa [zeroAccountAddress] using hreceiver) hltS
              exact (erc6909TransferX_insufficient (g := Sat256.ofUInt256 g)
                  hsz100 hsize hbig hcanonReceiver hsource hreceiver hlt hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := erc6909Decode_transfer_none_noncanon_receiver (I := I)
          hsz100 hbig hcanonReceiver
        have hnc : UInt256.eq (transferReceiverWord I)
            (UInt256.land (transferReceiverWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonReceiver (solcAddrCanonical_of_clean he))
        exact (erc6909TransferX_noncanon_receiver (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_transfer_none_huge (I := I) hbigge
      exact (erc6909TransferX_hugearg (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc6909Decode_transfer_none_short (I := I) hsz4 hshort
    exact (erc6909TransferX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
