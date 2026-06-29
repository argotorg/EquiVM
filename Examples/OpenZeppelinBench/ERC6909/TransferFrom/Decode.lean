import Examples.OpenZeppelinBench.ERC6909.Approve
import Examples.OpenZeppelinBench.ERC6909.BalanceOf
import Examples.OpenZeppelinBench.ERC6909.IsOperator
import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.ERC6909.Transfer
import Examples.OpenZeppelinBench.Pausable.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.SolcDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909


/-! ## `transferFrom(address,address,uint256,uint256)` body slice

This file keeps the source-side state threading explicit.  In particular, the sender balance is read
after the optional allowance update, matching the spec's assignment order and avoiding any storage
non-collision assumption between the allowance and balance slots.
-/

/-- The raw ABI word for `transferFrom`'s `sender` argument. -/
abbrev transferFromSenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `receiver` argument. -/
abbrev transferFromReceiverWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `id` argument. -/
abbrev transferFromIdWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `amount` argument. -/
abbrev transferFromAmountWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨96⟩ : UInt256).toNat 32)

abbrev transferFromSenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromSenderWord I).toNat)

abbrev transferFromReceiverValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromReceiverWord I).toNat)

abbrev transferFromIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromIdWord I).toNat)

abbrev transferFromAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromAmountWord I).toNat)

def transferFromStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "sender" (transferFromSenderValue I)).insert "receiver"
    (transferFromReceiverValue I)).insert "id" (transferFromIdValue I)).insert "amount"
    (transferFromAmountValue I)

/-! ### ABI decoding -/

theorem decodeScalarWords_address_address_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat <
      EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat)] :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_uint256_ok
        (bytes := bytes) hlen0 hlen32 hlen64 hlen96 hcanon0 hcanon32

theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_uint256_none_noncanon0
        (bytes := bytes) hlen0 hnc0

theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_uint256_none_noncanon1
        (bytes := bytes) hlen0 hlen32 hcanon0 hnc32

theorem decodeScalarWords_address_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 128) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_uint256_none_short
        (bytes := bytes) hshort

theorem decodeCalldata_address_address_uint256_uint256_ok {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd =
      some (((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
        (.int (Int.ofNat (calldataWord cd 100).toNat))) :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_uint256_ok
        (cd := cd) (x := x) (y := y) (z := z) (w := w) hsz132 hbig hcanon0 hcanon1

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_uint256_none_noncanon0
        (cd := cd) (x := x) (y := y) (z := z) (w := w) hsz132 hbig hnc0

theorem decodeCalldata_address_address_uint256_uint256_none_noncanon1 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_uint256_none_noncanon1
        (cd := cd) (x := x) (y := y) (z := z) (w := w) hsz132 hbig hcanon0 hnc1

theorem decodeCalldata_address_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_uint256_none_short
        (cd := cd) (x := x) (y := y) (z := z) (w := w) hsz4 hshort

theorem decodeCalldata_address_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z w : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_uint256_none_huge
        (cd := cd) (x := x) (y := y) (z := z) (w := w) hbig

theorem erc6909Decode_transferFrom_ok {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferFromStore, transferFromSenderValue,
    transferFromReceiverValue, transferFromIdValue, transferFromAmountValue,
    transferFromSenderWord, transferFromReceiverWord, transferFromIdWord,
    transferFromAmountWord, calldataWord]
    using decodeCalldata_address_address_uint256_uint256_ok
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hcanonSender hcanonReceiver

theorem erc6909Decode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_uint256_none_short
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz4 hshort

theorem erc6909Decode_transferFrom_none_noncanon_sender {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferFromSenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromSenderWord]
    using decodeCalldata_address_address_uint256_uint256_none_noncanon0
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hnc

theorem erc6909Decode_transferFrom_none_noncanon_receiver {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromSenderWord,
    transferFromReceiverWord]
    using decodeCalldata_address_address_uint256_uint256_none_noncanon1
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hcanonSender hnc

theorem erc6909Decode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_uint256_none_huge
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hbig

def transferFromOperatorSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address evm.executionEnv.source)

def transferFromAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address evm.executionEnv.source) (.int (Int.ofNat (transferFromIdWord I).toNat))

def transferFromInvalidSenderSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x01486a41⟩ ⟨231⟩

def transferFromInvalidReceiverSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x0b8bbd61⟩ ⟨228⟩

def transferFromSenderBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

def transferFromReceiverBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromReceiverWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

theorem transferFromSenderBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I) =
      transferFromSenderBalanceSlot I := by
  rw [transferOuterKeccakSlot _ _ hcanonSender]
  rfl

theorem transferFromReceiverBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I) =
      transferFromReceiverBalanceSlot I := by
  rw [transferOuterKeccakSlot _ _ hcanonReceiver]
  rfl

abbrev transferFromCallerWord (I : ExecutionEnv) : UInt256 :=
  approveOwnerWord I

theorem transferFromCallerWord_toNat (I : ExecutionEnv) :
    (transferFromCallerWord I).toNat = I.source.val :=
  approveOwnerWord_toNat I

theorem transferFromCallerWord_canonical (I : ExecutionEnv) :
    (transferFromCallerWord I).toNat < EVM.addressModulus :=
  approveOwnerWord_canonical I

theorem transferFromCaller_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (transferFromCallerWord I).toNat = I.source :=
  approveOwner_ofNat I

def transferFromOperatorSlotI (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address I.source)

def transferFromAllowanceSlotI (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address I.source) (.int (Int.ofNat (transferFromIdWord I).toNat))

theorem transferFromOperatorKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        ((ffi.KEC ((isOperatorOuterHashMem (transferFromSenderWord I)
          (transferFromCallerWord I)).readWithPadding 0 64)))) =
      transferFromOperatorSlotI I := by
  have hcallerKey : keyValueToWord (.address I.source) = transferFromCallerWord I := by
    rw [← transferFromCaller_ofNat I]
    exact keyValueToWord_address_of_canonical _
      (transferFromCallerWord_canonical I)
  have hinner :
      isOperatorInnerSlot (transferFromSenderWord I) =
        mapSlot (transferFromSenderWord I) ⟨1⟩ := by
    unfold isOperatorInnerSlot mapSlot
    rw [isOperatorInnerHashMem_read0_64]
    exact mappingSlot_single (transferFromSenderWord I) ⟨1⟩
  unfold transferFromOperatorSlotI operatorApprovalSlot mapSlot
  rw [isOperatorOuterHashMem_read0_64, hinner,
    keyValueToWord_address_of_canonical _ hcanonSender, hcallerKey]
  exact mappingSlot_single (transferFromCallerWord I)
    (mapSlot (transferFromSenderWord I) ⟨1⟩)

theorem transferFromAllowanceKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        ((ffi.KEC ((approveIdHashMem (transferFromSenderWord I)
          (transferFromCallerWord I) (transferFromIdWord I)).readWithPadding 0 64)))) =
      transferFromAllowanceSlotI I := by
  have hcallerKey : keyValueToWord (.address I.source) = transferFromCallerWord I := by
    rw [← transferFromCaller_ofNat I]
    exact keyValueToWord_address_of_canonical _
      (transferFromCallerWord_canonical I)
  have hownerSlot :
      approveOwnerSlot (transferFromSenderWord I) =
        mapSlot (transferFromSenderWord I) ⟨2⟩ := by
    unfold approveOwnerSlot mapSlot
    rw [approveOwnerHashMem_read0_64]
    exact mappingSlot_single (transferFromSenderWord I) ⟨2⟩
  have hspenderSlot :
      approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I) =
        mapSlot (transferFromCallerWord I) (mapSlot (transferFromSenderWord I) ⟨2⟩) := by
    unfold approveSpenderSlot mapSlot
    rw [approveSpenderHashMem_read0_64, hownerSlot]
    exact mappingSlot_single (transferFromCallerWord I)
      (mapSlot (transferFromSenderWord I) ⟨2⟩)
  unfold transferFromAllowanceSlotI allowanceSlot mapSlot
  rw [approveIdHashMem_read0_64, hspenderSlot,
    keyValueToWord_address_of_canonical _ hcanonSender, hcallerKey]
  rw [keyValueToWord_uint256 (transferFromIdWord I)]
  exact mappingSlot_single (transferFromIdWord I)
    (mapSlot (transferFromCallerWord I) (mapSlot (transferFromSenderWord I) ⟨2⟩))

theorem uint256_lnot_zero_max :
    UInt256.lnot (⟨0⟩ : UInt256) = UInt256.ofNat (UInt256.size - 1) := by
  decide

theorem transferFromOperatorSlot_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I =
      transferFromOperatorSlotI I := by
  simp [transferFromOperatorSlot, transferFromOperatorSlotI, initState]

theorem transferFromAllowanceSlot_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      transferFromAllowanceSlotI I := by
  simp [transferFromAllowanceSlot, transferFromAllowanceSlotI, initState]

def transferFromOperatorWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromOperatorSlot evm I))
    ⟨255⟩

abbrev transferFromOperatorValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  wordToElem .bool (transferFromOperatorWord evm I)

def transferFromCurrentAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

abbrev transferFromCurrentAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat)

@[irreducible] def transferFromStoreCurrentAllowance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStore I).insert "currentAllowance" (transferFromCurrentAllowanceValue evm I)

def transferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat)

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

def transferFromSenderBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromSenderBalanceSlot I)

abbrev transferFromSenderBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromSenderBalanceWord evm I).toNat)

def transferFromStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreCurrentAllowance evm I).insert "fromBalance"
    (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I)

def transferFromSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
      (transferFromAmountWord I).toNat)

def transferFromAfterSenderBalanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterAllowanceState evm I) evm.executionEnv.codeOwner
    (transferFromSenderBalanceSlot I) (transferFromSenderDebitWord evm I)

theorem transferFromAfterSenderBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterSenderBalanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterSenderBalanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases (transferFromAfterAllowanceState evm I).accountMap.find? evm.executionEnv.codeOwner with
  | none => exact transferFromAfterAllowance_codeOwner evm I
  | some acc =>
      simp only [Option.option, State.setAccount, Account.updateStorage,
        transferFromAfterAllowance_codeOwner]

def transferFromReceiverBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromAfterSenderBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromReceiverBalanceSlot I)

abbrev transferFromReceiverBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromReceiverBalanceWord evm I).toNat)

def transferFromStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreFromBalance evm I).insert "toBalance" (transferFromReceiverBalanceValue evm I)

def transferFromReceiverCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat

def transferFromReceiverCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromReceiverCreditNat evm I)

abbrev transferFromReceiverCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromReceiverCreditNat evm I))

def transferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterSenderBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromReceiverBalanceSlot I) (transferFromReceiverCreditWord evm I)

def transferFromTailStoreFromBalance (locals : Store) (evm : EVM.State)
    (I : ExecutionEnv) : Store :=
  locals.insert "fromBalance" (transferFromSenderBalanceValue evm I)

def transferFromTailSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat)

def transferFromTailAfterSenderBalanceState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (transferFromSenderBalanceSlot I) (transferFromTailSenderDebitWord evm I)

theorem transferFromTailAfterSenderBalance_codeOwner (evm : EVM.State)
    (I : ExecutionEnv) :
    (transferFromTailAfterSenderBalanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromTailAfterSenderBalanceState, Solm.EVM.storageStore,
    State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferFromTailReceiverBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromTailAfterSenderBalanceState evm I)
    evm.executionEnv.codeOwner (transferFromReceiverBalanceSlot I)

abbrev transferFromTailReceiverBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromTailReceiverBalanceWord evm I).toNat)

def transferFromTailStoreToBalance (locals : Store) (evm : EVM.State)
    (I : ExecutionEnv) : Store :=
  (transferFromTailStoreFromBalance locals evm I).insert "toBalance"
    (transferFromTailReceiverBalanceValue evm I)

def transferFromTailReceiverCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromTailReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat

def transferFromTailReceiverCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromTailReceiverCreditNat evm I)

abbrev transferFromTailReceiverCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromTailReceiverCreditNat evm I))

def transferFromTailPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromTailAfterSenderBalanceState evm I)
    evm.executionEnv.codeOwner (transferFromReceiverBalanceSlot I)
    (transferFromTailReceiverCreditWord evm I)

theorem transferFromReceiverCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    (transferFromReceiverCreditWord evm I).toNat = transferFromReceiverCreditNat evm I := by
  unfold transferFromReceiverCreditWord
  exact ulit_toNat' _ hfit

theorem transferFromTailReceiverCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    (transferFromTailReceiverCreditWord evm I).toNat =
      transferFromTailReceiverCreditNat evm I := by
  unfold transferFromTailReceiverCreditWord
  exact ulit_toNat' _ hfit

theorem transferFromStore_sender (I : ExecutionEnv) :
    (transferFromStore I).get? "sender" = some (transferFromSenderValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_receiver (I : ExecutionEnv) :
    (transferFromStore I).get? "receiver" = some (transferFromReceiverValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem transferFromStore_id (I : ExecutionEnv) :
    (transferFromStore I).get? "id" = some (transferFromIdValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_amount (I : ExecutionEnv) :
    (transferFromStore I).get? "amount" = some (transferFromAmountValue I) := by
  rw [transferFromStore, store_get_self]

theorem transferFromStoreCurrentAllowance_currentAllowance (evm : EVM.State)
    (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "currentAllowance" =
      some (transferFromCurrentAllowanceValue evm I) := by
  rw [transferFromStoreCurrentAllowance, store_get_self]

theorem transferFromStoreCurrentAllowance_sender (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "sender" =
      some (transferFromSenderValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_sender]

theorem transferFromStoreCurrentAllowance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_receiver]

theorem transferFromStoreCurrentAllowance_id (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "id" =
      some (transferFromIdValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem transferFromStoreCurrentAllowance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_amount]

theorem transferFromStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [transferFromStoreFromBalance, store_get_self]

theorem transferFromStoreFromBalance_sender (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "sender" =
      some (transferFromSenderValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_sender]

theorem transferFromStoreFromBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_receiver]

theorem transferFromStoreFromBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_amount]

theorem transferFromStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "toBalance" =
      some (transferFromReceiverBalanceValue evm I) := by
  rw [transferFromStoreToBalance, store_get_self]

theorem transferFromStoreToBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_amount]

theorem transferFromStoreToBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_receiver]

theorem erc6909TransferFromSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 7)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 7).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_transferFrom {cd : ByteArray}
    (hsel : (erc6909SelBytes 7 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = erc6909SelBytes 7 := (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition, supportsInterfaceTransition, transferTransition])
    (post := [])
    rfl rfl ?_ (by
      rw [selectorOf, erc6909TransferFromSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SetOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SupportsInterfaceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909TransferSelectorBytes, hcd]; decide



end OpenZeppelinBench.ERC6909
