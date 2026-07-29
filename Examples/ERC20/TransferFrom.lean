import Examples.ERC20.Transfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace ERC20

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
    (transferFromFromSlot I)
    (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I)

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
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_ok
        (bytes := bytes) hlen0 hlen32 hlen64 hcanon0 hcanon32

theorem decodeScalarWords_address_address_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_none_noncanon0
        (bytes := bytes) hlen0 hnc0

theorem decodeScalarWords_address_address_uint256_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_none_noncanon1
        (bytes := bytes) hlen0 hlen32 hcanon0 hnc32

theorem decodeScalarWords_address_address_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [addr, addr, uint256] bytes 0 = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeScalarWords_address_address_uint256_none_short
        (bytes := bytes) hshort

theorem decodeCalldata_address_address_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_ok
        (cd := cd) (x := x) (y := y) (z := z) hsz100 hbig hcanon0 hcanon1

theorem decodeCalldata_address_address_uint256_none_noncanon0 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_none_noncanon0
        (cd := cd) (x := x) (y := y) (z := z) hsz100 hbig hnc0

theorem decodeCalldata_address_address_uint256_none_noncanon1 {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_none_noncanon1
        (cd := cd) (x := x) (y := y) (z := z) hsz100 hbig hcanon0 hnc1

theorem decodeCalldata_address_address_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_none_short
        (cd := cd) (x := x) (y := y) (z := z) hsz4 hshort

theorem decodeCalldata_address_address_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [addr, addr, uint256] cd = none :=
  by
    simpa [addr, uint256, abiUInt256] using
      Reasoning.Theory.decodeCalldata_address_address_uint256_none_huge
        (cd := cd) (x := x) (y := y) (z := z) hbig

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

theorem evalExpr_transferFrom_value_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "value") = .ok (transferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_value]

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
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simpa [allowanceRef] using transferFromStore_allowance I)
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by simp [storageTypeAt?, transferFromAllowanceEvaledRef, erc20Contract,
      erc20StorageDecls, uint256Storage, storageTypeStep?])
    (hloc := erc20Config_storage_allowance
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
      (.address evm.executionEnv.source))]
  simp [transferFromAllowanceEvaledRef, transferFromAllowanceSlot,
    transferFromCurrentAllowanceWord, erc20StorageLocLoad_uint256]

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
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by
      simp only [balanceOfRef]
      rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
        transferFromStore_balanceOf])
    (her := evalStorageRef_transferFrom_from_balance_currentAllowance evm evm I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
      erc20StorageDecls, uint256Storage, storageTypeStep?])
    (hloc := erc20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))]
  simp [transferFromFromBalanceEvaledRef, transferFromFromSlot, transferFromFromBalanceWord,
    erc20StorageLocLoad_uint256]

theorem evalExpr_transferFrom_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue evm' I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simpa [balanceOfRef] using transferFromStoreFromBalance_balanceOf evm I)
    (her := evalStorageRef_transferFrom_from_balance_fromBalance evm evm' I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
      erc20StorageDecls, uint256Storage, storageTypeStep?])
    (hloc := erc20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))]
  simp [transferFromFromBalanceEvaledRef, transferFromFromSlot, transferFromFromBalanceWord,
    erc20StorageLocLoad_uint256]

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
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterAllowanceState evm I) := by
  simp only [allowanceRef]
  have href : evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      { base := "allowance", steps := [.mindex (.var "from"), .mindex sender] } =
        .ok (transferFromAllowanceEvaledRef evm I) := by
    simp [evalStorageRef, evalStorageRefStep, sender, envValue, evalExpr?,
      transferFromAllowanceEvaledRef, transferFromFromValue, valueToKey?,
      EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
      evalExpr_transferFrom_from_fromBalance]
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by simpa [allowanceRef] using transferFromStoreFromBalance_allowance evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromAllowanceEvaledRef, erc20Contract,
        erc20StorageDecls, uint256Storage, storageTypeStep?])
      (hloc := erc20Config_storage_allowance
        (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        (.address evm.executionEnv.source))
  rw [erc20StorageLocStore_uint256]
  simp [transferFromAfterAllowanceState, transferFromAllowanceSlot]

theorem evalExpr_transferFrom_balance_debit_raw (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .ok (.int
          (Int.ofNat (transferFromFromBalanceWord evm' I).toNat -
            Int.ofNat (transferFromValueWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_from_balance_fromBalance evm evm' I,
    evalExpr_transferFrom_value_fromBalance evm evm' I]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, transferFromFromBalanceValue,
    transferFromValueValue]

theorem evalExpr_transferFrom_balance_debit (evm evm' : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm' I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (valueInUInt256
        (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value"))) =
        .ok (.int (Int.ofNat (transferFromBalanceDebitWord evm' I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromFromBalanceWord evm' I).toNat -
          Int.ofNat (transferFromValueWord I).toNat =
        Int.ofNat
          ((transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromBalanceDebitWord evm' I).toNat =
      (transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromBalanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromFromBalanceWord evm' I).val.isLt)
  have hltNat :
      (transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat <
        2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using
        (transferFromFromBalanceWord evm' I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat) ≥
      (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg : ¬
      (Int.ofNat
        ((transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound : ¬
      115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (transferFromFromBalanceWord evm' I).toNat - (transferFromValueWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold valueInUInt256
    unfold evalExpr?
  rw [evalExpr_transferFrom_balance_debit_raw evm evm' I, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromFromBalanceWord evm' I).toNat -
        (transferFromValueWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFrom_balance_debit_revert (evm evm' : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord evm' I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (valueInUInt256
        (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value"))) = .revert := by
  have hneg :
      Int.ofNat (transferFromFromBalanceWord evm' I).toNat -
          Int.ofNat (transferFromValueWord I).toNat < 0 := by
    have hltInt : Int.ofNat (transferFromFromBalanceWord evm' I).toNat <
        Int.ofNat (transferFromValueWord I).toNat :=
      Int.ofNat_lt.mpr hlt
    omega
  have hnotEnough : ¬
      (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm' I).toNat :=
    Nat.not_le_of_lt hlt
  conv_lhs =>
    unfold valueInUInt256
    unfold evalExpr?
  rw [evalExpr_transferFrom_balance_debit_raw evm evm' I]
  simp [EvalResult.bind, bind, pure, uint256Int, hneg, hnotEnough]

theorem transferFromAssignFrom (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat
        (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterBalanceState evm I) := by
  simp only [balanceOfRef]
  have href := evalStorageRef_transferFrom_from_balance_fromBalance evm
    (transferFromAfterAllowanceState evm I) I
  simp only [balanceOfRef] at href
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by simpa [balanceOfRef] using transferFromStoreFromBalance_balanceOf evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
        erc20StorageDecls, uint256Storage, storageTypeStep?])
      (hloc := erc20Config_storage_balanceOf
        (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))
  rw [erc20StorageLocStore_uint256]
  simp [transferFromAfterBalanceState, transferFromFromSlot, transferFromAfterAllowance_codeOwner]

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
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simpa [balanceOfRef] using transferFromStoreFromBalance_balanceOf evm I)
    (her := evalStorageRef_transferFrom_to_balance_fromBalance evm
      (transferFromAfterBalanceState evm I) I)
    (hty := by simp [storageTypeAt?, transferFromToEvaledRef, erc20Contract,
      erc20StorageDecls, uint256Storage, storageTypeStep?])
    (hloc := erc20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromToWord I).toNat)))]
  simp [transferFromToEvaledRef, transferFromToSlot, transferFromToBalanceWord,
    erc20StorageLocLoad_uint256, transferFromAfterBalance_codeOwner]

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
      (transferFromAfterBalanceState evm I) .storage (balanceOfRef (.var "to"))
      (transferFromNewToValue evm I) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreNewToBalance evm I },
          transferFromPostState evm I) := by
  simp only [balanceOfRef]
  have href := evalStorageRef_transferFrom_to_balance_newToBalance evm
    (transferFromAfterBalanceState evm I) I
  simp only [balanceOfRef] at href
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by simpa [balanceOfRef] using transferFromStoreNewToBalance_balanceOf evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromToEvaledRef, erc20Contract, erc20StorageDecls,
        uint256Storage, storageTypeStep?])
      (hloc := erc20Config_storage_balanceOf
        (.address (AccountAddress.ofNat (transferFromToWord I).toNat)))
  rw [← transferFromNewToWord_toNat evm I hfit]
  rw [erc20StorageLocStore_uint256]
  simp [transferFromPostState, transferFromToSlot, transferFromAfterBalance_codeOwner]

theorem erc20TransferFromBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
        (transferFromPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowance)
      (transferFromAssignAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_balance_debit evm (transferFromAfterAllowanceState evm I) I
        hbalanceDebit)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_newToBalance evm I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_newToBalance_var evm I)
      (transferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem erc20TransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_allowance_false evm I hlt))

theorem erc20TransferFromBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hlt : (transferFromFromBalanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_from_false evm I hlt))

theorem erc20TransferFromBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowance)
      (transferFromAssignAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_balance_debit evm (transferFromAfterAllowanceState evm I) I
        hbalanceDebit)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_transferFrom_newToBalance_revert evm I hover))

theorem erc20TransferFromBodyReverts_balanceDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat)
    (hltDebit : (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromValueWord I).toNat) :
    ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowance)
      (transferFromAssignAllowance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_transferFrom_balance_debit_revert evm (transferFromAfterAllowanceState evm I) I
        hltDebit))

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
    show 128 - 96 = 32 from by norm_num,
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
        show 128 - 96 = 32 from by norm_num,
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
      show 128 - 96 = 32 from by norm_num]
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

theorem erc20TransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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

theorem erc20TransferFromX_dec1874_from {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨2134⟩, dup7, dup3, dup8, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `from` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2134` from chain. -/
theorem erc20TransferFromX_dec2134 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2134⟩
        [transferFromFromWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨199⟩, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec1874_from (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz100 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanonFrom (by jump_dest) (by evm_ov)

theorem erc20TransferFromX_dec1874_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec2134 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨2151⟩, dup7, dup3, dup8,
    add, push2 ⟨1874⟩, jump erc20_jd ]⟩

/-- The `to` address decode (success): a second application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2151` to chain. -/
theorem erc20TransferFromX_dec2151 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec1874_to (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.erc20DecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem erc20TransferFromX_dec1925_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec2151 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨2168⟩, dup7, dup3, dup8,
    add, push2 ⟨1925⟩, jump erc20_jd ]⟩

theorem erc20TransferFromX_dec1903_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
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
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec1925_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1939⟩, dup2,
    push2 ⟨1903⟩, jump erc20_jd ]⟩

theorem erc20TransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨613⟩
        [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd1903⟩ := erc20TransferFromX_dec1903_value (cA := cA) (gh := gh)
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
theorem erc20TransferFromX_afterAllowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨805⟩
        [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
          transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd613⟩ := erc20TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hsenderCleanL :
      UInt256.land erc20AddrMask (transferFromSenderWord I) = transferFromSenderWord I :=
    erc20AddrMask_clean_left (transferFromSenderWord_canonical I)
  have hslot := transferFromAllowanceKeccakSlot I hcanonFrom
  have rd663₀ := evm_run rd613 with [
    jumpdest, push0, push0, push1 ⟨1⟩, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd663 := rd663₀
  rw [hfromCleanL, hfromCleanL] at rd663
  obtain ⟨_, _, rd676⟩ := RD.erc20MappingHashSuffix rd663 erc20_mapping_hash_wf
    (by rfl) (approveInnerOwnerMem_writeSlot (transferFromFromWord I)) (by rfl) (by evm_ov)
  have rd722₀ := evm_run rd676 with [
    push0, caller, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd722 := rd722₀
  rw [hsenderCleanL, hsenderCleanL] at rd722
  obtain ⟨_, _, rd735⟩ := RD.erc20MappingHashSuffix rd722 erc20_mapping_hash_wf
    (by rfl)
    (approveOuterSpenderMem_writeSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  obtain ⟨k1, C1, rd736₀⟩ := rd735.sload (by decide) (by evm_ov)
  have rd737 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨737⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1 C1 := by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot,
      transferFromAllowanceSlotI, transferFromSenderWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, transferFromSender_ofNat] using rd736₀
  have hlt : UInt256.lt
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨0⟩ := ult_zero hallowance
  exact ⟨_, _, evm_run rd737 with [
    swap1, pop, dup3, dup2, lt, iszero,
    push2 ⟨805⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

/-- After the allowance check, `transferFrom` loads `balanceOf[from]` using the same
    balance mapping layout as `transfer`, checks `value <= fromBalance`, and reaches the
    mutation branch. -/
theorem erc20TransferFromX_afterBalance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨932⟩
        [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
          transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        (balanceOfHashMem (transferFromFromWord I))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd805⟩ := erc20TransferFromX_afterAllowance (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hallowance hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd854₀ := evm_run rd805 with [
    jumpdest, dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd854 := rd854₀
  rw [hfromCleanL, hfromCleanL] at rd854
  obtain ⟨_, _, rd867⟩ := RD.erc20MappingHashSuffix rd854 erc20_mapping_hash_wf
    (by rfl)
    (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  obtain ⟨k1, C1, rd868₀⟩ := rd867.sload (by decide) (by evm_ov)
  have rd868 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨868⟩
      [transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromFromBalanceWord, transferFromFromSlot, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd868₀
  have hlt : UInt256.lt
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨0⟩ := ult_zero hbalance
  exact ⟨_, _, evm_run rd868 with [
    lt, iszero, push2 ⟨932⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

theorem erc20TransferFromX_afterAllowanceStore {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1069⟩
        [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
          transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd932⟩ := erc20TransferFromX_afterBalance (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hallowance hbalance hreach
  have rd2552 := evm_run rd932 with [
    jumpdest, dup3, dup2, push2 ⟨944⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd944₀⟩ := erc20RoutineCheckedSub rd2552 hallowance erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferFromValueWord I) =
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat hallowance]
    unfold transferFromAllowanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd944 := rd944₀
  rw [hdebit] at rd944
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hsenderCleanL :
      UInt256.land erc20AddrMask (transferFromSenderWord I) = transferFromSenderWord I :=
    erc20AddrMask_clean_left (transferFromSenderWord_canonical I)
  have hslot := transferFromAllowanceKeccakSlot I hcanonFrom
  have rd993₀ := evm_run rd944 with [
    jumpdest, push1 ⟨1⟩, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd993 := rd993₀
  rw [hfromCleanL, hfromCleanL] at rd993
  obtain ⟨_, _, rd1006⟩ := RD.erc20MappingHashSuffix rd993 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner_self (transferFromFromWord I))
    (balanceOfHashMem_writeAllowanceSlot (transferFromFromWord I)) (by rfl) (by evm_ov)
  have rd1052₀ := evm_run rd1006 with [
    push0, caller, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd1052 := rd1052₀
  rw [hsenderCleanL, hsenderCleanL] at rd1052
  obtain ⟨_, _, rd1065⟩ := RD.erc20MappingHashSuffix rd1052 erc20_mapping_hash_wf
    (by rfl)
    (approveOuterSpenderMem_writeSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  have rd1067 := evm_run rd1065 with [ dup2, swap1 ]
  obtain ⟨k2, C2, rd1067s⟩ := rd1067.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1067s with [ pop ]⟩

theorem erc20TransferFromX_afterFromStore {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1151⟩
        [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
          transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        (balanceOfHashMem (transferFromFromWord I))
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C := by
  obtain ⟨k, C, rd1069⟩ := erc20TransferFromX_afterAllowanceStore (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonFrom hcanonTo hallowance hbalance hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd1117₀ := evm_run rd1069 with [
    dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1117 := rd1117₀
  rw [hfromCleanL, hfromCleanL] at rd1117
  obtain ⟨_, _, rd1130₀⟩ := RD.erc20MappingHashSuffix rd1117 erc20_mapping_hash_wf
    (by rfl)
    (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  have rd1130 := evm_run rd1130₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1134₀⟩ := rd1130.sload (by decide) (by evm_ov)
  have rd1134 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [transferFromFromBalanceWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I,
        transferFromValueWord I, ⟨0⟩, transferFromFromSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    unfold transferFromFromBalanceWord
    rw [transferFromAfterAllowance_codeOwner (initState cA gh bl σ σ₀ g A I) I]
    simpa [transferFromFromSlot, transferFromAfterAllowanceState,
      transferFromAllowanceSlot, transferFromAllowanceSlotI, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, erc20StorageStore_accountMap]
      using rd1134₀
  have rd2552 := evm_run rd1134 with [
    push2 ⟨1143⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1143₀⟩ := erc20RoutineCheckedSub rd2552 hbalanceDebit erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (transferFromFromBalanceWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
          (transferFromValueWord I) =
        transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I := by
    apply u256_inj
    rw [usub_toNat hbalanceDebit]
    unfold transferFromBalanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromFromBalanceWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).val.isLt)]
  have rd1143 := rd1143₀
  rw [hdebit] at rd1143
  have rd1149 := evm_run rd1143 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1149s⟩ := rd1149.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1149s with [ pop ]⟩

theorem erc20TransferFromX_balanceDebitUnderflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hltDebit :
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat <
        (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd1069⟩ := erc20TransferFromX_afterAllowanceStore (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonFrom hcanonTo hallowance hbalance hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd1117₀ := evm_run rd1069 with [
    dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1117 := rd1117₀
  rw [hfromCleanL, hfromCleanL] at rd1117
  obtain ⟨_, _, rd1130₀⟩ := RD.erc20MappingHashSuffix rd1117 erc20_mapping_hash_wf
    (by rfl)
    (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  have rd1130 := evm_run rd1130₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1134₀⟩ := rd1130.sload (by decide) (by evm_ov)
  have rd1134 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1134⟩
      [transferFromFromBalanceWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I,
        transferFromValueWord I, ⟨0⟩, transferFromFromSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    unfold transferFromFromBalanceWord
    rw [transferFromAfterAllowance_codeOwner (initState cA gh bl σ σ₀ g A I) I]
    simpa [transferFromFromSlot, transferFromAfterAllowanceState,
      transferFromAllowanceSlot, transferFromAllowanceSlotI, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, erc20StorageStore_accountMap]
      using rd1134₀
  have rd2552 := evm_run rd1134 with [
    push2 ⟨1143⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  exact erc20RoutineCheckedSub_underflow rd2552 hltDebit
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20TransferFromX_afterToStore {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1233⟩
        [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
          transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
        (balanceOfHashMem (transferFromToWord I))
        (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
              (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
            (transferFromFromSlot I)
            (transferFromBalanceDebitWord
              (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I))
          (transferFromToSlot I)
          (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd1151⟩ := erc20TransferFromX_afterFromStore (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonFrom hcanonTo hallowance hbalance hbalanceDebit hreach
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) = transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferFromToKeccakSlot I hcanonTo
  have rd1199₀ := evm_run rd1151 with [
    dup3, push0, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1199 := rd1199₀
  rw [htoCleanL, htoCleanL] at rd1199
  obtain ⟨_, _, rd1215₀⟩ := RD.erc20MappingHashSuffix rd1199 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner (transferFromFromWord I) (transferFromToWord I))
    (balanceOfHashMem_writeSlot_self (transferFromToWord I)) hslot (by evm_ov)
  have rd1215 := evm_run rd1215₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1216₀⟩ := rd1215.sload (by decide) (by evm_ov)
  have rd1216 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩
      [transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I, ⟨0⟩, transferFromToSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k1 C1 := by
    simpa [transferFromToBalanceWord, transferFromAfterBalanceState,
      transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
      initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      erc20StorageStore_accountMap, transferFromAfterAllowance_codeOwner]
      using rd1216₀
  have rd2603 := evm_run rd1216 with [
    push2 ⟨1225⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1225₀⟩ := erc20RoutineCheckedAdd rd2603
    (by simpa [transferFromNewToNat] using hfit)
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I +
          transferFromValueWord I =
        transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [transferFromNewToNat] using hfit)]
    unfold transferFromNewToWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1225 := rd1225₀
  rw [hnew] at rd1225
  have rd1231 := evm_run rd1225 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1231s⟩ := rd1231.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1231s with [ pop ]⟩

theorem erc20X_transferFrom {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I))
        (transferFromToSlot I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd1233⟩ := erc20TransferFromX_afterToStore (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonFrom hcanonTo hallowance hbalance hbalanceDebit hfit hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) =
      transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) =
      transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have rd1279₀ := evm_run rd1233 with [
    dup4, push20 erc20AddrMask, and, dup6, push20 erc20AddrMask, and ]
  have rd1279 := rd1279₀
  rw [htoCleanL, hfromCleanL] at rd1279
  have rd1312₀ := rd1279.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd2073 := evm_run rd1312₀ with [
    dup6, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferFromToWord I))
      (by decide) (by evm_ov),
    push2 ⟨1325⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd1325⟩ := erc20RoutineEncodeUint256FromMem
    (val := transferFromValueWord I) (ret := ⟨1325⟩)
    (R := [transferTransferTopic, transferFromFromWord I, transferFromToWord I,
      transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
      transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1333 := evm_run rd1325 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1334 := rd1333.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd204 := evm_run rd1334 with [
    push1 ⟨1⟩, swap2, pop, pop, swap4, swap3, pop, pop, pop, jump erc20_jd ]
  have rd2033 := evm_run rd204 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    push2 ⟨217⟩, swap2, swap1, push2 ⟨2033⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd217⟩ := erc20RoutineEncodeBoolFromMem
    (val := (⟨1⟩ : UInt256)) (ret := ⟨217⟩) (R := [sel])
    rd2033
    (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide])
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd217 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (transferReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        exact transferReturnMem_read128 (transferFromToWord I) (transferFromValueWord I))
      (by evm_ov) ]

theorem erc20TransferFromX_overflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hover : UInt256.size ≤
      transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd1151⟩ := erc20TransferFromX_afterFromStore (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonFrom hcanonTo hallowance hbalance hbalanceDebit hreach
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) = transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferFromToKeccakSlot I hcanonTo
  have rd1199₀ := evm_run rd1151 with [
    dup3, push0, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1199 := rd1199₀
  rw [htoCleanL, htoCleanL] at rd1199
  obtain ⟨_, _, rd1215₀⟩ := RD.erc20MappingHashSuffix rd1199 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner (transferFromFromWord I) (transferFromToWord I))
    (balanceOfHashMem_writeSlot_self (transferFromToWord I)) hslot (by evm_ov)
  have rd1215 := evm_run rd1215₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1216₀⟩ := rd1215.sload (by decide) (by evm_ov)
  have rd1216 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩
      [transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I, ⟨0⟩, transferFromToSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k1 C1 := by
    simpa [transferFromToBalanceWord, transferFromAfterBalanceState,
      transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
      initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      erc20StorageStore_accountMap, transferFromAfterAllowance_codeOwner]
      using rd1216₀
  have rd2603 := evm_run rd1216 with [
    push2 ⟨1225⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  exact erc20RoutineCheckedAdd_overflow rd2603
    (by simpa [transferFromNewToNat] using hover)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20TransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 3) hsz4
      (by simpa using hshort) hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2120⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20TransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 3) hbig hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2121⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2120⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20TransferFromX_noncanon_from {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferFromFromWord I)
      (UInt256.land (transferFromFromWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec1874_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20TransferFromX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (transferFromToWord I)
      (UInt256.land (transferFromToWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20TransferFromX_dec1874_to (cA := cA) (gh := gh)
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
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [approveTransition, totalSupplyTransition])
    (post := [balanceOfTransition, transferTransition, allowanceTransition])
    rfl rfl ?_ (by rw [selectorOf, erc20TransferFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, erc20ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TotalSupplySelectorBytes, hcd]; decide

/-- ERC20-local trace fact for the `require(currentAllowance >= value)` failure path.
    The branch builds `Error("ERC20: insufficient allowance")` and reverts. -/
theorem erc20TransferFromX_insufficientAllowance {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd613⟩ := erc20TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hsenderCleanL :
      UInt256.land erc20AddrMask (transferFromSenderWord I) = transferFromSenderWord I :=
    erc20AddrMask_clean_left (transferFromSenderWord_canonical I)
  have hslot := transferFromAllowanceKeccakSlot I hcanonFrom
  have rd663₀ := evm_run rd613 with [
    jumpdest, push0, push0, push1 ⟨1⟩, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd663 := rd663₀
  rw [hfromCleanL, hfromCleanL] at rd663
  obtain ⟨_, _, rd676⟩ := RD.erc20MappingHashSuffix rd663 erc20_mapping_hash_wf
    (by rfl) (approveInnerOwnerMem_writeSlot (transferFromFromWord I)) (by rfl) (by evm_ov)
  have rd722₀ := evm_run rd676 with [
    push0, caller, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd722 := rd722₀
  rw [hsenderCleanL, hsenderCleanL] at rd722
  obtain ⟨_, _, rd735⟩ := RD.erc20MappingHashSuffix rd722 erc20_mapping_hash_wf
    (by rfl)
    (approveOuterSpenderMem_writeSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  obtain ⟨k1, C1, rd736₀⟩ := rd735.sload (by decide) (by evm_ov)
  have rd737 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨737⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1 C1 := by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot,
      transferFromAllowanceSlotI, transferFromSenderWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, transferFromSender_ofNat] using rd736₀
  have hltw : UInt256.lt
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨1⟩ := ult_one hlt
  have rd742₀ := evm_run rd737 with [ swap1, pop, dup3, dup2, lt ]
  have rd742 := rd742₀
  rw [hltw] at rd742
  have rd743₀ := evm_run rd742 with [ iszero ]
  have rd743 := rd743₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd743
  have rd747 := evm_run rd743 with [
    push2 ⟨805⟩, jumpiNT (by decide) ]
  have rd750 := evm_run rd747 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceOuterHashMem_mload64 (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov) ]
  have rd783 := rd750.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd785 := evm_run rd783 with [
    dup2,
    raw mstore 6
      (transferFromInsufficientAllowanceSelectorMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2373 := evm_run rd785 with [
    push1 ⟨4⟩, add, push2 ⟨796⟩, swap1, push2 ⟨2373⟩, jump erc20_jd ]
  have rd2388 := evm_run rd2373 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3
      (transferFromInsufficientAllowanceOffsetMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2339 := evm_run rd2388 with [
    push2 ⟨2396⟩, dup2, push2 ⟨2339⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2339 with [
    jumpdest, push0, push2 ⟨2351⟩, push1 ⟨29⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2351 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3
      (transferFromInsufficientAllowanceLengthMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop, swap3, swap2, pop, pop,
    jump erc20_jd ]
  have rd2299 := evm_run rd2351 with [
    jumpdest, swap2, pop, push2 ⟨2362⟩, dup3, push2 ⟨2299⟩, jump erc20_jd ]
  have rd2300 := evm_run rd2299 with [ jumpdest ]
  have rd2333 := rd2300.pushConst transferFromInsufficientAllowanceWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2362 := evm_run rd2333 with [
    push0, dup3, add,
    raw mstore 3
      (transferFromInsufficientAllowanceStringMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2396 := evm_run rd2362 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd796ret := evm_run rd2396 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd796 := evm_run rd796ret with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferFromInsufficientAllowanceStringMem_mload64 (transferFromFromWord I)
        (transferFromSenderWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd796.rev 0 (by decide) mem_cost (by evm_ov)

/-- ERC20-local trace fact for the `require(balanceOf[from] >= value)` failure path.
    The branch builds `Error("ERC20: insufficient balance")` and reverts. -/
theorem erc20TransferFromX_insufficientBalance {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd805⟩ := erc20TransferFromX_afterAllowance (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hallowance hreach
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd854₀ := evm_run rd805 with [
    jumpdest, dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd854 := rd854₀
  rw [hfromCleanL, hfromCleanL] at rd854
  obtain ⟨_, _, rd867⟩ := RD.erc20MappingHashSuffix rd854 erc20_mapping_hash_wf
    (by rfl)
    (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
    hslot (by evm_ov)
  obtain ⟨k1, C1, rd868₀⟩ := rd867.sload (by decide) (by evm_ov)
  have rd868 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨868⟩
      [transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I,
        transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromFromBalanceWord, transferFromFromSlot, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd868₀
  have hltw : UInt256.lt
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨1⟩ := ult_one hlt
  have rd869₀ := evm_run rd868 with [ lt ]
  have rd869 := rd869₀
  rw [hltw] at rd869
  have rd870₀ := evm_run rd869 with [ iszero ]
  have rd870 := rd870₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd870
  have rd874 := evm_run rd870 with [
    push2 ⟨932⟩, jumpiNT (by decide) ]
  have rd877 := evm_run rd874 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferFromFromWord I))
      (by decide) (by evm_ov) ]
  have rd910 := rd877.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd912 := evm_run rd910 with [
    dup2,
    raw mstore 6 (transferInsufficientSelectorMem (transferFromFromWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2477 := evm_run rd912 with [
    push1 ⟨4⟩, add, push2 ⟨923⟩, swap1, push2 ⟨2477⟩, jump erc20_jd ]
  have rd2492 := evm_run rd2477 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3 (transferInsufficientOffsetMem (transferFromFromWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2443 := evm_run rd2492 with [
    push2 ⟨2500⟩, dup2, push2 ⟨2443⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2443 with [
    jumpdest, push0, push2 ⟨2455⟩, push1 ⟨27⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2455 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3 (transferInsufficientLengthMem (transferFromFromWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop, swap3, swap2, pop, pop,
    jump erc20_jd ]
  have rd2403 := evm_run rd2455 with [
    jumpdest, swap2, pop, push2 ⟨2466⟩, dup3, push2 ⟨2403⟩, jump erc20_jd ]
  have rd2404 := evm_run rd2403 with [ jumpdest ]
  have rd2437 := rd2404.pushConst transferInsufficientBalanceWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2466 := evm_run rd2437 with [
    push0, dup3, add,
    raw mstore 3 (transferInsufficientStringMem (transferFromFromWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2500 := evm_run rd2466 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd923ret := evm_run rd2500 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd923 := evm_run rd923ret with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferInsufficientStringMem_mload64 (transferFromFromWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd923.rev 0 (by decide) mem_cost (by evm_ov)

theorem erc20TransferFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc20TransferFromSelector_size hsel
  have hd := erc20Dispatch_transferFrom (cd := I.calldata) hsel
  let σ := σ_evm
  let σ₀ := σ₀
  let evmE := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageLoad_codeOwner
      (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        (.address I.source))
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I)
      (transferFromAfterAllowanceState evmS I) := by
    simpa [transferFromAfterAllowanceState, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageStore_codeOwner
      (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        (.address I.source)) (by
          simpa [transferFromAllowanceDebitWord, evmE, evmS] using
            congrArg
              (fun w : UInt256 =>
                UInt256.ofNat (w.toNat - (transferFromValueWord I).toNat))
              hAllowance)
  have hFromBalance :
      transferFromFromBalanceWord evmE I = transferFromFromBalanceWord evmS I := by
    simpa [transferFromFromBalanceWord] using
      hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hAfterAllowanceFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    simpa [transferFromFromBalanceWord] using
      hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceState evmE I)
      (transferFromAfterBalanceState evmS I) := by
    simpa [transferFromAfterBalanceState] using
      hσAllowance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromFromSlot I)
      (by simp [transferFromBalanceDebitWord, hAfterAllowanceFromBalance])
  have hToBalance :
      transferFromToBalanceWord evmE I = transferFromToBalanceWord evmS I := by
    simpa [transferFromToBalanceWord] using
      hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromToSlot I)
  have hNewToNat : transferFromNewToNat evmE I = transferFromNewToNat evmS I := by
    simp [transferFromNewToNat, hToBalance]
  have hσPost : EVMStateEquiv (transferFromPostState evmE I) (transferFromPostState evmS I) := by
    simpa [transferFromPostState] using
      hσBalance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromToSlot I)
      (by simp [transferFromNewToWord, hNewToNat])
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus
        · have hdec := erc20Decode_transferFrom_ok (I := I)
            hsz100 hbig hcanonFrom hcanonTo
          by_cases hallowance : (transferFromValueWord I).toNat ≤
              (transferFromCurrentAllowanceWord
                (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat
          · by_cases hbalance : (transferFromValueWord I).toNat ≤
                (transferFromFromBalanceWord
                  (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat
            · by_cases hbalanceDebit : (transferFromValueWord I).toNat ≤
                (transferFromFromBalanceWord
                  (transferFromAfterAllowanceState
                    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat
              · by_cases hfit :
                transferFromNewToNat
                    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I <
                  UInt256.size
                · have hbody := erc20TransferFromBodyReturns evmS I
                      (by simp only [evmS, initState]; exact hwv)
                      (by simpa [evmE, hAllowance] using hallowance)
                      (by simpa [evmE, hFromBalance] using hbalance)
                      (by simpa [evmE, hAfterAllowanceFromBalance] using hbalanceDebit)
                      (by simpa [evmE, hNewToNat] using hfit)
                  exact (erc20X_transferFrom (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hallowance hbalance
                    hbalanceDebit hfit
                    hreach)
                  |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                    (by simp [evmE, transferFromPostState, transferFromAfterBalanceState,
                      transferFromAfterAllowanceState, transferFromAllowanceSlot,
                      transferFromAllowanceSlotI, initState, erc20StorageStore_createdAccounts])
                    (accountMapEquiv.of_eq (by
                      simp [evmE, transferFromPostState, transferFromAfterBalanceState,
                        transferFromAfterAllowanceState, transferFromAllowanceSlot,
                        transferFromAllowanceSlotI, initState, erc20StorageStore_accountMap]))
                    hσPost
                    (returnEquiv_of_encode erc20BoolTrueReturnEncoding)
                · have hover :
                    UInt256.size ≤
                      transferFromNewToNat
                        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I := by
                    omega
                  have hbody := erc20TransferFromBodyReverts_overflow evmS I
                      (by simp only [evmS, initState]; exact hwv)
                      (by simpa [evmE, hAllowance] using hallowance)
                      (by simpa [evmE, hFromBalance] using hbalance)
                      (by simpa [evmE, hAfterAllowanceFromBalance] using hbalanceDebit)
                      (by simpa [evmE, hNewToNat] using hover)
                  exact (erc20TransferFromX_overflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hallowance hbalance
                    hbalanceDebit hover
                    hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hltDebit :
                  (transferFromFromBalanceWord
                    (transferFromAfterAllowanceState
                      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat <
                    (transferFromValueWord I).toNat := by
                  omega
                have hbody := erc20TransferFromBodyReverts_balanceDebit evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  (by simpa [evmE, hAllowance] using hallowance)
                  (by simpa [evmE, hFromBalance] using hbalance)
                  (by simpa [evmE, hAfterAllowanceFromBalance] using hltDebit)
                exact (erc20TransferFromX_balanceDebitUnderflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hallowance hbalance hltDebit
                    hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hlt :
                (transferFromFromBalanceWord
                    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
                  (transferFromValueWord I).toNat := by
                omega
              have hbody := erc20TransferFromBodyReverts_balance evmS I
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [evmE, hAllowance] using hallowance)
                (by simpa [evmE, hFromBalance] using hlt)
              exact (erc20TransferFromX_insufficientBalance (g := Sat256.ofUInt256 g)
                  hsz100 hsize hbig hcanonFrom hcanonTo hallowance hlt hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hlt :
              (transferFromCurrentAllowanceWord
                  (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
                (transferFromValueWord I).toNat := by
              omega
            have hbody := erc20TransferFromBodyReverts_allowance evmS I
              (by simp only [evmS, initState]; exact hwv)
              (by simpa [evmE, hAllowance] using hlt)
            exact (erc20TransferFromX_insufficientAllowance (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonFrom hcanonTo hlt hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := erc20Decode_transferFrom_none_noncanon_to (I := I)
            hsz100 hbig hcanonFrom hcanonTo
          have hnc : UInt256.eq (transferFromToWord I)
              (UInt256.land (transferFromToWord I) erc20AddrMask) = ⟨0⟩ :=
            erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
          exact (erc20TransferFromX_noncanon_to (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonFrom hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc20Decode_transferFrom_none_noncanon_from (I := I)
          hsz100 hbig hcanonFrom
        have hnc : UInt256.eq (transferFromFromWord I)
            (UInt256.land (transferFromFromWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonFrom (erc20Word_canonical_of_clean he))
        exact (erc20TransferFromX_noncanon_from (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_transferFrom_none_huge (I := I) hbigge
      exact (erc20TransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc20Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (erc20TransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec
