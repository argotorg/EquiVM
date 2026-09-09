import Examples.VyperERC20.Transfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

/-! ## Source-level body for `transferFrom(address,address,uint256)` -/

/-- The raw ABI word for `transferFrom`'s `from` argument. -/
abbrev transferFromFromWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `transferFrom`'s `to` argument. -/
abbrev transferFromToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

/-- The raw ABI word for `transferFrom`'s `value` argument. -/
abbrev transferFromValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

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

def transferFromCurrentAllowanceRaw (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferFromAllowanceSlotI I) ⟨0⟩)
    (Batteries.RBMap.find? σ I.codeOwner)

def transferFromFromBalanceRaw (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferFromFromSlot I) ⟨0⟩)
    (Batteries.RBMap.find? σ I.codeOwner)

def transferFromFromBalanceRawAfterAllowance
    (σ : AccountMap) (I : ExecutionEnv) (allowanceDebit : UInt256) : UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferFromFromSlot I) ⟨0⟩)
    (Batteries.RBMap.find?
      (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I) allowanceDebit) I.codeOwner)

def transferFromToBalanceRawAfterBalance
    (σ : AccountMap) (I : ExecutionEnv)
    (allowanceDebit balanceDebit : UInt256) : UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferFromToSlot I) ⟨0⟩)
    (Batteries.RBMap.find?
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I) allowanceDebit)
        (transferFromFromSlot I) balanceDebit) I.codeOwner)

def transferFromAccountMapAfterAllowanceI
    (σ : AccountMap) (I : ExecutionEnv) (allowanceDebit : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I) allowanceDebit

def transferFromAccountMapAfterBalanceI
    (σ : AccountMap) (I : ExecutionEnv)
    (allowanceDebit balanceDebit : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (transferFromAccountMapAfterAllowanceI σ I allowanceDebit)
    (transferFromFromSlot I) balanceDebit

def transferFromAccountMapAfterToI
    (σ : AccountMap) (I : ExecutionEnv)
    (allowanceDebit balanceDebit newTo : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (transferFromAccountMapAfterBalanceI σ I allowanceDebit balanceDebit)
    (transferFromToSlot I) newTo

theorem transferFromCurrentAllowanceRaw_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromCurrentAllowanceRaw σ I =
      transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I := by
  simpa [transferFromCurrentAllowanceRaw, transferFromCurrentAllowanceWord,
    transferFromAllowanceSlot, transferFromAllowanceSlotI, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]

theorem transferFromFromBalanceRaw_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromFromBalanceRaw σ I =
      transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
  simpa [transferFromFromBalanceRaw, transferFromFromBalanceWord,
    transferFromFromSlot, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem transferFromFromBalanceRawAfterAllowance_initState
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromFromBalanceRawAfterAllowance σ I
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I) =
      transferFromFromBalanceWord (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hcodeOwner :
      (transferFromAfterAllowanceState evm0 I).executionEnv.codeOwner = I.codeOwner := by
    simpa [evm0, initState] using transferFromAfterAllowance_codeOwner (evm := evm0) (I := I)
  unfold transferFromFromBalanceWord Solm.EVM.storageLoad
  rw [hcodeOwner]
  simpa [evm0, transferFromFromBalanceRawAfterAllowance, transferFromAfterAllowanceState,
    transferFromAllowanceSlot, transferFromAllowanceSlotI, initState, State.lookupAccount,
    Account.lookupStorage, vyperERC20StorageStore_accountMap]

theorem transferFromToBalanceRawAfterBalance_initState
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromToBalanceRawAfterBalance σ I
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I) =
      transferFromToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
  simpa [transferFromToBalanceRawAfterBalance, transferFromToBalanceWord,
    transferFromAfterBalanceState, transferFromAfterAllowanceState,
    transferFromAfterBalance_codeOwner, transferFromAfterAllowance_codeOwner,
    transferFromAllowanceSlot, transferFromAllowanceSlotI, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, vyperERC20StorageStore_accountMap]

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
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferFromTransition.params.map Param.name)
      (transitionSignature ERC20.transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldataWithMode DecodeMode.vyper ["from", "to", "value"] [addr, addr, uint256]
    I.calldata = _
  simpa [addr, uint256, abiUInt256, transferFromStore, transferFromFromValue,
    transferFromToValue, transferFromValueValue, transferFromFromWord, transferFromToWord,
    transferFromValueWord, calldataWord]
    using decodeCalldataWithMode_vyper_address_address_uint256_ok
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hcanonFrom hcanonTo

theorem erc20Decode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferFromTransition.params.map Param.name)
      (transitionSignature ERC20.transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["from", "to", "value"] [addr, addr, uint256]
    I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldataWithMode_vyper_address_address_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort

theorem erc20Decode_transferFrom_none_noncanon_from {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hnc : ¬ (transferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferFromTransition.params.map Param.name)
      (transitionSignature ERC20.transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["from", "to", "value"] [addr, addr, uint256]
    I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromFromWord]
    using decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hnc

theorem erc20Decode_transferFrom_none_noncanon_to {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferFromTransition.params.map Param.name)
      (transitionSignature ERC20.transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["from", "to", "value"] [addr, addr, uint256]
    I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromFromWord, transferFromToWord]
    using decodeCalldataWithMode_vyper_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hcanonFrom hnc

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
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_from]

theorem evalExpr_transferFrom_from_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_from]

theorem evalExpr_transferFrom_from_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "from") = .ok (transferFromFromValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_from]

theorem evalExpr_transferFrom_to_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_to]

theorem evalExpr_transferFrom_to_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } evm'
      (.var "to") = .ok (transferFromToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreNewToBalance_to]

theorem evalExpr_transferFrom_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.var "value") = .ok (transferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_value]

theorem evalExpr_transferFrom_value_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "value") = .ok (transferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_value]

def transferFromAllowanceEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)),
      .mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
  evalStorageRef vyperERC20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (allowanceRef (.var "from") sender) =
        .ok (transferFromAllowanceEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, ERC20.allowanceRef, sender,
    ERC20.sender, envValue, evalExpr?, transferFromAllowanceEvaledRef,
    transferFromFromValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_from]

theorem evalExpr_transferFrom_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (transferFromCurrentAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simpa [allowanceRef, ERC20.allowanceRef] using transferFromStore_allowance I)
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by simp [storageTypeAt?, transferFromAllowanceEvaledRef, erc20Contract,
      ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
      ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_allowance
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
      (.address evm.executionEnv.source))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferFromAllowanceEvaledRef, transferFromAllowanceSlot,
    transferFromCurrentAllowanceWord]

theorem evalExpr_transferFrom_require_allowance_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? vyperERC20Config
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
    evalExpr? vyperERC20Config
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
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef,
    transferFromFromBalanceEvaledRef, transferFromFromValue, valueToKey?,
    EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr_transferFrom_from_currentAllowance]

theorem evalStorageRef_transferFrom_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceOfRef (.var "from")) = .ok (transferFromFromBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef,
    transferFromFromBalanceEvaledRef, transferFromFromValue, valueToKey?,
    EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr_transferFrom_from_fromBalance]

theorem evalExpr_transferFrom_from_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by
      simp only [balanceOfRef, ERC20.balanceOfRef]
      rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
        transferFromStore_balanceOf])
    (her := evalStorageRef_transferFrom_from_balance_currentAllowance evm evm I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
      ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
      ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferFromFromBalanceEvaledRef, transferFromFromSlot, transferFromFromBalanceWord]

theorem evalExpr_transferFrom_from_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (.storage (balanceOfRef (.var "from"))) =
        .ok (transferFromFromBalanceValue evm' I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by
      simpa [balanceOfRef, ERC20.balanceOfRef] using
        transferFromStoreFromBalance_balanceOf evm I)
    (her := evalStorageRef_transferFrom_from_balance_fromBalance evm evm' I)
    (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
      ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
      ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferFromFromBalanceEvaledRef, transferFromFromSlot, transferFromFromBalanceWord]

theorem evalExpr_transferFrom_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromFromBalanceValue, transferFromValueValue]
  exact henough

theorem evalExpr_transferFrom_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromFromBalanceValue, transferFromValueValue]
  omega

theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? vyperERC20Config
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
    assignStorageRef? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterAllowanceState evm I) := by
  simp only [allowanceRef]
  have href : evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm
      { base := "allowance", steps := [.mindex (.var "from"), .mindex sender] } =
        .ok (transferFromAllowanceEvaledRef evm I) := by
    simp [evalStorageRef, evalStorageRefStep, sender, ERC20.sender, envValue, evalExpr?,
      transferFromAllowanceEvaledRef, transferFromFromValue, valueToKey?,
      EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
      evalExpr_transferFrom_from_fromBalance]
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by
        simpa [allowanceRef, ERC20.allowanceRef] using
          transferFromStoreFromBalance_allowance evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromAllowanceEvaledRef, erc20Contract,
        ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
        ERC20.uint256Storage, storageTypeStep?])
      (hloc := vyperERC20Config_storage_allowance
        (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
        (.address evm.executionEnv.source))
  rw [vyperERC20StorageLocStore_uint256]
  simp [transferFromAfterAllowanceState, transferFromAllowanceSlot]

theorem evalExpr_transferFrom_balance_debit_raw (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
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
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (ERC20.valueInUInt256
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
    unfold ERC20.valueInUInt256
    unfold evalExpr?
  rw [evalExpr_transferFrom_balance_debit_raw evm evm' I, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, ERC20.uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromFromBalanceWord evm' I).toNat -
        (transferFromValueWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFrom_balance_debit_revert (evm evm' : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromFromBalanceWord evm' I).toNat <
      (transferFromValueWord I).toNat) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (ERC20.valueInUInt256
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
    unfold ERC20.valueInUInt256
    unfold evalExpr?
  rw [evalExpr_transferFrom_balance_debit_raw evm evm' I]
  simp [EvalResult.bind, bind, pure, uint256Int, ERC20.uint256Int, hneg, hnotEnough]

theorem transferFromAssignFrom (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat
        (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm I) I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterBalanceState evm I) := by
  simp only [balanceOfRef]
  have href := evalStorageRef_transferFrom_from_balance_fromBalance evm
    (transferFromAfterAllowanceState evm I) I
  simp only [balanceOfRef, ERC20.balanceOfRef] at href
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by
        simpa [balanceOfRef, ERC20.balanceOfRef] using
          transferFromStoreFromBalance_balanceOf evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromFromBalanceEvaledRef, erc20Contract,
        ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
        ERC20.uint256Storage, storageTypeStep?])
      (hloc := vyperERC20Config_storage_balanceOf
        (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)))
  rw [vyperERC20StorageLocStore_uint256]
  simp [transferFromAfterBalanceState, transferFromFromSlot, transferFromAfterAllowance_codeOwner]

def transferFromToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromToWord I).toNat))] }

theorem evalStorageRef_transferFrom_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_fromBalance]

theorem evalStorageRef_transferFrom_to_balance_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferFromToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef,
    transferFromToEvaledRef, transferFromToValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr_transferFrom_to_newToBalance]

theorem evalExpr_transferFrom_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterBalanceState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferFromToBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by
      simpa [balanceOfRef, ERC20.balanceOfRef] using
        transferFromStoreFromBalance_balanceOf evm I)
    (her := evalStorageRef_transferFrom_to_balance_fromBalance evm
      (transferFromAfterBalanceState evm I) I)
    (hty := by simp [storageTypeAt?, transferFromToEvaledRef, erc20Contract,
      ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
      ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferFromToWord I).toNat)))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferFromToEvaledRef, transferFromToSlot, transferFromToBalanceWord,
    transferFromAfterBalance_codeOwner]

theorem evalExpr_transferFrom_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I)
      (ERC20.valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferFromNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat (transferFromNewToNat evm I) < 0 := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  simp only [ERC20.valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, transferFromToBalanceValue, transferFromValueValue,
    transferFromNewToValue, transferFromNewToNat, uint256Int, ERC20.uint256Int, hlt, hnonneg]
  constructor
  · exact Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  · have hfitNat :
        (transferFromToBalanceWord evm I).toNat + (transferFromValueWord I).toNat < 2 ^ 256 := by
      simpa [transferFromNewToNat, UInt256.size] using hfit
    exact Int.ofNat_lt.mpr hfitNat

theorem evalExpr_transferFrom_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterBalanceState evm I)
      (ERC20.valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferFromNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [ERC20.valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_value]
  simp [evalBinaryOp?, transferFromToBalanceValue, transferFromValueValue,
    transferFromNewToValue, transferFromNewToNat, uint256Int, ERC20.uint256Int]
  intro _
  simpa [transferFromNewToNat] using hge

theorem evalExpr_transferFrom_newToBalance_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
      (transferFromAfterBalanceState evm I) (.var "newToBalance") =
        .ok (transferFromNewToValue evm I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreNewToBalance_newToBalance]

theorem transferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? vyperERC20Config
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
      (transferFromAfterBalanceState evm I) .storage (balanceOfRef (.var "to"))
      (transferFromNewToValue evm I) =
        .ok ({ contract := erc20Contract, locals := transferFromStoreNewToBalance evm I },
          transferFromPostState evm I) := by
  simp only [balanceOfRef]
  have href := evalStorageRef_transferFrom_to_balance_newToBalance evm
    (transferFromAfterBalanceState evm I) I
  simp only [balanceOfRef, ERC20.balanceOfRef] at href
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := by
        simpa [balanceOfRef, ERC20.balanceOfRef] using
          transferFromStoreNewToBalance_balanceOf evm I)
      (her := href)
      (hty := by simp [storageTypeAt?, transferFromToEvaledRef, erc20Contract,
        ERC20.erc20Contract, erc20StorageDecls, ERC20.erc20StorageDecls, uint256Storage,
        ERC20.uint256Storage, storageTypeStep?])
      (hloc := vyperERC20Config_storage_balanceOf
        (.address (AccountAddress.ofNat (transferFromToWord I).toNat)))
  rw [← transferFromNewToWord_toNat evm I hfit]
  rw [vyperERC20StorageLocStore_uint256]
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
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferFromStore I)
      ERC20.transferFromTransition.body
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
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferFromStore I)
      ERC20.transferFromTransition.body .reverted := by
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
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferFromStore I)
      ERC20.transferFromTransition.body .reverted := by
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
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferFromStore I)
      ERC20.transferFromTransition.body .reverted := by
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
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferFromStore I)
      ERC20.transferFromTransition.body .reverted := by
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

def transferFromSelectorWord : UInt256 :=
  ⟨0x23b872dd⟩

def transferFromDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 809 ByteArray.empty 30 2

theorem transferFromDispatchMem_size : transferFromDispatchMem.size = 32 := by
  decide +native

macro "vyper_erc20_transferFrom_decode" : tactic =>
  `(tactic| decide +native)

def transferFromFromArgMem (src : UInt256) : ByteArray :=
  (UInt256.toByteArray src).write 0 transferFromDispatchMem 64 32

def transferFromArgsMem (src dst : UInt256) : ByteArray :=
  (UInt256.toByteArray dst).write 0 (transferFromFromArgMem src) 96 32

noncomputable def transferFromAllowanceInnerKeyMem (src dst : UInt256) : ByteArray :=
  wordAt32Mem src (transferFromArgsMem src dst)

noncomputable def transferFromAllowanceInnerHashMem (src dst : UInt256) : ByteArray :=
  wordAt0Mem ⟨1⟩ (transferFromAllowanceInnerKeyMem src dst)

noncomputable def transferFromAllowanceInnerSlotWord (src dst : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((transferFromAllowanceInnerHashMem src dst).readWithPadding 0 64)))

noncomputable def transferFromAllowanceOuterKeyMem (src dst caller : UInt256) : ByteArray :=
  wordAt32Mem caller (transferFromAllowanceInnerHashMem src dst)

noncomputable def transferFromAllowanceOuterHashMem (src dst caller : UInt256) : ByteArray :=
  wordAt0Mem (transferFromAllowanceInnerSlotWord src dst)
    (transferFromAllowanceOuterKeyMem src dst caller)

noncomputable def transferFromAllowanceMem
    (src dst caller allowance : UInt256) : ByteArray :=
  (UInt256.toByteArray allowance).write 0
    (transferFromAllowanceOuterHashMem src dst caller) 128 32

noncomputable def transferFromFromBalanceKeyMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt32Mem src (transferFromAllowanceMem src dst caller allowance)

noncomputable def transferFromFromBalanceHashMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (transferFromFromBalanceKeyMem src dst caller allowance)

noncomputable def transferFromToBalanceKeyMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt32Mem dst (transferFromFromBalanceHashMem src dst caller allowance)

noncomputable def transferFromToBalanceHashMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (transferFromToBalanceKeyMem src dst caller allowance)

noncomputable def transferFromAllowanceInnerScratchMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt0Mem ⟨1⟩ (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance))

noncomputable def transferFromAllowanceScratchMem
    (src dst caller allowance : UInt256) : ByteArray :=
  wordAt0Mem (transferFromAllowanceInnerSlotWord src dst)
    (wordAt32Mem caller (transferFromAllowanceInnerScratchMem src dst caller allowance))

noncomputable def transferFromAllowanceInnerSlotI (I : ExecutionEnv) : UInt256 :=
  transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I)

noncomputable def transferFromAllowanceInnerScratchMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromAllowanceInnerScratchMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromAllowanceScratchMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromAllowanceScratchMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromFromBalanceKeyMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromFromBalanceKeyMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromFromBalanceHashMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromFromBalanceHashMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromAfterFromLoadMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem ⟨0⟩ (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))

noncomputable def transferFromToBalanceKeyMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromToBalanceKeyMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromToBalanceHashMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  transferFromToBalanceHashMem
    (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
    (transferFromCurrentAllowanceRaw σ I)

noncomputable def transferFromAfterToLoadMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem ⟨0⟩ (wordAt32Mem (transferFromToWord I) (transferFromAfterFromLoadMemI σ I))

noncomputable def transferFromAllowanceDebitI
    (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : Sat256) : UInt256 :=
  transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I

noncomputable def transferFromLogMem
    (src dst caller allowance val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0
    (transferFromToBalanceHashMem src dst caller allowance) 160 32

noncomputable def transferFromReturnMem
    (src dst caller allowance val : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (transferFromLogMem src dst caller allowance val) 160 32

theorem transferFromFromArgMem_size (src : UInt256) :
    (transferFromFromArgMem src).size = 96 := by
  unfold transferFromFromArgMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferFromDispatchMem_size]; omega)
      (by rw [transferFromDispatchMem_size]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, transferFromDispatchMem_size,
    ByteArray_zeroes_size,
    toByteArray_size]

theorem transferFromArgsMem_size (src dst : UInt256) :
    (transferFromArgsMem src dst).size = 128 := by
  unfold transferFromArgsMem
  simpa [transferFromFromArgMem_size] using
    write_end_size_from (UInt256.toByteArray dst) (transferFromFromArgMem src) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem transferFromAllowanceInnerKeyMem_size (src dst : UInt256) :
    (transferFromAllowanceInnerKeyMem src dst).size = 128 := by
  unfold transferFromAllowanceInnerKeyMem
  change ((UInt256.toByteArray src).write 0 (transferFromArgsMem src dst) 32 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromArgsMem_size src dst]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferFromArgsMem_size,
    toByteArray_size]
  norm_num

theorem transferFromAllowanceInnerHashMem_size (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).size = 128 := by
  unfold transferFromAllowanceInnerHashMem
  change ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (transferFromAllowanceInnerKeyMem src dst) 0 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerKeyMem_size src dst]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferFromAllowanceInnerKeyMem_size,
    toByteArray_size]
  norm_num

theorem transferFromAllowanceOuterKeyMem_size (src dst caller : UInt256) :
    (transferFromAllowanceOuterKeyMem src dst caller).size = 128 := by
  unfold transferFromAllowanceOuterKeyMem
  change ((UInt256.toByteArray caller).write 0
    (transferFromAllowanceInnerHashMem src dst) 32 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferFromAllowanceInnerHashMem_size,
    toByteArray_size]
  norm_num

theorem transferFromAllowanceOuterHashMem_size (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).size = 128 := by
  unfold transferFromAllowanceOuterHashMem
  change ((UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst)).write 0
    (transferFromAllowanceOuterKeyMem src dst caller) 0 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferFromAllowanceOuterKeyMem_size,
    toByteArray_size]
  norm_num

theorem transferFromAllowanceMem_size (src dst caller allowance : UInt256) :
    (transferFromAllowanceMem src dst caller allowance).size = 160 := by
  unfold transferFromAllowanceMem
  simpa [transferFromAllowanceOuterHashMem_size] using
    write_end_size_from (UInt256.toByteArray allowance)
      (transferFromAllowanceOuterHashMem src dst caller) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem transferFromFromBalanceKeyMem_size (src dst caller allowance : UInt256) :
    (transferFromFromBalanceKeyMem src dst caller allowance).size = 160 := by
  unfold transferFromFromBalanceKeyMem wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromAllowanceMem_size, toByteArray_size]
  omega

theorem transferFromFromBalanceHashMem_size (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).size = 160 := by
  unfold transferFromFromBalanceHashMem wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromFromBalanceKeyMem_size, toByteArray_size]
  omega

theorem transferFromToBalanceKeyMem_size (src dst caller allowance : UInt256) :
    (transferFromToBalanceKeyMem src dst caller allowance).size = 160 := by
  unfold transferFromToBalanceKeyMem wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromFromBalanceHashMem_size, toByteArray_size]
  omega

theorem transferFromAllowanceInnerScratchMem_size
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceInnerScratchMem src dst caller allowance).size = 160 := by
  have hinner :
      (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromFromBalanceHashMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceInnerScratchMem wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [hinner]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    hinner, toByteArray_size]
  omega

theorem transferFromAllowanceScratchMem_size
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceScratchMem src dst caller allowance).size = 160 := by
  have hinner :
      (wordAt32Mem caller
        (transferFromAllowanceInnerScratchMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromAllowanceInnerScratchMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceScratchMem wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [hinner]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    hinner, toByteArray_size]
  omega

theorem transferFromAfterFromLoadInnerMem_size
    (src dst caller allowance : UInt256) :
    (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance)).size = 160 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromAllowanceScratchMem_size, toByteArray_size]
  omega

theorem transferFromAfterFromLoadMem_size
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).size =
      160 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromAfterFromLoadInnerMem_size, toByteArray_size]
  omega

theorem transferFromToBalanceHashMem_size (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).size = 160 := by
  unfold transferFromToBalanceHashMem wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromToBalanceKeyMem_size, toByteArray_size]
  omega

theorem transferFromLogMem_size (src dst caller allowance val : UInt256) :
    (transferFromLogMem src dst caller allowance val).size = 192 := by
  unfold transferFromLogMem
  simpa [transferFromToBalanceHashMem_size] using
    write_end_size_from (UInt256.toByteArray val)
      (transferFromToBalanceHashMem src dst caller allowance) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem transferFromFromArgMem_read64 (src : UInt256) :
    (transferFromFromArgMem src).readWithPadding 64 32 = UInt256.toByteArray src := by
  unfold transferFromFromArgMem
  exact toByteArray_write_read_back_of_gap src transferFromDispatchMem 64
    (by rw [transferFromDispatchMem_size]; exact lt_usize 32 (by norm_num))

theorem transferFromArgsMem_read64 (src dst : UInt256) :
    (transferFromArgsMem src dst).readWithPadding 64 32 = UInt256.toByteArray src := by
  unfold transferFromArgsMem
  rw [write32_read_below _ _ 96 64 (by rw [toByteArray_size])
      (by rw [transferFromFromArgMem_size src]) (by omega)]
  exact transferFromFromArgMem_read64 src

theorem transferFromArgsMem_read96 (src dst : UInt256) :
    (transferFromArgsMem src dst).readWithPadding 96 32 = UInt256.toByteArray dst := by
  unfold transferFromArgsMem
  exact toByteArray_write_read_back_of_gap dst (transferFromFromArgMem src) 96
    (by rw [transferFromFromArgMem_size]; exact lt_usize 0 (by norm_num))

theorem transferFromAllowanceInnerKeyMem_write (src dst : UInt256) :
    (UInt256.toByteArray src).write 0 (transferFromArgsMem src dst) 32 32 =
      transferFromAllowanceInnerKeyMem src dst := by
  rfl

theorem transferFromAllowanceInnerKeyMem_read32 (src dst : UInt256) :
    (transferFromAllowanceInnerKeyMem src dst).readWithPadding 32 32 = UInt256.toByteArray src := by
  unfold transferFromAllowanceInnerKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromArgsMem_size src dst]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray src).size ≤ 32
    rw [toByteArray_size])

theorem transferFromAllowanceInnerKeyMem_read96 (src dst : UInt256) :
    (transferFromAllowanceInnerKeyMem src dst).readWithPadding 96 32 = UInt256.toByteArray dst := by
  unfold transferFromAllowanceInnerKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
      (by rw [transferFromArgsMem_size src dst]; omega)
      (by omega)
      (by rw [transferFromArgsMem_size src dst])]
  exact transferFromArgsMem_read96 src dst

theorem transferFromAllowanceInnerHashMem_read0 (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).readWithPadding 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferFromAllowanceInnerHashMem
  exact wordAt0Mem_read0 ⟨1⟩ (transferFromAllowanceInnerKeyMem src dst)

theorem transferFromAllowanceInnerHashMem_write (src dst : UInt256) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
        (transferFromAllowanceInnerKeyMem src dst) 0 32 =
      transferFromAllowanceInnerHashMem src dst := by
  rfl

theorem transferFromAllowanceInnerHashMem_read32 (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).readWithPadding 32 32 =
      UInt256.toByteArray src := by
  unfold transferFromAllowanceInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerKeyMem_size src dst]; omega)
    (by omega)
    (by rw [transferFromAllowanceInnerKeyMem_size src dst]; omega)]
  exact transferFromAllowanceInnerKeyMem_read32 src dst

theorem transferFromAllowanceInnerHashMem_read64 (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold transferFromAllowanceInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerKeyMem_size src dst]; omega)
    (by omega)
    (by rw [transferFromAllowanceInnerKeyMem_size src dst]; norm_num)]
  unfold transferFromAllowanceInnerKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromArgsMem_size src dst]; omega)
    (by norm_num)
    (by rw [transferFromArgsMem_size src dst]; norm_num)]
  exact transferFromArgsMem_read64 src dst

theorem transferFromAllowanceInnerHashMem_read96 (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold transferFromAllowanceInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerKeyMem_size src dst]; omega)
    (by omega)
    (by rw [transferFromAllowanceInnerKeyMem_size src dst])]
  exact transferFromAllowanceInnerKeyMem_read96 src dst

theorem transferFromAllowanceInnerHashMem_read0_64 (src dst : UInt256) :
    (transferFromAllowanceInnerHashMem src dst).readWithPadding 0 64 =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++ UInt256.toByteArray src := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega)]
  have hleft :
      (transferFromAllowanceInnerHashMem src dst).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega),
      transferFromAllowanceInnerHashMem_read0 src dst]
  have hright :
      (transferFromAllowanceInnerHashMem src dst).extract 32 64 =
        UInt256.toByteArray src := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega),
      transferFromAllowanceInnerHashMem_read32 src dst]
  rw [show (transferFromAllowanceInnerHashMem src dst).extract 0 64 =
      (transferFromAllowanceInnerHashMem src dst).extract 0 32 ++
        (transferFromAllowanceInnerHashMem src dst).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromAllowanceInnerKeccakSlot (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I) =
      erc20AllowanceOwnerSlot
        (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)) := by
  unfold transferFromAllowanceInnerSlotWord
  rw [transferFromAllowanceInnerHashMem_read0_64]
  unfold erc20AllowanceOwnerSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonFrom]
  exact keccakSlot_eq _

theorem transferFromAllowanceOuterKeyMem_read32 (src dst caller : UInt256) :
    (transferFromAllowanceOuterKeyMem src dst caller).readWithPadding 32 32 =
      UInt256.toByteArray caller := by
  unfold transferFromAllowanceOuterKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray caller).size ≤ 32
    rw [toByteArray_size])

theorem transferFromAllowanceOuterHashMem_read0 (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).readWithPadding 0 32 =
      UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst) := by
  unfold transferFromAllowanceOuterHashMem
  exact wordAt0Mem_read0 (transferFromAllowanceInnerSlotWord src dst)
    (transferFromAllowanceOuterKeyMem src dst caller)

theorem transferFromAllowanceOuterHashMem_read32 (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).readWithPadding 32 32 =
      UInt256.toByteArray caller := by
  unfold transferFromAllowanceOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; omega)
    (by omega)
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; omega)]
  exact transferFromAllowanceOuterKeyMem_read32 src dst caller

theorem transferFromAllowanceOuterHashMem_read64 (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold transferFromAllowanceOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; omega)
    (by omega)
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; norm_num)]
  unfold transferFromAllowanceOuterKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceInnerHashMem_size src dst]; norm_num)]
  exact transferFromAllowanceInnerHashMem_read64 src dst

theorem transferFromAllowanceOuterHashMem_read96 (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold transferFromAllowanceOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller]; omega)
    (by omega)
    (by rw [transferFromAllowanceOuterKeyMem_size src dst caller])]
  unfold transferFromAllowanceOuterKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerHashMem_size src dst]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceInnerHashMem_size src dst])]
  exact transferFromAllowanceInnerHashMem_read96 src dst

theorem transferFromAllowanceOuterHashMem_read0_64 (src dst caller : UInt256) :
    (transferFromAllowanceOuterHashMem src dst caller).readWithPadding 0 64 =
      UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst) ++
        UInt256.toByteArray caller := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAllowanceOuterHashMem_size src dst caller]; omega)]
  have hleft :
      (transferFromAllowanceOuterHashMem src dst caller).extract 0 32 =
        UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAllowanceOuterHashMem_size src dst caller]; omega),
      transferFromAllowanceOuterHashMem_read0 src dst caller]
  have hright :
      (transferFromAllowanceOuterHashMem src dst caller).extract 32 64 =
        UInt256.toByteArray caller := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAllowanceOuterHashMem_size src dst caller]; omega),
      transferFromAllowanceOuterHashMem_read32 src dst caller]
  rw [show (transferFromAllowanceOuterHashMem src dst caller).extract 0 64 =
      (transferFromAllowanceOuterHashMem src dst caller).extract 0 32 ++
        (transferFromAllowanceOuterHashMem src dst caller).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromAllowanceOuterKeccakSlot (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferFromAllowanceOuterHashMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I))
          |>.readWithPadding 0 64))) =
      transferFromAllowanceSlotI I := by
  rw [transferFromAllowanceOuterHashMem_read0_64,
    transferFromAllowanceInnerKeccakSlot I hcanonFrom]
  unfold transferFromAllowanceSlotI erc20AllowanceSlot erc20AllowanceOwnerSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonFrom,
    keyValueToWord_address]
  exact keccakSlot_eq _

theorem transferFromAllowanceMem_read64 (src dst caller allowance : UInt256) :
    (transferFromAllowanceMem src dst caller allowance).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold transferFromAllowanceMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceOuterHashMem_size src dst caller]) (by omega)]
  exact transferFromAllowanceOuterHashMem_read64 src dst caller

theorem transferFromAllowanceMem_read96 (src dst caller allowance : UInt256) :
    (transferFromAllowanceMem src dst caller allowance).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold transferFromAllowanceMem
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceOuterHashMem_size src dst caller]) (by omega)]
  exact transferFromAllowanceOuterHashMem_read96 src dst caller

theorem transferFromAllowanceMem_read128 (src dst caller allowance : UInt256) :
    (transferFromAllowanceMem src dst caller allowance).readWithPadding 128 32 =
      UInt256.toByteArray allowance := by
  unfold transferFromAllowanceMem
  exact toByteArray_write_read_back_of_gap allowance
    (transferFromAllowanceOuterHashMem src dst caller) 128
    (by rw [transferFromAllowanceOuterHashMem_size]; exact lt_usize 0 (by norm_num))

theorem transferFromFromBalanceKeyMem_read32 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceKeyMem src dst caller allowance).readWithPadding 32 32 =
      UInt256.toByteArray src := by
  unfold transferFromFromBalanceKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray src).size ≤ 32
    rw [toByteArray_size])

theorem transferFromFromBalanceHashMem_read0 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferFromFromBalanceHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (transferFromFromBalanceKeyMem src dst caller allowance)

theorem transferFromFromBalanceHashMem_read32 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 32 32 =
      UInt256.toByteArray src := by
  unfold transferFromFromBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega)]
  exact transferFromFromBalanceKeyMem_read32 src dst caller allowance

theorem transferFromFromBalanceHashMem_read64 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold transferFromFromBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; norm_num)]
  unfold transferFromFromBalanceKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; norm_num)]
  exact transferFromAllowanceMem_read64 src dst caller allowance

theorem transferFromFromBalanceHashMem_read96 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold transferFromFromBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; norm_num)]
  unfold transferFromFromBalanceKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; norm_num)]
  exact transferFromAllowanceMem_read96 src dst caller allowance

theorem transferFromFromBalanceHashMem_read128 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 128 32 =
      UInt256.toByteArray allowance := by
  unfold transferFromFromBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 128 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromFromBalanceKeyMem_size src dst caller allowance])]
  unfold transferFromFromBalanceKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 128 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAllowanceMem_size src dst caller allowance])]
  exact transferFromAllowanceMem_read128 src dst caller allowance

theorem transferFromFromBalanceHashMem_read0_64 (src dst caller allowance : UInt256) :
    (transferFromFromBalanceHashMem src dst caller allowance).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray src := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)]
  have hleft :
      (transferFromFromBalanceHashMem src dst caller allowance).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
      transferFromFromBalanceHashMem_read0 src dst caller allowance]
  have hright :
      (transferFromFromBalanceHashMem src dst caller allowance).extract 32 64 =
        UInt256.toByteArray src := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
      transferFromFromBalanceHashMem_read32 src dst caller allowance]
  rw [show (transferFromFromBalanceHashMem src dst caller allowance).extract 0 64 =
      (transferFromFromBalanceHashMem src dst caller allowance).extract 0 32 ++
        (transferFromFromBalanceHashMem src dst caller allowance).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromAllowanceInnerScratchMem_read0_64
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceInnerScratchMem src dst caller allowance).readWithPadding 0 64 =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++ UInt256.toByteArray src := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)]
  have hleft :
      (transferFromAllowanceInnerScratchMem src dst caller allowance).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)]
    unfold transferFromAllowanceInnerScratchMem
    exact wordAt0Mem_read0 ⟨1⟩
      (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance))
  have hright :
      (transferFromAllowanceInnerScratchMem src dst caller allowance).extract 32 64 =
        UInt256.toByteArray src := by
    have hsize32 :
        (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance)).size = 160 := by
      unfold wordAt32Mem
      rw [write32_eq _ _ _ (by rw [toByteArray_size])
        (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        transferFromFromBalanceHashMem_size, toByteArray_size]
      omega
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)]
    unfold transferFromAllowanceInnerScratchMem wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [hsize32]; omega)
      (by omega)
      (by rw [hsize32]; omega)]
    unfold wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray src).size ≤ 32
      rw [toByteArray_size])
  rw [show (transferFromAllowanceInnerScratchMem src dst caller allowance).extract 0 64 =
      (transferFromAllowanceInnerScratchMem src dst caller allowance).extract 0 32 ++
        (transferFromAllowanceInnerScratchMem src dst caller allowance).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num,
    hleft, hright]

theorem transferFromAllowanceInnerScratchMem_read64
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceInnerScratchMem src dst caller allowance).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  have hsize32 :
      (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromFromBalanceHashMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceInnerScratchMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hsize32]; omega)
    (by omega)
    (by rw [hsize32]; omega)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; norm_num)]
  exact transferFromFromBalanceHashMem_read64 src dst caller allowance

theorem transferFromAllowanceScratchMem_read32
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceScratchMem src dst caller allowance).readWithPadding 32 32 =
      UInt256.toByteArray caller := by
  have hsize32 :
      (wordAt32Mem caller
        (transferFromAllowanceInnerScratchMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromAllowanceInnerScratchMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceScratchMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [hsize32]; omega)
    (by omega)
    (by rw [hsize32]; omega)]
  unfold wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray caller).size ≤ 32
    rw [toByteArray_size])

theorem transferFromAllowanceScratchMem_read64
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceScratchMem src dst caller allowance).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  have hsize32 :
      (wordAt32Mem caller
        (transferFromAllowanceInnerScratchMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromAllowanceInnerScratchMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceScratchMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hsize32]; omega)
    (by omega)
    (by rw [hsize32]; omega)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; norm_num)]
  exact transferFromAllowanceInnerScratchMem_read64 src dst caller allowance

theorem transferFromAllowanceScratchMem_read96
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceScratchMem src dst caller allowance).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  have hsize32 :
      (wordAt32Mem caller
        (transferFromAllowanceInnerScratchMem src dst caller allowance)).size = 160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      transferFromAllowanceInnerScratchMem_size, toByteArray_size]
    omega
  unfold transferFromAllowanceScratchMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [hsize32]; omega)
    (by omega)
    (by rw [hsize32]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceInnerScratchMem_size src dst caller allowance]; norm_num)]
  unfold transferFromAllowanceInnerScratchMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [show (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance)).size = 160 by
      unfold wordAt32Mem
      rw [write32_eq _ _ _ (by rw [toByteArray_size])
        (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        transferFromFromBalanceHashMem_size, toByteArray_size]
      omega]; omega)
    (by omega)
    (by rw [show (wordAt32Mem src (transferFromFromBalanceHashMem src dst caller allowance)).size = 160 by
      unfold wordAt32Mem
      rw [write32_eq _ _ _ (by rw [toByteArray_size])
        (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        transferFromFromBalanceHashMem_size, toByteArray_size]
      omega]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; norm_num)]
  exact transferFromFromBalanceHashMem_read96 src dst caller allowance

theorem transferFromAllowanceScratchMem_read0_64
    (src dst caller allowance : UInt256) :
    (transferFromAllowanceScratchMem src dst caller allowance).readWithPadding 0 64 =
      UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst) ++
        UInt256.toByteArray caller := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega)]
  have hleft :
      (transferFromAllowanceScratchMem src dst caller allowance).extract 0 32 =
        UInt256.toByteArray (transferFromAllowanceInnerSlotWord src dst) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega)]
    unfold transferFromAllowanceScratchMem
    exact wordAt0Mem_read0 (transferFromAllowanceInnerSlotWord src dst)
      (wordAt32Mem caller (transferFromAllowanceInnerScratchMem src dst caller allowance))
  have hright :
      (transferFromAllowanceScratchMem src dst caller allowance).extract 32 64 =
        UInt256.toByteArray caller := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega),
      transferFromAllowanceScratchMem_read32 src dst caller allowance]
  rw [show (transferFromAllowanceScratchMem src dst caller allowance).extract 0 64 =
      (transferFromAllowanceScratchMem src dst caller allowance).extract 0 32 ++
        (transferFromAllowanceScratchMem src dst caller allowance).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num,
    hleft, hright]

theorem transferFromAfterFromLoadMem_read32
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).readWithPadding 32 32 =
      UInt256.toByteArray src := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; omega)]
  unfold wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray src).size ≤ 32
    rw [toByteArray_size])

theorem transferFromAfterFromLoadMem_read64
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; norm_num)]
  exact transferFromAllowanceScratchMem_read64 src dst caller allowance

theorem transferFromAfterFromLoadMem_read96
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterFromLoadInnerMem_size src dst caller allowance]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAllowanceScratchMem_size src dst caller allowance]; norm_num)]
  exact transferFromAllowanceScratchMem_read96 src dst caller allowance

theorem transferFromAfterFromLoadMem_read0_64
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray src := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAfterFromLoadMem_size src dst caller allowance]; omega)]
  have hleft :
      (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAfterFromLoadMem_size src dst caller allowance]; omega)]
    exact wordAt0Mem_read0 ⟨0⟩
      (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))
  have hright :
      (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).extract 32 64 =
        UInt256.toByteArray src := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAfterFromLoadMem_size src dst caller allowance]; omega),
      transferFromAfterFromLoadMem_read32 src dst caller allowance]
  rw [show (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).extract 0 64 =
      (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).extract 0 32 ++
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromAfterToLoadMem_size
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).size =
      160 := by
  have hmid :
      (wordAt0Mem ⟨0⟩
        (src.toByteArray.write 0 (transferFromAllowanceScratchMem src dst caller allowance) 32 32)).size =
        160 := by
    simpa [wordAt32Mem] using transferFromAfterFromLoadMem_size src dst caller allowance
  have hinner :
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance)))).size =
        160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [hmid]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      hmid, toByteArray_size]
    omega
  have hinner' :
      (wordAt32Mem dst
        ((⟨0⟩ : UInt256).toByteArray.write 0
          (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance)) 0 32)).size =
        160 := by
    simpa [wordAt0Mem] using hinner
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [hinner']; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    hinner', toByteArray_size]
  omega

theorem transferFromAfterFromLoadMem_unfold_size
    (src dst caller allowance : UInt256) :
    (((⟨0⟩ : UInt256).toByteArray.write 0
      (src.toByteArray.write 0 (transferFromAllowanceScratchMem src dst caller allowance) 32 32) 0 32).size) =
      160 := by
  simpa [wordAt0Mem, wordAt32Mem] using transferFromAfterFromLoadMem_size src dst caller allowance

theorem transferFromAfterToLoadInnerMem_size
    (src dst caller allowance : UInt256) :
    (wordAt32Mem dst
      (((⟨0⟩ : UInt256).toByteArray.write 0
        (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance)) 0 32))).size =
      160 := by
  have hmid :
      (wordAt0Mem ⟨0⟩
        (src.toByteArray.write 0 (transferFromAllowanceScratchMem src dst caller allowance) 32 32)).size =
        160 := by
    simpa [wordAt32Mem] using transferFromAfterFromLoadMem_size src dst caller allowance
  have hinner :
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance)))).size =
        160 := by
    unfold wordAt32Mem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [hmid]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      hmid, toByteArray_size]
    omega
  simpa [wordAt0Mem] using hinner

theorem transferFromAfterToLoadMem_read32
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).readWithPadding 32 32 =
      UInt256.toByteArray dst := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; omega)]
  unfold wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadMem_unfold_size src dst caller allowance]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray dst).size ≤ 32
    rw [toByteArray_size])

theorem transferFromAfterToLoadMem_read0_64
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray dst := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromAfterToLoadMem_size src dst caller allowance]; omega)]
  have hleft :
      (wordAt0Mem ⟨0⟩
        (wordAt32Mem dst
          (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromAfterToLoadMem_size src dst caller allowance]; omega)]
    exact wordAt0Mem_read0 ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))
  have hright :
      (wordAt0Mem ⟨0⟩
        (wordAt32Mem dst
          (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).extract 32 64 =
        UInt256.toByteArray dst := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromAfterToLoadMem_size src dst caller allowance]; omega),
      transferFromAfterToLoadMem_read32 src dst caller allowance]
  rw [show (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).extract 0 64 =
      (wordAt0Mem ⟨0⟩
        (wordAt32Mem dst
          (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).extract 0 32 ++
        (wordAt0Mem ⟨0⟩
          (wordAt32Mem dst
            (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromAfterToLoadMem_read64
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadMem_unfold_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAfterFromLoadMem_unfold_size src dst caller allowance]; norm_num)]
  exact transferFromAfterFromLoadMem_read64 src dst caller allowance

theorem transferFromAfterToLoadMem_read96
    (src dst caller allowance : UInt256) :
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem dst
        (wordAt0Mem ⟨0⟩ (wordAt32Mem src (transferFromAllowanceScratchMem src dst caller allowance))))).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromAfterToLoadInnerMem_size src dst caller allowance]; norm_num)]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromAfterFromLoadMem_unfold_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromAfterFromLoadMem_unfold_size src dst caller allowance]; norm_num)]
  exact transferFromAfterFromLoadMem_read96 src dst caller allowance

theorem transferFromFromBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (allowance : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferFromFromBalanceHashMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I) allowance)
          |>.readWithPadding 0 64))) =
      transferFromFromSlot I := by
  rw [transferFromFromBalanceHashMem_read0_64]
  unfold transferFromFromSlot erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonFrom]
  exact keccakSlot_eq _

theorem transferFromToBalanceKeyMem_read32 (src dst caller allowance : UInt256) :
    (transferFromToBalanceKeyMem src dst caller allowance).readWithPadding 32 32 =
      UInt256.toByteArray dst := by
  unfold transferFromToBalanceKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray dst).size ≤ 32
    rw [toByteArray_size])

theorem transferFromToBalanceHashMem_read0 (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferFromToBalanceHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (transferFromToBalanceKeyMem src dst caller allowance)

theorem transferFromToBalanceHashMem_read32 (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).readWithPadding 32 32 =
      UInt256.toByteArray dst := by
  unfold transferFromToBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; omega)]
  exact transferFromToBalanceKeyMem_read32 src dst caller allowance

theorem transferFromToBalanceHashMem_read64 (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).readWithPadding 64 32 =
      UInt256.toByteArray src := by
  unfold transferFromToBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; norm_num)]
  unfold transferFromToBalanceKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; norm_num)]
  exact transferFromFromBalanceHashMem_read64 src dst caller allowance

theorem transferFromToBalanceHashMem_read96 (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).readWithPadding 96 32 =
      UInt256.toByteArray dst := by
  unfold transferFromToBalanceHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; omega)
    (by omega)
    (by rw [transferFromToBalanceKeyMem_size src dst caller allowance]; norm_num)]
  unfold transferFromToBalanceKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; omega)
    (by norm_num)
    (by rw [transferFromFromBalanceHashMem_size src dst caller allowance]; norm_num)]
  exact transferFromFromBalanceHashMem_read96 src dst caller allowance

theorem transferFromToBalanceHashMem_read0_64 (src dst caller allowance : UInt256) :
    (transferFromToBalanceHashMem src dst caller allowance).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray dst := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferFromToBalanceHashMem_size src dst caller allowance]; omega)]
  have hleft :
      (transferFromToBalanceHashMem src dst caller allowance).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferFromToBalanceHashMem_size src dst caller allowance]; omega),
      transferFromToBalanceHashMem_read0 src dst caller allowance]
  have hright :
      (transferFromToBalanceHashMem src dst caller allowance).extract 32 64 =
        UInt256.toByteArray dst := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferFromToBalanceHashMem_size src dst caller allowance]; omega),
      transferFromToBalanceHashMem_read32 src dst caller allowance]
  rw [show (transferFromToBalanceHashMem src dst caller allowance).extract 0 64 =
      (transferFromToBalanceHashMem src dst caller allowance).extract 0 32 ++
        (transferFromToBalanceHashMem src dst caller allowance).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferFromToBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (allowance : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferFromToBalanceHashMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I) allowance)
          |>.readWithPadding 0 64))) =
      transferFromToSlot I := by
  rw [transferFromToBalanceHashMem_read0_64]
  unfold transferFromToSlot erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonTo]
  exact keccakSlot_eq _

theorem transferFromLogMem_read160 (src dst caller allowance val : UInt256) :
    (transferFromLogMem src dst caller allowance val).readWithPadding 160 32 =
      UInt256.toByteArray val := by
  unfold transferFromLogMem
  exact toByteArray_write_read_back_of_gap val
    (transferFromToBalanceHashMem src dst caller allowance) 160
    (by rw [transferFromToBalanceHashMem_size]; exact lt_usize 0 (by norm_num))

theorem transferFromReturnMem_read160 (src dst caller allowance val : UInt256) :
    (transferFromReturnMem src dst caller allowance val).readWithPadding 160 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferFromReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromLogMem_size src dst caller allowance val]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])



theorem transferFromDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ transferFromDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (transferFromDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨331⟩ : UInt256) := by
  decide +native

theorem erc20TransferFromSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem transferFromSelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      transferFromSelectorWord := by
  have h := evmSelectorDecode hsz 0x23 0xb8 0x72 0xdd transferFromSelectorWord (by decide +native)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      transferFromSelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem erc20X_transferFromReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz := erc20TransferFromSelector_size hsel
  have hword := transferFromSelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, transferFromSelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 transferFromDispatchMem (UInt256.ofNat 1)
    (by decide +native) mem_cost (by decide +native) (by decide) (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨331⟩ (UInt256.ofNat 1)
      (by decide +native)
      mem_cost
      transferFromDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by decide +native) (by decide +native) (by evm_ov)⟩

theorem erc20TransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd331⟩ := hreach
  have hsizeGuard := calldataSizeGuardShort (n := I.calldata.size) (m := 100)
    hsize (by norm_num [UInt256.size]) hshort
  have hsizeGuard100 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨100⟩ = ⟨1⟩ := by
    simpa using hsizeGuard
  have rd801 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by vyper_erc20_transferFrom_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨100⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by rw [hwv, hsizeGuard100]; decide) (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by norm_num)

theorem erc20TransferFromX_noncanon_from {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd331⟩ := hreach
  have hsizeGuard := calldataSizeGuardOk (n := I.calldata.size) (m := 100) hsz100 hsize
  have hsizeGuard100 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨100⟩ = ⟨0⟩ := by
    simpa using hsizeGuard
  have hcanonGuard : UInt256.shiftRight (transferFromFromWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (transferFromFromWord I) hzero)
  have rd801 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by vyper_erc20_transferFrom_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨100⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard100]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiT (by
      simp [transferFromFromWord, calldataWord]
      exact hcanonGuard) (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)

theorem erc20TransferFromX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd331⟩ := hreach
  have hsizeGuard := calldataSizeGuardOk (n := I.calldata.size) (m := 100) hsz100 hsize
  have hsizeGuard100 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨100⟩ = ⟨0⟩ := by
    simpa using hsizeGuard
  have hcanonFromGuard : UInt256.shiftRight (transferFromFromWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (transferFromFromWord I) hcanonFrom
  have hcanonToGuard : UInt256.shiftRight (transferFromToWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (transferFromToWord I) hzero)
  have rd801 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by vyper_erc20_transferFrom_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨100⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard100]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromFromWord, calldataWord] using hcanonFromGuard),
    push1 ⟨64⟩,
    raw mstore 6
      ((UInt256.toByteArray (transferFromFromWord I)).write 0 transferFromDispatchMem 64 32)
      (UInt256.ofNat 3)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨36⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiT (by
      simp [transferFromToWord, calldataWord]
      exact hcanonToGuard) (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)


end VyperERC20
