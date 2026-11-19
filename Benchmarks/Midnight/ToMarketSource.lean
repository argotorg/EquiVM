import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.InternalCall
import Reasoning.ExternalCall
import Benchmarks.Midnight.CodeStorage

/-! Value-level evaluation of the stored-market getter and its explicit size guards. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the full-width bytes-to-integer cast used by code-storage addresses.
theorem evalBytes32ToUint {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {word : UInt256}
    (h : evalExpr? cfg frame evm expr = .ok (wordBytes32Value word)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (uint256Value word) := by
  simp only [evalExpr?, h, bind, EvalResult.bind, castValue?, wordBytes32Value,
    abiBytes32Width, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    word_toBytesBE_length_32, Nat.reduceAdd, Nat.reduceMul, if_true,
    fromBytesBE_word, EvalResult.ofOption, decide_true, uint256Value]

theorem evalUint160ToAddress {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {word : UInt256}
    (h : evalExpr? cfg frame evm expr = .ok (uint256Value word)) :
    evalExpr? cfg frame evm
      (.cast (.cast expr (.elem (.int (.uint ⟨160, by decide⟩)))) (.elem .address)) =
      .ok (.address (AccountAddress.ofUInt256 word)) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExpr?, h, uint256Value, castValue?, normalizeInt, EVM.twoPow,
    AccountAddress.ofNat, Fin.ofNat, AccountAddress.size,
    EvalResult.bind, bind, EvalResult.ofOption]
  change (match if (Int.ofNat word.toNat % Int.ofNat (2 ^ 160)) < 0 then none else
    some (Value.address (AccountAddress.ofNat
      (Int.ofNat word.toNat % Int.ofNat (2 ^ 160)).toNat)) with
      | some a => EvalResult.ok a
      | none => EvalResult.error .typeError) = _
  simp only [Int.ofNat_eq_natCast]
  rw [← Int.natCast_mod]
  rw [if_neg (by omega)]
  simp only [Int.toNat_natCast]
  congr 2
  apply Fin.ext
  change (word.toNat % 2 ^ 160) % 2 ^ 160 = word.toNat % 2 ^ 160
  exact Nat.mod_mod _ _

def toMarketArguments (id : UInt256) : Store := (∅ : Store).insert "id" (wordBytes32Value id)

def toMarketFrame (evm : State) (id : UInt256) : Frame :=
  calldataFrame contract (toMarketArguments id) ∅ evm

def toMarketAddressExpr : Expr :=
  .cast (.cast (.cast (.var "id") (.elem (.int (.uint ⟨256, by decide⟩))))
    (.elem (.int (.uint ⟨160, by decide⟩)))) (.elem .address)

def toMarketAddressFrame (evm : State) (id : UInt256) : Frame :=
  { toMarketFrame evm id with
    locals := (toMarketFrame evm id).locals.insert "create2Address"
      (.address (AccountAddress.ofUInt256 id)) }

def toMarketCodeGuard : Expr :=
  .binary .le (.extCodeSize (.var "create2Address")) (.intLit 18446744073709550464)

def toMarketTickGuard : Expr := .binary .gt
  (.storage { base := "marketState", steps := [.mindex (.var "id"), .field "tickSpacing"] }) (.intLit 0)

def toMarketCapacityExpr : Expr :=
  .binary .lt
    (.binary .add
      (.binary .add
        (.binary .mul (.binary .div (.binary .add (.arrayLength .localVar ⟨"code", []⟩) (.intLit 31))
          (.intLit 32)) (.intLit 32))
        (.binary .mul (.intLit 160) (.arrayLength .localVar ⟨"collaterals", []⟩))) (.intLit 1408))
    (.intLit 18446744073709551616)

theorem toMarketBody_shape : toMarketTransition.body = entryPrefix ++
    [.require toMarketTickGuard,
     .letDecl "create2Address" (some (.elem .address)) toMarketAddressExpr,
     .require toMarketCodeGuard,
     .letDecl "code" (some .bytes)
       (.extCodePrefix (.var "create2Address") (.extCodeSize (.var "create2Address"))),
     .letDecl "decoded" none (.abiDecode Model.marketABI (.var "code")),
     .letDecl "collaterals" none (.tupleGet (.var "decoded") 3),
     .require toMarketCapacityExpr, .return [.var "decoded"]] := rfl

theorem toMarketIdGet (evm : State) (id : UInt256) :
    (toMarketFrame evm id).locals.get? "id" = some (wordBytes32Value id) := by
  simp only [toMarketFrame, calldataFrame, toMarketArguments]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem toMarketAddressEval (evm : State) (id : UInt256) :
    evalExpr? config (toMarketFrame evm id) evm toMarketAddressExpr =
      .ok (.address (AccountAddress.ofUInt256 id)) := by
  apply evalUint160ToAddress
  apply evalBytes32ToUint
  simp only [evalExpr?, toMarketIdGet, EvalResult.ofOption]

theorem toMarketTickEval (evm : State) (id : UInt256) :
    evalExpr? config (toMarketFrame evm id) evm toMarketTickGuard =
      .ok (.bool (decide (0 < (marketTickSpacing (marketFeeWord evm id)).toNat))) := by
  have hr : evalExpr? config (toMarketFrame evm id) evm
      (.storage { base := "marketState", steps := [.mindex (.var "id"), .field "tickSpacing"] }) =
      .ok (.int (marketTickSpacing (marketFeeWord evm id)).toNat) := by
    apply evalBytes32MappingField (t := .int (.uint ⟨8, by decide⟩))
      (loc := {
        slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩, offset := 18, size := 1,
        hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }) evm id
      rfl rfl ?_ (storageLocLoad_uint8_offset18 evm _) (by decide) (by decide) (by decide)
    change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩,
      offset := 18, size := 1, hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  rw [toMarketTickGuard, evalExpr_binary_nonshort (by decide) (by decide), hr]
  simp [evalExpr?, evalBinaryOp?, bind, pure, EvalResult.bind]

theorem toMarketCodeGuardEval (evm : State) (id : UInt256) :
    evalExpr? config (toMarketAddressFrame evm id) evm toMarketCodeGuard =
      .ok (.bool (decide ((extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464))) := by
  have hr : evalExpr? config (toMarketAddressFrame evm id) evm (.var "create2Address") =
      .ok (.address (AccountAddress.ofUInt256 id)) := by
    simp only [evalExpr?, toMarketAddressFrame, store_get_self, EvalResult.ofOption]
  rw [toMarketCodeGuard, evalExpr_binary_nonshort (by decide) (by decide), extCodeSource rfl hr]
  simp [evalExpr?, evalBinaryOp?, pure, bind, EvalResult.bind]

theorem toMarketUninitialized (evm : State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hzero : ¬ 0 < (marketTickSpacing (marketFeeWord evm id)).toNat) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [toMarketBody_shape]
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert (ExecStmt.requireFalse _)
  exact (toMarketTickEval evm id).trans (by rw [decide_eq_false hzero])

theorem toMarketCodeTooLarge (evm : State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hlarge : ¬ (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [toMarketBody_shape]
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (toMarketTickEval evm id).trans (by rw [decide_eq_true hinit])
  apply ExecBlock.consNormal (ExecStmt.letDecl (toMarketAddressEval evm id))
  apply ExecBlock.consRevert (ExecStmt.requireFalse _)
  exact (toMarketCodeGuardEval evm id).trans (by rw [decide_eq_false hlarge])

def toMarketCodeFrame (evm : State) (id : UInt256) : Frame :=
  { toMarketAddressFrame evm id with
    locals := (toMarketAddressFrame evm id).locals.insert "code"
      (.bytes (externalCodePrefix evm.accountMap id)) }

def toMarketDecodedFrame (evm : State) (id : UInt256) (decoded : Value) : Frame :=
  { toMarketCodeFrame evm id with
    locals := (toMarketCodeFrame evm id).locals.insert "decoded" decoded }

def toMarketResultFrame (evm : State) (id : UInt256) (decoded : Value)
    (collaterals : List Value) : Frame :=
  { toMarketDecodedFrame evm id decoded with
    locals := (toMarketDecodedFrame evm id decoded).locals.insert "collaterals" (.array collaterals) }

theorem toMarketCodeEval (evm : State) (id : UInt256) :
    evalExpr? config (toMarketAddressFrame evm id) evm
      (.extCodePrefix (.var "create2Address") (.extCodeSize (.var "create2Address"))) =
      .ok (.bytes (externalCodePrefix evm.accountMap id)) := by
  apply evalExternalCodePrefix
  simp only [evalExpr?, toMarketAddressFrame, store_get_self, EvalResult.ofOption]

theorem toMarketCodeRun (evm : State) (id : UInt256) {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (htail : ExecBlock config (toMarketCodeFrame evm id) evm
      [.letDecl "decoded" none (.abiDecode Model.marketABI (.var "code")),
       .letDecl "collaterals" none (.tupleGet (.var "decoded") 3),
       .require toMarketCapacityExpr, .return [.var "decoded"]] result) :
    ExecBlock config { contract := contract, locals := toMarketArguments id } evm
      toMarketTransition.body result := by
  rw [toMarketBody_shape]
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    ((toMarketTickEval evm id).trans (by rw [decide_eq_true hinit])))
  apply ExecBlock.consNormal (ExecStmt.letDecl (toMarketAddressEval evm id))
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    ((toMarketCodeGuardEval evm id).trans (by rw [decide_eq_true hcode])))
  exact ExecBlock.consNormal (ExecStmt.letDecl (toMarketCodeEval evm id)) htail

theorem toMarketDecodeReverts (evm : State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hdecode : config.externalABI.decodeValue? Model.marketABI
      (externalCodePrefix evm.accountMap id) = none) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply toMarketCodeRun evm id hwv hhi hinit hcode
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert _)
  simp only [evalExpr?, toMarketCodeFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, hdecode]

set_option maxRecDepth 4096 in
theorem toMarketCapacityEval {frame : Frame} {evm : State} {code : ByteArray}
    {collaterals : List Value}
    (hc : frame.locals.get? "code" = some (.bytes code))
    (hp : frame.locals.get? "collaterals" = some (.array collaterals)) :
    evalExpr? config frame evm toMarketCapacityExpr =
      .ok (.bool (decide ((code.size + 31) / 32 * 32 + 160 * collaterals.length + 1408 < 2^64))) := by
  simp only [toMarketCapacityExpr, evalExpr?, hc, hp, readLocalPath?, bind, EvalResult.bind,
    pure, evalBinaryOp?, Int.ofNat_eq_natCast, show (32 : Int) ≠ 0 from by decide, if_false]
  norm_cast

theorem toMarketDecodedRun (evm : State) (id : UInt256) {decoded : Value}
    {collaterals : List Value} {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hdecode : config.externalABI.decodeValue? Model.marketABI
      (externalCodePrefix evm.accountMap id) = some decoded)
    (hcoll : tupleGetValue? decoded 3 = .ok (.array collaterals))
    (htail : ExecBlock config (toMarketResultFrame evm id decoded collaterals) evm
      [.require toMarketCapacityExpr, .return [.var "decoded"]] result) :
    ExecBlock config { contract := contract, locals := toMarketArguments id } evm
      toMarketTransition.body result := by
  apply toMarketCodeRun evm id hwv hhi hinit hcode
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := decoded) ?_) ?_
  · simp only [evalExpr?, toMarketCodeFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, hdecode, pure]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .array collaterals) ?_) htail
  simp only [evalExpr?, toMarketDecodedFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, hcoll]

theorem toMarketResultCapacityEval (evm : State) (id : UInt256) (decoded : Value)
    (collaterals : List Value) :
    evalExpr? config (toMarketResultFrame evm id decoded collaterals) evm toMarketCapacityExpr =
      .ok (.bool (decide (((extCodeSizeWord evm.accountMap id).toNat + 31) / 32 * 32 +
        160 * collaterals.length + 1408 < 2^64))) := by
  have hc : (toMarketResultFrame evm id decoded collaterals).locals.get? "code" =
      some (.bytes (externalCodePrefix evm.accountMap id)) := by
    simp only [toMarketResultFrame, toMarketDecodedFrame, toMarketCodeFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hp : (toMarketResultFrame evm id decoded collaterals).locals.get? "collaterals" =
      some (.array collaterals) := by
    exact store_get_self _ _ _
  simpa only [externalCodePrefix_size] using toMarketCapacityEval (evm := evm) hc hp

theorem toMarketCapacityReverts (evm : State) (id : UInt256) {decoded : Value}
    {collaterals : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hdecode : config.externalABI.decodeValue? Model.marketABI
      (externalCodePrefix evm.accountMap id) = some decoded)
    (hcoll : tupleGetValue? decoded 3 = .ok (.array collaterals))
    (hcap : ¬ ((extCodeSizeWord evm.accountMap id).toNat + 31) / 32 * 32 +
      160 * collaterals.length + 1408 < 2^64) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply toMarketDecodedRun evm id hwv hhi hinit hcode hdecode hcoll
  exact .consRevert (.requireFalse
    ((toMarketResultCapacityEval evm id decoded collaterals).trans (by rw [decide_eq_false hcap])))

theorem toMarketReturns (evm : State) (id : UInt256) {decoded : Value}
    {collaterals : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hinit : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat)
    (hcode : (extCodeSizeWord evm.accountMap id).toNat ≤ 18446744073709550464)
    (hdecode : config.externalABI.decodeValue? Model.marketABI
      (externalCodePrefix evm.accountMap id) = some decoded)
    (hcoll : tupleGetValue? decoded 3 = .ok (.array collaterals))
    (hcap : ((extCodeSizeWord evm.accountMap id).toNat + 31) / 32 * 32 +
      160 * collaterals.length + 1408 < 2^64) :
    ExecTransitionBody config contract evm (toMarketArguments id) toMarketTransition.body
      (.returned (toMarketResultFrame evm id decoded collaterals) evm (some [decoded])) := by
  apply ExecFuncBody.execBlockRet
  apply toMarketDecodedRun evm id hwv hhi hinit hcode hdecode hcoll
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    ((toMarketResultCapacityEval evm id decoded collaterals).trans (by rw [decide_eq_true hcap])))
  apply ExecBlock.consReturn (ExecStmt.return _)
  have hd : (toMarketResultFrame evm id decoded collaterals).locals.get? "decoded" =
      some decoded := by
    simp only [toMarketResultFrame, toMarketDecodedFrame]
    rw [store_get_ne _ _ (by decide), store_get_self]
  simp only [evalExprs?, evalExpr?, hd, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Midnight
