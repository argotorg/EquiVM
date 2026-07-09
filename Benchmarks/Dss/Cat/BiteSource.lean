import Benchmarks.Dss.Cat.Arithmetic
import Benchmarks.Dss.Cat.Common
import Benchmarks.Dss.Cat.BiteEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite(bytes32,address)` — Solm-side body (`ExecTransitionBody`)

Source-side refinement obligations for `bite`, proved with NO bytecode/RD.  The five external calls
(`vat.ilks`, `vat.urns`, `vat.grab`, `vow.fess`, `milkFlip.kick`) are threaded via
`ExecStmt.externalCallSuccess`/`Failure` over abstract `typedCallViaEVM` hypotheses; storage reads use
the `evalExpr_storage_scalar_value` collapse (ported from `Ilks.lean`); the three `min` calls use the
`execMinFunctionReturnX/Y` facts from `Arithmetic.lean`; the inline `checkedMul`/`checkedSub`/
`checkedAdd` reuse the `evalExpr_{mul,sub,add}256_{ok,revert}` facts; the divisions go through the
raw `.binary .div` evaluator (which reverts on `/0`).
-/

/-! ## `ilk`-keyed storage slot equations (ported from `Ilks.lean`) -/

abbrev biteIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev biteIlkVal (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (biteIlkBytes I)

abbrev biteIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (biteIlkBytes I)

abbrev biteIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev biteFlipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (biteIlkKey I), .field "flip"] }

abbrev biteChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (biteIlkKey I), .field "chop"] }

abbrev biteDunkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (biteIlkKey I), .field "dunk"] }

abbrev biteFlipSlot (I : ExecutionEnv) : UInt256 := ilksBase (biteIlkKey I)
abbrev biteChopSlot (I : ExecutionEnv) : UInt256 := biteFlipSlot I + ⟨1⟩
abbrev biteDunkSlot (I : ExecutionEnv) : UInt256 := biteFlipSlot I + ⟨2⟩

theorem biteIlkBytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (biteIlkBytes I).length = bytes32Width.val + 1 := by
  unfold biteIlkBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [htlen]; simp [bytes32Width]; omega

theorem biteIlkBytes_len_min {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [htlen]; simp [bytes32Width]; omega

theorem keyValueToWord_biteIlkKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (biteIlkKey I) = biteIlkWord I := by
  have hlen32 : (biteIlkBytes I).length = 32 := by
    have hlen := biteIlkBytes_len (I := I) hsz36
    simpa [bytes32Width] using hlen
  have hword : ABI.bytesToWord (biteIlkBytes I) = biteIlkWord I := by
    simpa [biteIlkBytes, biteIlkWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := biteIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [biteIlkKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (biteIlkWord I)

theorem biteFlipSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    biteFlipSlot I = solcMappingSlot ⟨1⟩ (biteIlkWord I) := by
  unfold biteFlipSlot ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_biteIlkKey hsz36]

/-! ## Storage-read helpers (parameterized over the accumulated frame + evm state)

Each read is a scalar collapse via `evalExpr_storage_scalar_value`; layouts are the fixed
`storageLayoutRaw` slots (`vat @3`, `live @2`, `box @5`, `litter @6`, `ilks[ilk].{flip,chop,dunk}`).
-/

/-- `vat` address read (`addrLoc ⟨3⟩`). -/
theorem biteVatRead {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (catSlotWord ⟨3⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat
      (UInt256.land (catSlotWord ⟨3⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat))
    hbase
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vatRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_address_offset0 evm ⟨3⟩)

/-- `vow` address read (`addrLoc ⟨4⟩`). -/
theorem biteVowRead {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (catSlotWord ⟨4⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨4⟩)
    (value := .address (AccountAddress.ofNat
      (UInt256.land (catSlotWord ⟨4⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat))
    hbase
    (by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vowRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_address_offset0 evm ⟨4⟩)

/-- `live` uint256 read (`wordLoc ⟨2⟩`). -/
theorem biteLiveRead {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "live" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (catSlotWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨2⟩)
    (value := .int (Int.ofNat (catSlotWord ⟨2⟩ evm.accountMap evm.executionEnv).toNat))
    hbase
    (by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [liveRef, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm ⟨2⟩)

/-- `box` uint256 read (`wordLoc ⟨5⟩`). -/
theorem biteBoxRead {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "box" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage boxRef) =
      .ok (.int (Int.ofNat (catSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := boxRef) (er := ({ base := "box", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (catSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat))
    hbase
    (by simp [boxRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [boxRef, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm ⟨5⟩)

/-- `litter` uint256 read (`wordLoc ⟨6⟩`). -/
theorem biteLitterRead {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "litter" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage litterRef) =
      .ok (.int (Int.ofNat (catSlotWord ⟨6⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := litterRef) (er := ({ base := "litter", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
    (value := .int (Int.ofNat (catSlotWord ⟨6⟩ evm.accountMap evm.executionEnv).toNat))
    hbase
    (by simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [litterRef, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm ⟨6⟩)

/-- `ilks[ilk].flip` address read. -/
theorem biteFlipRead {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (biteIlkVal I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "flip")) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (catSlotWord (biteFlipSlot I) evm.accountMap evm.executionEnv)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "flip") (er := biteFlipEvaledRef I)
    (t := .address) (loc := addrLoc (biteFlipSlot I))
    (value := .address (AccountAddress.ofNat
      (UInt256.land (catSlotWord (biteFlipSlot I) evm.accountMap evm.executionEnv)
        solcAddrMask).toNat))
    hbase
    (by
      have hkeyLen := biteIlkBytes_len_min (I := I) hsz36
      have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
          .ok (biteIlkVal I) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
        rw [hilk]; rfl
      simp [biteFlipEvaledRef, biteIlkKey, biteIlkVal, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, hvar, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [biteIlkKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, addrSt, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_address_offset0 evm (biteFlipSlot I))

/-- `ilks[ilk].chop` uint256 read. -/
theorem biteChopRead {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (biteIlkVal I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "chop")) =
      .ok (.int (Int.ofNat (catSlotWord (biteChopSlot I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "chop") (er := biteChopEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (biteChopSlot I))
    (value := .int (Int.ofNat (catSlotWord (biteChopSlot I) evm.accountMap evm.executionEnv).toNat))
    hbase
    (by
      have hkeyLen := biteIlkBytes_len_min (I := I) hsz36
      have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
          .ok (biteIlkVal I) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
        rw [hilk]; rfl
      simp [biteChopEvaledRef, biteIlkKey, biteIlkVal, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, hvar, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [biteIlkKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, addrSt, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm (biteChopSlot I))

/-- `ilks[ilk].dunk` uint256 read. -/
theorem biteDunkRead {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (biteIlkVal I)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "dunk")) =
      .ok (.int (Int.ofNat (catSlotWord (biteDunkSlot I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "dunk") (er := biteDunkEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (biteDunkSlot I))
    (value := .int (Int.ofNat (catSlotWord (biteDunkSlot I) evm.accountMap evm.executionEnv).toNat))
    hbase
    (by
      have hkeyLen := biteIlkBytes_len_min (I := I) hsz36
      have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
          .ok (biteIlkVal I) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
        rw [hilk]; rfl
      simp [biteDunkEvaledRef, biteIlkKey, biteIlkVal, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, hvar, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [biteIlkKey, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, IlkStructTy, addrSt, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_uint256 evm (biteDunkSlot I))

/-! ## Decoded locals and their lookups -/

abbrev biteUrnVal (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)

theorem biteLocals_get_ilk (I : ExecutionEnv) :
    (biteLocals I).get? "ilk" = some (biteIlkVal I) := by
  simp only [biteLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]; rfl

theorem biteLocals_get_urn (I : ExecutionEnv) :
    (biteLocals I).get? "urn" = some (biteUrnVal I) := by
  simp only [biteLocals]
  rw [store_get_self]

theorem biteLocals_get_vat (I : ExecutionEnv) : (biteLocals I).get? "vat" = none := by
  simp only [biteLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

/-- `.var "ilk"` evaluates to the decoded bytes32 given the lookup fact. -/
theorem evalExpr_biteIlk {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hilk : locals.get? "ilk" = some (biteIlkVal I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
      .ok (biteIlkVal I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
  rw [hilk]; rfl

theorem evalExpr_biteUrn {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hurn : locals.get? "urn" = some (biteUrnVal I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "urn") =
      .ok (biteUrnVal I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "urn") = _
  rw [hurn]; rfl

/-- `vat.ilks(ilk)` argument list. -/
theorem evalExprs_biteIlksArgs {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hilk : locals.get? "ilk" = some (biteIlkVal I)) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "ilk"] =
      .ok [biteIlkVal I] := by
  simp [evalExprs?, evalExpr_biteIlk I hilk, EvalResult.bind, bind, pure]

/-- `vat.urns(ilk, urn)` argument list. -/
theorem evalExprs_biteUrnsArgs {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hilk : locals.get? "ilk" = some (biteIlkVal I))
    (hurn : locals.get? "urn" = some (biteUrnVal I)) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "ilk", .var "urn"] =
      .ok [biteIlkVal I, biteUrnVal I] := by
  simp [evalExprs?, evalExpr_biteIlk I hilk, evalExpr_biteUrn I hurn,
    EvalResult.bind, bind, pure]

/-! ## The `vat` addresses at the entry / post-ilks EVM states -/

/-- The `vat` address at an EVM state, as returned by `biteVatRead`. -/
abbrev biteVatAddr (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (catSlotWord ⟨3⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat

/-- The extcodesize guard on `vat` is true when the vat account has nonempty code. -/
theorem biteVatGuard_true {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none)
    (hcode : 0 <
      (UInt256.ofNat ((evm.lookupAccount (biteVatAddr evm)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, biteVatRead hbase, evalBinaryOp?, EVM.Word.ofNat,
    biteVatAddr, hcode]

/-- The extcodesize guard on `vow` is true when the vow account has nonempty code. -/
theorem biteVowGuard_true {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vow" = none)
    (hcode : 0 <
      (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofNat
          (UInt256.land (catSlotWord ⟨4⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vowRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, biteVowRead hbase, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

/-- The extcodesize guard on `vow` is false when the vow account has empty code. Dual of
`biteVowGuard_true`. -/
theorem biteVowGuard_false {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vow" = none)
    (hcode0 : (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofNat
          (UInt256.land (catSlotWord ⟨4⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vowRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, biteVowRead hbase, evalBinaryOp?, EVM.Word.ofNat,
    hcode0]

/-- A `bytes32`/`uint256`/`address` word as a Solm `Value`. -/
abbrev bw (w : UInt256) : Value := .int (Int.ofNat w.toNat)

abbrev biteIlkTuple (a r s l d : UInt256) : Value := .tuple [bw a, bw r, bw s, bw l, bw d]
abbrev biteUrnTuple (ink art : UInt256) : Value := .tuple [bw ink, bw art]

theorem biteLocals_get_ne (I : ExecutionEnv) {a : Ident}
    (h1 : ("ilk" == a) = false) (h2 : ("urn" == a) = false) :
    (biteLocals I).get? a = none := by
  simp only [biteLocals]
  rw [store_get_ne _ _ h2, store_get_ne _ _ h1]
  simp

/-- Bind `.tupleGet (.var vn) i` in a `letDecl`, given the tuple lookup + the projection. -/
theorem biteTupleLet {evm : EVM.State} {locals : Store} (vn name : Ident) (ty : Option ABIType)
    (i : Nat) {tup elem : Value}
    (hget : locals.get? vn = some tup)
    (hidx : tupleGetValue? tup i = .ok elem) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.letDecl name ty (.tupleGet (.var vn) i))
      (.ok { contract := contract, locals := locals.insert name elem } evm) := by
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var vn) =
      .ok tup := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? vn) = .ok tup
    rw [hget]; rfl
  apply ExecStmt.letDecl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  exact hidx

/-! ## Checkpoint stores (prefix through `ink`/`art`) -/

abbrev bsIlk (I : ExecutionEnv) (a r s l d : UInt256) : Store :=
  (biteLocals I).insert "vatIlk" (biteIlkTuple a r s l d)
abbrev bsRate (I : ExecutionEnv) (a r s l d : UInt256) : Store :=
  (bsIlk I a r s l d).insert "rate" (bw r)
abbrev bsSpot (I : ExecutionEnv) (a r s l d : UInt256) : Store :=
  (bsRate I a r s l d).insert "spot" (bw s)
abbrev bsDust (I : ExecutionEnv) (a r s l d : UInt256) : Store :=
  (bsSpot I a r s l d).insert "dust" (bw d)
abbrev bsUrn (I : ExecutionEnv) (a r s l d ink art : UInt256) : Store :=
  (bsDust I a r s l d).insert "vatUrn" (biteUrnTuple ink art)
abbrev bsInk (I : ExecutionEnv) (a r s l d ink art : UInt256) : Store :=
  (bsUrn I a r s l d ink art).insert "ink" (bw ink)
abbrev bsArt (I : ExecutionEnv) (a r s l d ink art : UInt256) : Store :=
  (bsInk I a r s l d ink art).insert "art" (bw art)

theorem bsIlk_get_vatIlk (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsIlk I a r s l d).get? "vatIlk" = some (biteIlkTuple a r s l d) := by
  simp only [bsIlk]; rw [store_get_self]
theorem bsRate_get_vatIlk (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsRate I a r s l d).get? "vatIlk" = some (biteIlkTuple a r s l d) := by
  simp only [bsRate]; rw [store_get_ne _ _ (by decide)]; exact bsIlk_get_vatIlk I a r s l d
theorem bsSpot_get_vatIlk (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsSpot I a r s l d).get? "vatIlk" = some (biteIlkTuple a r s l d) := by
  simp only [bsSpot]; rw [store_get_ne _ _ (by decide)]; exact bsRate_get_vatIlk I a r s l d
theorem bsDust_get_vat (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsDust I a r s l d).get? "vat" = none := by
  simp only [bsDust, bsSpot, bsRate, bsIlk]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  exact biteLocals_get_vat I
theorem bsDust_get_ilk (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsDust I a r s l d).get? "ilk" = some (biteIlkVal I) := by
  simp only [bsDust, bsSpot, bsRate, bsIlk]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  exact biteLocals_get_ilk I
theorem bsDust_get_urn (I : ExecutionEnv) (a r s l d : UInt256) :
    (bsDust I a r s l d).get? "urn" = some (biteUrnVal I) := by
  simp only [bsDust, bsSpot, bsRate, bsIlk]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  exact biteLocals_get_urn I
theorem bsUrn_get_vatUrn (I : ExecutionEnv) (a r s l d ink art : UInt256) :
    (bsUrn I a r s l d ink art).get? "vatUrn" = some (biteUrnTuple ink art) := by
  simp only [bsUrn]; rw [store_get_self]
theorem bsInk_get_vatUrn (I : ExecutionEnv) (a r s l d ink art : UInt256) :
    (bsInk I a r s l d ink art).get? "vatUrn" = some (biteUrnTuple ink art) := by
  simp only [bsInk]; rw [store_get_ne _ _ (by decide)]; exact bsUrn_get_vatUrn I a r s l d ink art
theorem bsArt_get_live (I : ExecutionEnv) (a r s l d ink art : UInt256) :
    (bsArt I a r s l d ink art).get? "live" = none := by
  simp only [bsArt, bsInk, bsUrn, bsDust, bsSpot, bsRate, bsIlk]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  exact biteLocals_get_ne I (by decide) (by decide)

/-! ## Revert branch: `live != 1`

Threads the two `view` STATICCALLs (`vat.ilks`, `vat.urns`) and their tuple projections, then reverts
at `require(live == 1)`.  Exercises the full external-call + tuple-get + storage-read prefix. -/

set_option maxHeartbeats 4000000 in
theorem catBiteSourceLiveRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmIlk evmUrn : EVM.State}
    {ilksOut urnsOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art : UInt256}
    (hsz36 : 36 ≤ I.calldata.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0
          (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec :
      config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv ≠ ⟨1⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  -- checkpoint stores
  set L0 := biteLocals I with hL0
  set Lilk := L0.insert "vatIlk" (biteIlkTuple iArt iRate iSpot iLine iDust) with hLilk
  set Lrate := Lilk.insert "rate" (bw iRate) with hLrate
  set Lspot := Lrate.insert "spot" (bw iSpot) with hLspot
  set Ldust := Lspot.insert "dust" (bw iDust) with hLdust
  set Lurn := Ldust.insert "vatUrn" (biteUrnTuple ink art) with hLurn
  set Link := Lurn.insert "ink" (bw ink) with hLink
  set Lart := Link.insert "art" (bw art) with hLart
  -- ilks external call (success)
  have hIlksStmt :
      ExecStmt config { contract := contract, locals := L0 } evm0
        (.externalCall (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk" (perm := false))
        (.ok { contract := contract, locals := Lilk } evmIlk) := by
    simpa [hLilk, biteIlkTuple, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := L0 }) (evm := evm0)
        (evm' := evmIlk)
        (receiver := .storage vatRef) (name := "ilks") (sendVal := 0)
        (target := biteVatAddr evm0) (args := [.var "ilk"]) (argVals := [biteIlkVal I])
        (out := ilksOut) (perm := false)
        (value := [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
        (biteVatRead (biteLocals_get_vat I))
        (by simp [evalExpr?, pure])
        (evalExprs_biteIlksArgs I (biteLocals_get_ilk I))
        hIlksCall hIlksDec
  -- rate / spot / dust tuple projections
  have hRateStmt :
      ExecStmt config { contract := contract, locals := Lilk } evmIlk
        (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := Lrate } evmIlk) := by
    refine biteTupleLet "vatIlk" "rate" (some uint256) 1
      (by rw [hLilk, store_get_self]) (by rfl)
  have hSpotStmt :
      ExecStmt config { contract := contract, locals := Lrate } evmIlk
        (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract, locals := Lspot } evmIlk) := by
    refine biteTupleLet "vatIlk" "spot" (some uint256) 2
      (by rw [hLrate, store_get_ne _ _ (by decide), hLilk, store_get_self]) (by rfl)
  have hDustStmt :
      ExecStmt config { contract := contract, locals := Lspot } evmIlk
        (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract, locals := Ldust } evmIlk) := by
    refine biteTupleLet "vatIlk" "dust" (some uint256) 4
      (by rw [hLspot, store_get_ne _ _ (by decide), hLrate, store_get_ne _ _ (by decide),
        hLilk, store_get_self]) (by rfl)
  -- urns external call (success)
  have hDustVat : Ldust.get? "vat" = none := by
    rw [hLdust, store_get_ne _ _ (by decide), hLspot, store_get_ne _ _ (by decide),
      hLrate, store_get_ne _ _ (by decide), hLilk, store_get_ne _ _ (by decide)]
    exact biteLocals_get_vat I
  have hDustIlk : Ldust.get? "ilk" = some (biteIlkVal I) := by
    rw [hLdust, store_get_ne _ _ (by decide), hLspot, store_get_ne _ _ (by decide),
      hLrate, store_get_ne _ _ (by decide), hLilk, store_get_ne _ _ (by decide)]
    exact biteLocals_get_ilk I
  have hDustUrn : Ldust.get? "urn" = some (biteUrnVal I) := by
    rw [hLdust, store_get_ne _ _ (by decide), hLspot, store_get_ne _ _ (by decide),
      hLrate, store_get_ne _ _ (by decide), hLilk, store_get_ne _ _ (by decide)]
    exact biteLocals_get_urn I
  have hUrnsStmt :
      ExecStmt config { contract := contract, locals := Ldust } evmIlk
        (.externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", .var "urn"] "vatUrn"
          (perm := false))
        (.ok { contract := contract, locals := Lurn } evmUrn) := by
    simpa [hLurn, biteUrnTuple, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := Ldust }) (evm := evmIlk)
        (evm' := evmUrn)
        (receiver := .storage vatRef) (name := "urns") (sendVal := 0)
        (target := biteVatAddr evmIlk) (args := [.var "ilk", .var "urn"])
        (argVals := [biteIlkVal I, biteUrnVal I]) (out := urnsOut) (perm := false)
        (value := [bw ink, bw art])
        (biteVatRead hDustVat)
        (by simp [evalExpr?, pure])
        (evalExprs_biteUrnsArgs I hDustIlk hDustUrn)
        hUrnsCall hUrnsDec
  -- ink / art tuple projections
  have hInkStmt :
      ExecStmt config { contract := contract, locals := Lurn } evmUrn
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := Link } evmUrn) := by
    refine biteTupleLet "vatUrn" "ink" (some uint256) 0
      (by rw [hLurn, store_get_self]) (by rfl)
  have hArtStmt :
      ExecStmt config { contract := contract, locals := Link } evmUrn
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := Lart } evmUrn) := by
    refine biteTupleLet "vatUrn" "art" (some uint256) 1
      (by rw [hLink, store_get_ne _ _ (by decide), hLurn, store_get_self]) (by rfl)
  -- live == 1 evaluates false
  have hLartLive : Lart.get? "live" = none := by
    rw [hLart, store_get_ne _ _ (by decide), hLink, store_get_ne _ _ (by decide),
      hLurn, store_get_ne _ _ (by decide), hLdust, store_get_ne _ _ (by decide),
      hLspot, store_get_ne _ _ (by decide), hLrate, store_get_ne _ _ (by decide),
      hLilk, store_get_ne _ _ (by decide)]
    exact biteLocals_get_ne I (by decide) (by decide)
  have hLiveReq :
      evalExpr? config { contract := contract, locals := Lart } evmUrn
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    have hval :
        (Value.int (Int.ofNat (catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv).toNat) ==
          Value.int 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hlive (u256_inj (Int.ofNat.inj hbad))
    simp only [evalExpr?, biteLiveRead hLartLive, EvalResult.bind, bind, pure, evalBinaryOp?, hval]
  -- assemble the reverting block
  have hblock :
      ExecBlock config { contract := contract, locals := L0 } evm0 biteTransition.body
        .reverted := by
    simp only [biteTransition, nonpayable, checkedExternalCallStmts, checkedMulUintInto,
      checkedSubUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0))) ?_
    refine ExecBlock.consNormal hIlksStmt ?_
    refine ExecBlock.consNormal hRateStmt ?_
    refine ExecBlock.consNormal hSpotStmt ?_
    refine ExecBlock.consNormal hDustStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true hDustVat hvatCodeIlk)) ?_
    refine ExecBlock.consNormal hUrnsStmt ?_
    refine ExecBlock.consNormal hInkStmt ?_
    refine ExecBlock.consNormal hArtStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hLiveReq)
  simpa [ExecTransitionBody, hL0] using ExecFuncBody.execBlockRevert hblock

/-! ## Generic Solm-expression evaluation helpers for the `bite` body -/

/-- `x / y` reverts on `y = 0`; otherwise the quotient word. -/
theorem evalExpr_div256_ok {evm : EVM.State} {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y = .ok (bw b))
    (hb : 0 < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (bw (UInt256.div a b)) := by
  have hbne : Int.ofNat b.toNat ≠ 0 := by rw [Int.ofNat_eq_natCast]; exact_mod_cast hb.ne'
  simp only [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, bw, if_neg hbne]
  exact congrArg (fun z => EvalResult.ok (Value.int z)) Int.ofNat_ediv_ofNat

theorem evalExpr_div256_revert {evm : EVM.State} {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y = .ok (bw b))
    (hb : b.toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) = .revert := by
  simp only [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, bw]
  rw [if_pos (by rw [hb]; rfl)]

theorem evalExpr_and_true {evm : EVM.State} {locals : Store} {p q : Expr}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (.bool true))
    (hq : evalExpr? config { contract := contract, locals := locals } evm q = .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and p q) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, hq, pure]

theorem evalExpr_and_falseL {evm : EVM.State} {locals : Store} {p q : Expr}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (.bool false)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and p q) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, pure]

theorem evalExpr_and_falseR {evm : EVM.State} {locals : Store} {p q : Expr}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (.bool true))
    (hq : evalExpr? config { contract := contract, locals := locals } evm q = .ok (.bool false)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .and p q) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, hq, pure]

theorem evalExpr_gtLit_true {evm : EVM.State} {locals : Store} {x : Expr} {a : UInt256} {n : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (h : n < Int.ofNat a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .gt x (.intLit n)) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, pure, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t)) (decide_eq_true h)

theorem evalExpr_gtLit_false {evm : EVM.State} {locals : Store} {x : Expr} {a : UInt256} {n : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (h : Int.ofNat a.toNat ≤ n) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .gt x (.intLit n)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, pure, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t)) (decide_eq_false (by omega))

theorem evalExpr_leLit_true {evm : EVM.State} {locals : Store} {x : Expr} {a : UInt256} {n : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (h : Int.ofNat a.toNat ≤ n) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le x (.intLit n)) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, pure, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t)) (decide_eq_true h)

theorem evalExpr_leLit_false {evm : EVM.State} {locals : Store} {x : Expr} {a : UInt256} {n : Int}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (h : n < Int.ofNat a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le x (.intLit n)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hx, evalBinaryOp?, pure, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t)) (decide_eq_false (by omega))

theorem evalExpr_lt_uint256_true {evm : EVM.State} {locals : Store} {p q : Expr} {a b : UInt256}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (bw a))
    (hq : evalExpr? config { contract := contract, locals := locals } evm q = .ok (bw b))
    (h : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt p q) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, hq, evalBinaryOp?, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t)) (decide_eq_true (Int.ofNat_lt.mpr h))

theorem evalExpr_lt_uint256_false {evm : EVM.State} {locals : Store} {p q : Expr} {a b : UInt256}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (bw a))
    (hq : evalExpr? config { contract := contract, locals := locals } evm q = .ok (bw b))
    (h : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt p q) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, hq, evalBinaryOp?, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t))
    (decide_eq_false (not_lt.mpr (Int.ofNat_le.mpr h)))

theorem evalExpr_ge_uint256_false {evm : EVM.State} {locals : Store} {p q : Expr} {a b : UInt256}
    (hp : evalExpr? config { contract := contract, locals := locals } evm p = .ok (bw a))
    (hq : evalExpr? config { contract := contract, locals := locals } evm q = .ok (bw b))
    (h : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge p q) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hp, hq, evalBinaryOp?, bw]
  exact congrArg (fun t => EvalResult.ok (Value.bool t))
    (decide_eq_false (not_le.mpr (Int.ofNat_lt.mpr h)))

/-- The `checkedMul` overflow guard `y == 0 || name / y == x` is `true` for `name = x*y`, `y > 0`,
    no overflow. -/
theorem evalExpr_checkedMulCheck_true {evm : EVM.State} {locals : Store} {x y : Expr}
    {name : Ident} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x = .ok (bw a))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y = .ok (bw b))
    (hname : locals.get? name = some (bw prod))
    (hprod : prod = a * b) (hfit : a.toNat * b.toNat < UInt256.size) (hb : 0 < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .or (.binary .eq y (.intLit 0)) (.binary .eq (.binary .div (.var name) y) x)) =
      .ok (.bool true) := by
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (bw prod) := by
    rw [evalExpr?]; change EvalResult.ofOption _ (locals.get? name) = _; rw [hname]; rfl
  have hbne : Int.ofNat b.toNat ≠ 0 := by rw [Int.ofNat_eq_natCast]; exact_mod_cast hb.ne'
  have hprodNat : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, u256_mul_op_toNat, Nat.mod_eq_of_lt hfit]
  have hyne : (bw b == (Value.int 0)) = false := by
    simp only [bw, beq_eq_false_iff_ne, ne_eq, Value.int.injEq]
    rw [Int.ofNat_eq_natCast]; exact_mod_cast hb.ne'
  simp only [evalExpr?, EvalResult.bind, bind, hx, hy, hvar, evalBinaryOp?, pure, hyne,
    if_neg hbne, bw]
  have hdiv : Int.ofNat prod.toNat / Int.ofNat b.toNat = Int.ofNat a.toNat := by
    rw [hprodNat]; exact Int.ofNat_ediv_ofNat.trans (congrArg Int.ofNat (Nat.mul_div_cancel _ hb))
  rw [hdiv]; simp

/-- `WAD` as a `UInt256`. -/
def wadU : UInt256 := UInt256.ofNat WAD.toNat

theorem wadU_toNat : wadU.toNat = 1000000000000000000 := by
  rw [wadU, ulit_toNat']
  · rfl
  · unfold WAD; decide

theorem wadU_pos : 0 < wadU.toNat := by rw [wadU_toNat]; omega

theorem evalExpr_wad {evm : EVM.State} {solm : Frame} :
    evalExpr? config solm evm (.intLit WAD) = .ok (bw wadU) := by
  have h : (WAD : Int) = Int.ofNat wadU.toNat := by rw [wadU_toNat]; rfl
  simp only [evalExpr?, pure, bw]; rw [h]

/-- `-int256(v)` for a `uint256`-valued local. -/
theorem evalExpr_negInt256_var {evm : EVM.State} {locals : Store} {name : Ident} {d : UInt256}
    (hd : locals.get? name = some (bw d)) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.unary .neg (asInt256 (.var name))) = .ok (.int (-(Int.ofNat d.toNat))) := by
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (bw d) := by
    rw [evalExpr?]; change EvalResult.ofOption _ (locals.get? name) = _; rw [hd]; rfl
  simp only [asInt256, evalExpr?, EvalResult.bind, bind, hvar, evalUnaryOp?, castValue?,
    int256St, int256Int, EvalResult.ofOption, bw]

theorem evalExpr_this {evm : EVM.State} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals } evm thisAddr =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp only [thisAddr, evalExpr?, envValue, pure]

/-! ## `min` internal call -/

/-- Word `min` as a `UInt256` (`bite`'s three `min` calls). -/
def umin (a b : UInt256) : UInt256 := if a.toNat ≤ b.toNat then a else b

theorem execMinReturn (evm : EVM.State) (x y : UInt256) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      minFunction.body
      (.returned { contract := contract, locals := uintBinaryLocals x y } evm
        (some [bw (umin x y)])) := by
  unfold umin
  by_cases h : x.toNat ≤ y.toNat
  · simp only [h, if_true]; exact execMinFunctionReturnX evm h
  · simp only [h, if_false]; exact execMinFunctionReturnY evm (by omega)

/-- An internal `min(xn, yn)` call, binding `min` of the two operand words to `retVar`. -/
theorem execMinCall {locals : Store} {evm : EVM.State} {xn yn retVar : Ident} {x y : UInt256}
    (hx : locals.get? xn = some (bw x)) (hy : locals.get? yn = some (bw y)) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "min" [.var xn, .var yn] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (bw (umin x y)) } evm) := by
  have hxv : evalExpr? config { contract := contract, locals := locals } evm (.var xn) =
      .ok (bw x) := by
    rw [evalExpr?]; change EvalResult.ofOption _ (locals.get? xn) = _; rw [hx]; rfl
  have hyv : evalExpr? config { contract := contract, locals := locals } evm (.var yn) =
      .ok (bw y) := by
    rw [evalExpr?]; change EvalResult.ofOption _ (locals.get? yn) = _; rw [hy]; rfl
  have hargs : evalExprs? config { contract := contract, locals := locals } evm
      [.var xn, .var yn] = .ok [bw x, bw y] := by
    simp [evalExprs?, hxv, hyv, EvalResult.bind, bind, pure]
  simpa [resumeAfterInternalCall, collapseReturns] using
    internalCallFunctionReturn (cfg := config)
      (caller := { contract := contract, locals := locals }) (evm := evm) (name := "min")
      (retVar := retVar) (args := [.var xn, .var yn]) (argVals := [bw x, bw y])
      (callee := minFunction) (locals := uintBinaryLocals x y)
      (calleeSolm := { contract := contract, locals := uintBinaryLocals x y }) (calleeEvm := evm)
      (value := some [bw (umin x y)]) hargs (by rfl) (by rfl) (execMinReturn evm x y)

/-! ## Derived storage-word / intermediate values -/

abbrev biteBoxW (evm : EVM.State) : UInt256 := catSlotWord ⟨5⟩ evm.accountMap evm.executionEnv
abbrev biteLitW (evm : EVM.State) : UInt256 := catSlotWord ⟨6⟩ evm.accountMap evm.executionEnv
abbrev biteChopW (I : ExecutionEnv) (evm : EVM.State) : UInt256 :=
  catSlotWord (biteChopSlot I) evm.accountMap evm.executionEnv
abbrev biteDunkW (I : ExecutionEnv) (evm : EVM.State) : UInt256 :=
  catSlotWord (biteDunkSlot I) evm.accountMap evm.executionEnv
abbrev biteFlipAddrV (I : ExecutionEnv) (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (catSlotWord (biteFlipSlot I) evm.accountMap evm.executionEnv) solcAddrMask).toNat

abbrev biteRoomV (evm : EVM.State) : UInt256 := UInt256.sub (biteBoxW evm) (biteLitW evm)
abbrev biteDunkRoomV (I : ExecutionEnv) (evm : EVM.State) : UInt256 :=
  umin (biteDunkW I evm) (biteRoomV evm)
abbrev biteDunkRoomWadV (I : ExecutionEnv) (evm : EVM.State) : UInt256 :=
  biteDunkRoomV I evm * wadU
abbrev biteDartDenomV (I : ExecutionEnv) (evm : EVM.State) (r : UInt256) : UInt256 :=
  UInt256.div (biteDunkRoomWadV I evm) r
abbrev biteDartCandV (I : ExecutionEnv) (evm : EVM.State) (r : UInt256) : UInt256 :=
  UInt256.div (biteDartDenomV I evm r) (biteChopW I evm)
abbrev biteDartV (I : ExecutionEnv) (evm : EVM.State) (r art : UInt256) : UInt256 :=
  umin art (biteDartCandV I evm r)
abbrev biteInkDartV (I : ExecutionEnv) (evm : EVM.State) (r art ink : UInt256) : UInt256 :=
  ink * biteDartV I evm r art
abbrev biteDinkCandV (I : ExecutionEnv) (evm : EVM.State) (r art ink : UInt256) : UInt256 :=
  UInt256.div (biteInkDartV I evm r art ink) art
abbrev biteDinkV (I : ExecutionEnv) (evm : EVM.State) (r art ink : UInt256) : UInt256 :=
  umin ink (biteDinkCandV I evm r art ink)
abbrev biteDartRateV (I : ExecutionEnv) (evm : EVM.State) (r art : UInt256) : UInt256 :=
  biteDartV I evm r art * r
abbrev biteTabBaseV (I : ExecutionEnv) (evm : EVM.State) (r art : UInt256) : UInt256 :=
  biteDartRateV I evm r art * biteChopW I evm
abbrev biteTabV (I : ExecutionEnv) (evm : EVM.State) (r art : UInt256) : UInt256 :=
  UInt256.div (biteTabBaseV I evm r art) wadU
abbrev biteLitterNewV (I : ExecutionEnv) (evmUrn evmFess : EVM.State) (r art : UInt256) : UInt256 :=
  biteLitW evmFess + biteTabV I evmUrn r art

/-! ## Checkpoint stores through the arithmetic middle (extends `bsArt`) -/

abbrev bsInkSpot (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsArt I a r s l d ink art).insert "inkSpot" (bw (ink * s))
abbrev bsArtRate (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsInkSpot I evmUrn a r s l d ink art).insert "artRateUnsafe" (bw (art * r))
abbrev bsMilkFlip (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsArtRate I evmUrn a r s l d ink art).insert "milkFlip" (.address (biteFlipAddrV I evmUrn))
abbrev bsMilkChop (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsMilkFlip I evmUrn a r s l d ink art).insert "milkChop" (bw (biteChopW I evmUrn))
abbrev bsMilkDunk (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsMilkChop I evmUrn a r s l d ink art).insert "milkDunk" (bw (biteDunkW I evmUrn))
abbrev bsRoom (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsMilkDunk I evmUrn a r s l d ink art).insert "room" (bw (biteRoomV evmUrn))
abbrev bsDunkRoom (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsRoom I evmUrn a r s l d ink art).insert "dunkRoom" (bw (biteDunkRoomV I evmUrn))
abbrev bsDunkRoomWad (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDunkRoom I evmUrn a r s l d ink art).insert "dunkRoomWad" (bw (biteDunkRoomWadV I evmUrn))
abbrev bsDartDenom (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDunkRoomWad I evmUrn a r s l d ink art).insert "dartDenomRate" (bw (biteDartDenomV I evmUrn r))
abbrev bsDartCand (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDartDenom I evmUrn a r s l d ink art).insert "dartCandidate" (bw (biteDartCandV I evmUrn r))
abbrev bsDart (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDartCand I evmUrn a r s l d ink art).insert "dart" (bw (biteDartV I evmUrn r art))
abbrev bsInkDart (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDart I evmUrn a r s l d ink art).insert "inkDart" (bw (biteInkDartV I evmUrn r art ink))
abbrev bsDinkCand (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsInkDart I evmUrn a r s l d ink art).insert "dinkCandidate" (bw (biteDinkCandV I evmUrn r art ink))
abbrev bsDink (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDinkCand I evmUrn a r s l d ink art).insert "dink" (bw (biteDinkV I evmUrn r art ink))

/-! ## Checkpoint stores through the tail (grab / fess / assign / kick) -/

abbrev btGrab (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (bsDink I evmUrn a r s l d ink art).insert "_grabRet" .unit
abbrev btDartRate (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (btGrab I evmUrn a r s l d ink art).insert "dartRate" (bw (biteDartRateV I evmUrn r art))
abbrev btFess (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (btDartRate I evmUrn a r s l d ink art).insert "_fessRet" .unit
abbrev btTabBase (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (btFess I evmUrn a r s l d ink art).insert "tabBase" (bw (biteTabBaseV I evmUrn r art))
abbrev btTab (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) : Store :=
  (btTabBase I evmUrn a r s l d ink art).insert "tab" (bw (biteTabV I evmUrn r art))
abbrev btLitterNew (I : ExecutionEnv) (evmUrn evmFess : EVM.State) (a r s l d ink art : UInt256) :
    Store :=
  (btTab I evmUrn a r s l d ink art).insert "litterNew"
    (bw (biteLitterNewV I evmUrn evmFess r art))
abbrev btKick (I : ExecutionEnv) (evmUrn evmFess : EVM.State) (a r s l d ink art id : UInt256) :
    Store :=
  (btLitterNew I evmUrn evmFess a r s l d ink art).insert "id" (bw id)

/-! ## Store lookups at the arithmetic / tail checkpoint frames

All proved uniformly by `simp (disch := decide) only [<frame unfolds>, store_get_ne, store_get_self]`,
peeling inserts down to `biteLocals` (then the base lookup) or to the target insert. -/

section Lookups
variable (I : ExecutionEnv) (evmUrn evmFess : EVM.State) (a r s l d ink art id : UInt256)

/-- The full frame-unfold simp set. -/
local macro "peel" : tactic =>
  `(tactic| simp (disch := decide) only
    [bsInkSpot, bsArtRate, bsMilkFlip, bsMilkChop, bsMilkDunk, bsRoom, bsDunkRoom, bsDunkRoomWad,
     bsDartDenom, bsDartCand, bsDart, bsInkDart, bsDinkCand, bsDink, btGrab, btDartRate, btFess,
     btTabBase, btTab, btLitterNew, btKick, bsArt, bsInk, bsUrn, bsDust, bsSpot, bsRate, bsIlk,
     store_get_ne, store_get_self])

-- value / self lookups
theorem bsArt_get_ink : (bsArt I a r s l d ink art).get? "ink" = some (bw ink) := by peel
theorem bsArt_get_spot : (bsArt I a r s l d ink art).get? "spot" = some (bw s) := by peel
theorem bsInkSpot_get_ink : (bsInkSpot I evmUrn a r s l d ink art).get? "ink" = some (bw ink) := by peel
theorem bsInkSpot_get_spot : (bsInkSpot I evmUrn a r s l d ink art).get? "spot" = some (bw s) := by peel
theorem bsInkSpot_get_inkSpot :
    (bsInkSpot I evmUrn a r s l d ink art).get? "inkSpot" = some (bw (ink * s)) := by peel
theorem bsInkSpot_get_art : (bsInkSpot I evmUrn a r s l d ink art).get? "art" = some (bw art) := by peel
theorem bsInkSpot_get_rate : (bsInkSpot I evmUrn a r s l d ink art).get? "rate" = some (bw r) := by peel
theorem bsArtRate_get_art : (bsArtRate I evmUrn a r s l d ink art).get? "art" = some (bw art) := by peel
theorem bsArtRate_get_rate : (bsArtRate I evmUrn a r s l d ink art).get? "rate" = some (bw r) := by peel
theorem bsArtRate_get_spot : (bsArtRate I evmUrn a r s l d ink art).get? "spot" = some (bw s) := by peel
theorem bsArtRate_get_inkSpot :
    (bsArtRate I evmUrn a r s l d ink art).get? "inkSpot" = some (bw (ink * s)) := by peel
theorem bsArtRate_get_artRateUnsafe :
    (bsArtRate I evmUrn a r s l d ink art).get? "artRateUnsafe" = some (bw (art * r)) := by peel
theorem bsRoom_get_room : (bsRoom I evmUrn a r s l d ink art).get? "room" = some (bw (biteRoomV evmUrn)) := by peel
theorem bsRoom_get_dust : (bsRoom I evmUrn a r s l d ink art).get? "dust" = some (bw d) := by peel
theorem bsRoom_get_milkDunk :
    (bsRoom I evmUrn a r s l d ink art).get? "milkDunk" = some (bw (biteDunkW I evmUrn)) := by peel
theorem bsDunkRoom_get_dunkRoom :
    (bsDunkRoom I evmUrn a r s l d ink art).get? "dunkRoom" = some (bw (biteDunkRoomV I evmUrn)) := by peel
theorem bsDunkRoomWad_get_dunkRoom :
    (bsDunkRoomWad I evmUrn a r s l d ink art).get? "dunkRoom" = some (bw (biteDunkRoomV I evmUrn)) := by peel
theorem bsDunkRoomWad_get_dunkRoomWad :
    (bsDunkRoomWad I evmUrn a r s l d ink art).get? "dunkRoomWad" =
      some (bw (biteDunkRoomWadV I evmUrn)) := by peel
theorem bsDunkRoomWad_get_rate :
    (bsDunkRoomWad I evmUrn a r s l d ink art).get? "rate" = some (bw r) := by peel
theorem bsDartDenom_get_dartDenomRate :
    (bsDartDenom I evmUrn a r s l d ink art).get? "dartDenomRate" =
      some (bw (biteDartDenomV I evmUrn r)) := by peel
theorem bsDartDenom_get_milkChop :
    (bsDartDenom I evmUrn a r s l d ink art).get? "milkChop" = some (bw (biteChopW I evmUrn)) := by peel
theorem bsDartCand_get_art : (bsDartCand I evmUrn a r s l d ink art).get? "art" = some (bw art) := by peel
theorem bsDartCand_get_dartCandidate :
    (bsDartCand I evmUrn a r s l d ink art).get? "dartCandidate" =
      some (bw (biteDartCandV I evmUrn r)) := by peel
theorem bsDart_get_ink : (bsDart I evmUrn a r s l d ink art).get? "ink" = some (bw ink) := by peel
theorem bsDart_get_dart :
    (bsDart I evmUrn a r s l d ink art).get? "dart" = some (bw (biteDartV I evmUrn r art)) := by peel
theorem bsInkDart_get_ink : (bsInkDart I evmUrn a r s l d ink art).get? "ink" = some (bw ink) := by peel
theorem bsInkDart_get_dart :
    (bsInkDart I evmUrn a r s l d ink art).get? "dart" = some (bw (biteDartV I evmUrn r art)) := by peel
theorem bsInkDart_get_art : (bsInkDart I evmUrn a r s l d ink art).get? "art" = some (bw art) := by peel
theorem bsInkDart_get_inkDart :
    (bsInkDart I evmUrn a r s l d ink art).get? "inkDart" = some (bw (biteInkDartV I evmUrn r art ink)) := by peel
theorem bsDinkCand_get_ink : (bsDinkCand I evmUrn a r s l d ink art).get? "ink" = some (bw ink) := by peel
theorem bsDinkCand_get_dinkCandidate :
    (bsDinkCand I evmUrn a r s l d ink art).get? "dinkCandidate" =
      some (bw (biteDinkCandV I evmUrn r art ink)) := by peel
theorem bsDink_get_dart :
    (bsDink I evmUrn a r s l d ink art).get? "dart" = some (bw (biteDartV I evmUrn r art)) := by peel
theorem bsDink_get_dink :
    (bsDink I evmUrn a r s l d ink art).get? "dink" = some (bw (biteDinkV I evmUrn r art ink)) := by peel

-- passthrough lookups (ilk / urn / storage-name → none)
theorem bsArtRate_get_ilk : (bsArtRate I evmUrn a r s l d ink art).get? "ilk" = some (biteIlkVal I) := by
  peel; exact biteLocals_get_ilk I
theorem bsArtRate_get_ilks : (bsArtRate I evmUrn a r s l d ink art).get? "ilks" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsMilkFlip_get_ilk : (bsMilkFlip I evmUrn a r s l d ink art).get? "ilk" = some (biteIlkVal I) := by
  peel; exact biteLocals_get_ilk I
theorem bsMilkFlip_get_ilks : (bsMilkFlip I evmUrn a r s l d ink art).get? "ilks" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsMilkChop_get_ilk : (bsMilkChop I evmUrn a r s l d ink art).get? "ilk" = some (biteIlkVal I) := by
  peel; exact biteLocals_get_ilk I
theorem bsMilkChop_get_ilks : (bsMilkChop I evmUrn a r s l d ink art).get? "ilks" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsMilkDunk_get_box : (bsMilkDunk I evmUrn a r s l d ink art).get? "box" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsMilkDunk_get_litter : (bsMilkDunk I evmUrn a r s l d ink art).get? "litter" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsRoom_get_box : (bsRoom I evmUrn a r s l d ink art).get? "box" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsRoom_get_litter : (bsRoom I evmUrn a r s l d ink art).get? "litter" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsDink_get_vat : (bsDink I evmUrn a r s l d ink art).get? "vat" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsDink_get_vow : (bsDink I evmUrn a r s l d ink art).get? "vow" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem bsDink_get_ilk : (bsDink I evmUrn a r s l d ink art).get? "ilk" = some (biteIlkVal I) := by
  peel; exact biteLocals_get_ilk I
theorem bsDink_get_urn : (bsDink I evmUrn a r s l d ink art).get? "urn" = some (biteUrnVal I) := by
  peel; exact biteLocals_get_urn I

-- tail-frame lookups
theorem btGrab_get_dart :
    (btGrab I evmUrn a r s l d ink art).get? "dart" = some (bw (biteDartV I evmUrn r art)) := by peel
theorem btGrab_get_rate : (btGrab I evmUrn a r s l d ink art).get? "rate" = some (bw r) := by peel
theorem btDartRate_get_dart :
    (btDartRate I evmUrn a r s l d ink art).get? "dart" = some (bw (biteDartV I evmUrn r art)) := by peel
theorem btDartRate_get_rate : (btDartRate I evmUrn a r s l d ink art).get? "rate" = some (bw r) := by peel
theorem btDartRate_get_dartRate :
    (btDartRate I evmUrn a r s l d ink art).get? "dartRate" = some (bw (biteDartRateV I evmUrn r art)) := by peel
theorem btDartRate_get_vow : (btDartRate I evmUrn a r s l d ink art).get? "vow" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem btFess_get_dartRate :
    (btFess I evmUrn a r s l d ink art).get? "dartRate" = some (bw (biteDartRateV I evmUrn r art)) := by peel
theorem btFess_get_milkChop :
    (btFess I evmUrn a r s l d ink art).get? "milkChop" = some (bw (biteChopW I evmUrn)) := by peel
theorem btTabBase_get_dartRate :
    (btTabBase I evmUrn a r s l d ink art).get? "dartRate" = some (bw (biteDartRateV I evmUrn r art)) := by peel
theorem btTabBase_get_milkChop :
    (btTabBase I evmUrn a r s l d ink art).get? "milkChop" = some (bw (biteChopW I evmUrn)) := by peel
theorem btTabBase_get_tabBase :
    (btTabBase I evmUrn a r s l d ink art).get? "tabBase" = some (bw (biteTabBaseV I evmUrn r art)) := by peel
theorem btTab_get_tab :
    (btTab I evmUrn a r s l d ink art).get? "tab" = some (bw (biteTabV I evmUrn r art)) := by peel
theorem btTab_get_litter : (btTab I evmUrn a r s l d ink art).get? "litter" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem btLitterNew_get_litter : (btLitterNew I evmUrn evmFess a r s l d ink art).get? "litter" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem btLitterNew_get_litterNew :
    (btLitterNew I evmUrn evmFess a r s l d ink art).get? "litterNew" =
      some (bw (biteLitterNewV I evmUrn evmFess r art)) := by peel
theorem btLitterNew_get_milkFlip :
    (btLitterNew I evmUrn evmFess a r s l d ink art).get? "milkFlip" =
      some (.address (biteFlipAddrV I evmUrn)) := by peel
theorem btLitterNew_get_urn :
    (btLitterNew I evmUrn evmFess a r s l d ink art).get? "urn" = some (biteUrnVal I) := by
  peel; exact biteLocals_get_urn I
theorem btLitterNew_get_vow : (btLitterNew I evmUrn evmFess a r s l d ink art).get? "vow" = none := by
  peel; exact biteLocals_get_ne I (by decide) (by decide)
theorem btLitterNew_get_tab :
    (btLitterNew I evmUrn evmFess a r s l d ink art).get? "tab" = some (bw (biteTabV I evmUrn r art)) := by peel
theorem btLitterNew_get_dink :
    (btLitterNew I evmUrn evmFess a r s l d ink art).get? "dink" = some (bw (biteDinkV I evmUrn r art ink)) := by peel
theorem btKick_get_id : (btKick I evmUrn evmFess a r s l d ink art id).get? "id" = some (bw id) := by peel

end Lookups

/-! ## Body decomposition: prefix / arith₁ / arith₂ / tail -/

def bitePreStmts : List Stmt :=
  nonpayable ++
  checkedExternalCallStmts (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
    (perm := false) ++
  [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
    .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
    .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ] ++
  checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0) [.var "ilk", .var "urn"] "vatUrn"
    (perm := false) ++
  [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
    .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
    .require (.binary .eq (.storage liveRef) (.intLit 1)) ]

def biteArith1Stmts : List Stmt :=
  checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
  checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
  [ .require (.binary .and (.binary .gt (.var "spot") (.intLit 0))
      (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))),
    .letDecl "milkFlip" (some addr) (.storage (ilksF (.var "ilk") "flip")),
    .letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")),
    .letDecl "milkDunk" (some uint256) (.storage (ilksF (.var "ilk") "dunk")) ] ++
  checkedSubUintInto "room" (.storage boxRef) (.storage litterRef) ++
  [ .require (.binary .and (.binary .lt (.storage litterRef) (.storage boxRef))
      (.binary .ge (.var "room") (.var "dust"))) ]

def biteArith2Stmts : List Stmt :=
  [ .internalCall "min" [.var "milkDunk", .var "room"] "dunkRoom" ] ++
  checkedMulUintInto "dunkRoomWad" (.var "dunkRoom") (.intLit WAD) ++
  [ .letDecl "dartDenomRate" (some uint256) (.binary .div (.var "dunkRoomWad") (.var "rate")),
    .letDecl "dartCandidate" (some uint256) (.binary .div (.var "dartDenomRate") (.var "milkChop")),
    .internalCall "min" [.var "art", .var "dartCandidate"] "dart" ] ++
  checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
  [ .letDecl "dinkCandidate" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
    .internalCall "min" [.var "ink", .var "dinkCandidate"] "dink",
    .require (.binary .and (.binary .gt (.var "dart") (.intLit 0))
      (.binary .gt (.var "dink") (.intLit 0))),
    .require (.binary .and (.binary .le (.var "dart") (.intLit int256Limit))
      (.binary .le (.var "dink") (.intLit int256Limit))) ]

def biteTailStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
    [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
      .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
  checkedMulUintInto "dartRate" (.var "dart") (.var "rate") ++
  checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "dartRate"] "_fessRet" ++
  checkedMulUintInto "tabBase" (.var "dartRate") (.var "milkChop") ++
  [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
  checkedAddUintInto "litterNew" (.storage litterRef) (.var "tab") ++
  [ .assign .storage litterRef (.var "litterNew") ] ++
  checkedExternalCallStmts (.var "milkFlip") "kick" (.intLit 0)
    [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0] "id" ++
  [ .return [.var "id"] ]

theorem biteBody_split :
    biteTransition.body =
      bitePreStmts ++ (biteArith1Stmts ++ (biteArith2Stmts ++ biteTailStmts)) := by
  simp only [biteTransition, bitePreStmts, biteArith1Stmts, biteArith2Stmts, biteTailStmts,
    nonpayable, checkedExternalCallStmts, checkedMulUintInto, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc, List.cons_append, List.nil_append]

/-! ## Prefix checkpoint: through `require(live == 1)` (passing) to `bsArt` -/

set_option maxHeartbeats 4000000 in
theorem catBiteSourcePreLive
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmIlk evmUrn : EVM.State}
    {ilksOut urnsOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec :
      config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := biteLocals I }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) bitePreStmts
      (.ok { contract := contract, locals := bsArt I iArt iRate iSpot iLine iDust ink art } evmUrn) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hIlksStmt :
      ExecStmt config { contract := contract, locals := biteLocals I } evm0
        (.externalCall (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk" (perm := false))
        (.ok { contract := contract, locals := bsIlk I iArt iRate iSpot iLine iDust } evmIlk) := by
    simpa [bsIlk, biteIlkTuple, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := biteLocals I }) (evm := evm0)
        (evm' := evmIlk) (receiver := .storage vatRef) (name := "ilks") (sendVal := 0)
        (target := biteVatAddr evm0) (args := [.var "ilk"]) (argVals := [biteIlkVal I])
        (out := ilksOut) (perm := false)
        (value := [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
        (biteVatRead (biteLocals_get_vat I))
        (by simp [evalExpr?, pure])
        (evalExprs_biteIlksArgs I (biteLocals_get_ilk I))
        hIlksCall hIlksDec
  have hRateStmt :
      ExecStmt config { contract := contract, locals := bsIlk I iArt iRate iSpot iLine iDust } evmIlk
        (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := bsRate I iArt iRate iSpot iLine iDust } evmIlk) :=
    biteTupleLet "vatIlk" "rate" (some uint256) 1 (bsIlk_get_vatIlk I _ _ _ _ _) (by rfl)
  have hSpotStmt :
      ExecStmt config { contract := contract, locals := bsRate I iArt iRate iSpot iLine iDust } evmIlk
        (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract, locals := bsSpot I iArt iRate iSpot iLine iDust } evmIlk) :=
    biteTupleLet "vatIlk" "spot" (some uint256) 2 (bsRate_get_vatIlk I _ _ _ _ _) (by rfl)
  have hDustStmt :
      ExecStmt config { contract := contract, locals := bsSpot I iArt iRate iSpot iLine iDust } evmIlk
        (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract, locals := bsDust I iArt iRate iSpot iLine iDust } evmIlk) :=
    biteTupleLet "vatIlk" "dust" (some uint256) 4 (bsSpot_get_vatIlk I _ _ _ _ _) (by rfl)
  have hUrnsStmt :
      ExecStmt config { contract := contract, locals := bsDust I iArt iRate iSpot iLine iDust } evmIlk
        (.externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", .var "urn"] "vatUrn"
          (perm := false))
        (.ok { contract := contract, locals := bsUrn I iArt iRate iSpot iLine iDust ink art } evmUrn) := by
    simpa [bsUrn, biteUrnTuple, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := bsDust I iArt iRate iSpot iLine iDust })
        (evm := evmIlk) (evm' := evmUrn) (receiver := .storage vatRef) (name := "urns") (sendVal := 0)
        (target := biteVatAddr evmIlk) (args := [.var "ilk", .var "urn"])
        (argVals := [biteIlkVal I, biteUrnVal I]) (out := urnsOut) (perm := false)
        (value := [bw ink, bw art])
        (biteVatRead (bsDust_get_vat I _ _ _ _ _))
        (by simp [evalExpr?, pure])
        (evalExprs_biteUrnsArgs I (bsDust_get_ilk I _ _ _ _ _) (bsDust_get_urn I _ _ _ _ _))
        hUrnsCall hUrnsDec
  have hInkStmt :
      ExecStmt config { contract := contract, locals := bsUrn I iArt iRate iSpot iLine iDust ink art } evmUrn
        (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := bsInk I iArt iRate iSpot iLine iDust ink art } evmUrn) :=
    biteTupleLet "vatUrn" "ink" (some uint256) 0 (bsUrn_get_vatUrn I _ _ _ _ _ _ _) (by rfl)
  have hArtStmt :
      ExecStmt config { contract := contract, locals := bsInk I iArt iRate iSpot iLine iDust ink art } evmUrn
        (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := bsArt I iArt iRate iSpot iLine iDust ink art } evmUrn) :=
    biteTupleLet "vatUrn" "art" (some uint256) 1 (bsInk_get_vatUrn I _ _ _ _ _ _ _) (by rfl)
  have hLiveReq :
      evalExpr? config { contract := contract, locals := bsArt I iArt iRate iSpot iLine iDust ink art }
        evmUrn (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    have hval :
        (Value.int (Int.ofNat (catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv).toNat) ==
          Value.int 1) = true := by rw [hlive]; rfl
    simp only [evalExpr?, biteLiveRead (bsArt_get_live I _ _ _ _ _ _ _), EvalResult.bind, bind,
      pure, evalBinaryOp?, hval]
  simp only [bitePreStmts, nonpayable, checkedExternalCallStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0))) ?_
  refine ExecBlock.consNormal hIlksStmt ?_
  refine ExecBlock.consNormal hRateStmt ?_
  refine ExecBlock.consNormal hSpotStmt ?_
  refine ExecBlock.consNormal hDustStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDust_get_vat I _ _ _ _ _) hvatCodeIlk)) ?_
  refine ExecBlock.consNormal hUrnsStmt ?_
  refine ExecBlock.consNormal hInkStmt ?_
  refine ExecBlock.consNormal hArtStmt ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hLiveReq) ExecBlock.nil

/-! ## Arithmetic checkpoint 1: `bsArt → bsRoom` -/

theorem catBiteSourceArith1 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    {evmUrn : EVM.State} {a r s l d ink art : UInt256}
    (hfitInkSpot : ink.toNat * s.toNat < UInt256.size)
    (hfitArtRate : art.toNat * r.toNat < UInt256.size)
    (hspotPos : 0 < s.toNat) (hratePos : 0 < r.toNat)
    (hunsafe : (ink * s).toNat < (art * r).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : d.toNat ≤ (biteRoomV evmUrn).toNat) :
    ExecBlock config { contract := contract, locals := bsArt I a r s l d ink art } evmUrn
      biteArith1Stmts
      (.ok { contract := contract, locals := bsRoom I evmUrn a r s l d ink art } evmUrn) := by
  have hroomLeBox : (biteRoomV evmUrn).toNat ≤ (biteBoxW evmUrn).toNat := by
    simp only [biteRoomV]; rw [usub_toNat (le_of_lt hlitLtBox)]; exact Nat.sub_le _ _
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I a r s l d ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I a r s l d ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkSpot_get_ink I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn a r s l d ink art))
      (bsInkSpot_get_inkSpot I evmUrn a r s l d ink art) rfl hfitInkSpot hspotPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn a r s l d ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsArtRate_get_art I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn a r s l d ink art))
      (bsArtRate_get_artRateUnsafe I evmUrn a r s l d ink art) rfl hfitArtRate
      hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true (evalExpr_gtLit_true (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn a r s l d ink art))
        (by simpa using hspotPos))
      (evalExpr_lt_uint256_true (evalExpr_varUInt256 (bsArtRate_get_inkSpot I evmUrn a r s l d ink art))
        (evalExpr_varUInt256 (bsArtRate_get_artRateUnsafe I evmUrn a r s l d ink art)) hunsafe))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteFlipRead hsz36 (bsArtRate_get_ilks I evmUrn a r s l d ink art)
      (bsArtRate_get_ilk I evmUrn a r s l d ink art))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteChopRead hsz36 (bsMilkFlip_get_ilks I evmUrn a r s l d ink art)
      (bsMilkFlip_get_ilk I evmUrn a r s l d ink art))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteDunkRead hsz36 (bsMilkChop_get_ilks I evmUrn a r s l d ink art)
      (bsMilkChop_get_ilk I evmUrn a r s l d ink art))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sub256_ok (biteBoxRead (bsMilkDunk_get_box I evmUrn a r s l d ink art))
      (biteLitterRead (bsMilkDunk_get_litter I evmUrn a r s l d ink art)) rfl
      (le_of_lt hlitLtBox))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_le_uint256_true (evalExpr_varUInt256 (bsRoom_get_room I evmUrn a r s l d ink art))
      (biteBoxRead (bsRoom_get_box I evmUrn a r s l d ink art)) hroomLeBox)) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true
      (evalExpr_lt_uint256_true (biteLitterRead (bsRoom_get_litter I evmUrn a r s l d ink art))
        (biteBoxRead (bsRoom_get_box I evmUrn a r s l d ink art)) hlitLtBox)
      (evalExpr_ge_uint256_true (evalExpr_varUInt256 (bsRoom_get_room I evmUrn a r s l d ink art))
        (evalExpr_varUInt256 (bsRoom_get_dust I evmUrn a r s l d ink art)) hroomGeDust)))
    ExecBlock.nil

/-! ## Arithmetic checkpoint 2: `bsRoom → bsDink` -/

theorem catBiteSourceArith2 {I : ExecutionEnv} {evmUrn : EVM.State} {a r s l d ink art : UInt256}
    (hratePos : 0 < r.toNat) (hartPos : 0 < art.toNat)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn r art).toNat < UInt256.size)
    (hdartPos : 0 < (biteDartV I evmUrn r art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn r art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn r art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn r art ink).toNat ≤ int256Limit) :
    ExecBlock config { contract := contract, locals := bsRoom I evmUrn a r s l d ink art } evmUrn
      biteArith2Stmts
      (.ok { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn) := by
  simp only [biteArith2Stmts, checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (execMinCall (bsRoom_get_milkDunk I evmUrn a r s l d ink art)
      (bsRoom_get_room I evmUrn a r s l d ink art)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok
      (evalExpr_varUInt256 (bsDunkRoom_get_dunkRoom I evmUrn a r s l d ink art))
      evalExpr_wad rfl hfitDunkRoomWad)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoom I evmUrn a r s l d ink art))
      evalExpr_wad (bsDunkRoomWad_get_dunkRoomWad I evmUrn a r s l d ink art) rfl
      hfitDunkRoomWad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoomWad I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsDunkRoomWad_get_rate I evmUrn a r s l d ink art)) hratePos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsDartDenom_get_dartDenomRate I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsDartDenom_get_milkChop I evmUrn a r s l d ink art)) hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (execMinCall (bsDartCand_get_art I evmUrn a r s l d ink art)
      (bsDartCand_get_dartCandidate I evmUrn a r s l d ink art)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsDart_get_ink I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsDart_get_dart I evmUrn a r s l d ink art)) rfl hfitInkDart)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkDart_get_ink I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsInkDart_get_dart I evmUrn a r s l d ink art))
      (bsInkDart_get_inkDart I evmUrn a r s l d ink art) rfl hfitInkDart hdartPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsInkDart_get_inkDart I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (bsInkDart_get_art I evmUrn a r s l d ink art)) hartPos)) ?_
  refine ExecBlock.consNormal
    (execMinCall (bsDinkCand_get_ink I evmUrn a r s l d ink art)
      (bsDinkCand_get_dinkCandidate I evmUrn a r s l d ink art)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn a r s l d ink art))
        (by simpa using hdartPos))
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dink I evmUrn a r s l d ink art))
        (by simpa using hdinkPos)))) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true
      (evalExpr_leLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn a r s l d ink art)) hdartLim)
      (evalExpr_leLit_true (evalExpr_varUInt256 (bsDink_get_dink I evmUrn a r s l d ink art)) hdinkLim)))
    ExecBlock.nil

/-! ## Tail (grab / fess / assign litter / kick → return) -/

/-- The `vow` address as read by `biteVowRead` at an EVM state. -/
abbrev biteVowAddrV (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (catSlotWord ⟨4⟩ evm.accountMap evm.executionEnv) solcAddrMask).toNat

theorem evalExpr_vowAddr {evm : EVM.State} {locals : Store} (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm vowAddr =
      .ok (.address (biteVowAddrV evm)) := biteVowRead hbase

theorem evalExpr_varAddr {evm : EVM.State} {locals : Store} {name : Ident} {ad : AccountAddress}
    (h : locals.get? name = some (.address ad)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.address ad) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = _
  rw [h]; rfl

theorem evalExpr_intLit {evm : EVM.State} {locals : Store} (n : Int) :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit n) = .ok (.int n) := by
  simp [evalExpr?, pure]

/-- The `grab(ilk, urn, this, vow, -dink, -dart)` argument list evaluated at `bsDink`. -/
theorem biteGrabArgsEval (I : ExecutionEnv) (evmUrn : EVM.State) (a r s l d ink art : UInt256) :
    evalExprs? config { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn
      [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
        .unary .neg (asInt256 (.var "dart")) ] =
      .ok [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
        .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
        .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))] := by
  simp [evalExprs?, evalExpr_biteIlk I (bsDink_get_ilk I evmUrn a r s l d ink art),
    evalExpr_biteUrn I (bsDink_get_urn I evmUrn a r s l d ink art), evalExpr_this,
    evalExpr_vowAddr (bsDink_get_vow I evmUrn a r s l d ink art),
    evalExpr_negInt256_var (bsDink_get_dink I evmUrn a r s l d ink art),
    evalExpr_negInt256_var (bsDink_get_dart I evmUrn a r s l d ink art),
    EvalResult.bind, bind, pure]

/-- The `grab` external call succeeding (`bsDink → btGrab`). -/
theorem biteGrabSuccessStmt {I : ExecutionEnv} {evmUrn evmGrab : EVM.State} {grabOut : ByteArray}
    {a r s l d ink art : UInt256}
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some []) :
    ExecStmt config { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn
      (.externalCall (.storage vatRef) "grab" (.intLit 0)
        [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
          .unary .neg (asInt256 (.var "dart")) ] "_grabRet" (perm := true))
      (.ok { contract := contract, locals := btGrab I evmUrn a r s l d ink art } evmGrab) := by
  simpa [btGrab, collapseReturns] using
    ExecStmt.externalCallSuccess
      (cfg := config) (solm := { contract := contract, locals := bsDink I evmUrn a r s l d ink art })
      (evm := evmUrn) (evm' := evmGrab) (receiver := .storage vatRef) (name := "grab") (sendVal := 0)
      (target := biteVatAddr evmUrn)
      (args := [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
          .unary .neg (asInt256 (.var "dart")) ])
      (argVals := [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
        .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
        .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))]) (out := grabOut) (perm := true)
      (value := []) (biteVatRead (bsDink_get_vat I evmUrn a r s l d ink art)) (by simp [evalExpr?, pure])
      (biteGrabArgsEval I evmUrn a r s l d ink art) hGrabCall hGrabDec

/-- The `fess` external call succeeding (`btDartRate → btFess`). -/
theorem biteFessSuccessStmt {I : ExecutionEnv} {evmUrn evmGrab evmFess : EVM.State}
    {fessOut : ByteArray} {a r s l d ink art : UInt256}
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn r art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some []) :
    ExecStmt config { contract := contract, locals := btDartRate I evmUrn a r s l d ink art } evmGrab
      (.externalCall vowAddr "fess" (.intLit 0) [.var "dartRate"] "_fessRet" (perm := true))
      (.ok { contract := contract, locals := btFess I evmUrn a r s l d ink art } evmFess) := by
  simpa [btFess, collapseReturns] using
    ExecStmt.externalCallSuccess
      (cfg := config) (solm := { contract := contract, locals := btDartRate I evmUrn a r s l d ink art })
      (evm := evmGrab) (evm' := evmFess) (receiver := vowAddr) (name := "fess") (sendVal := 0)
      (target := biteVowAddrV evmGrab) (args := [.var "dartRate"])
      (argVals := [bw (biteDartRateV I evmUrn r art)]) (out := fessOut) (perm := true) (value := [])
      (biteVowRead (btDartRate_get_vow I evmUrn a r s l d ink art)) (by simp [evalExpr?, pure])
      (by simp [evalExprs?, evalExpr_varUInt256 (btDartRate_get_dartRate I evmUrn a r s l d ink art),
        EvalResult.bind, bind, pure]) hFessCall hFessDec

/-- The `kick(urn, vow, tab, dink, 0)` argument list evaluated at `btLitterNew` (state `evmLit`). -/
theorem biteKickArgsEval (I : ExecutionEnv) (evmUrn evmFess evmLit : EVM.State)
    (a r s l d ink art : UInt256) :
    evalExprs? config
      { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art } evmLit
      [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0] =
      .ok [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn r art),
        bw (biteDinkV I evmUrn r art ink), .int 0] := by
  simp [evalExprs?, evalExpr_biteUrn I (btLitterNew_get_urn I evmUrn evmFess a r s l d ink art),
    evalExpr_vowAddr (btLitterNew_get_vow I evmUrn evmFess a r s l d ink art),
    evalExpr_varUInt256 (btLitterNew_get_tab I evmUrn evmFess a r s l d ink art),
    evalExpr_varUInt256 (btLitterNew_get_dink I evmUrn evmFess a r s l d ink art),
    evalExpr_intLit, EvalResult.bind, bind, pure]

set_option maxHeartbeats 4000000 in
theorem catBiteSourceTail {I : ExecutionEnv}
    {evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
    {grabOut fessOut kickOut : ByteArray} {a r s l d ink art id : UInt256}
    (hratePos : 0 < r.toNat) (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitDartRate : (biteDartV I evmUrn r art).toNat * r.toNat < UInt256.size)
    (hfitTabBase : (biteDartRateV I evmUrn r art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn r art).toNat < UInt256.size)
    (hvatCodeMid :
      0 < (UInt256.ofNat
        ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn r art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess r art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn r art),
          bw (biteDinkV I evmUrn r art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = some [bw id]) :
    ExecBlock config { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn
      biteTailStmts
      (.returned { contract := contract, locals := btKick I evmUrn evmFess a r s l d ink art id }
        evmKick (some [bw id])) := by
  -- grab args
  have hGrabArgs :
      evalExprs? config { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn
        [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
          .unary .neg (asInt256 (.var "dart")) ] =
        .ok [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))] := by
    simp [evalExprs?, evalExpr_biteIlk I (bsDink_get_ilk I evmUrn a r s l d ink art),
      evalExpr_biteUrn I (bsDink_get_urn I evmUrn a r s l d ink art), evalExpr_this,
      evalExpr_vowAddr (bsDink_get_vow I evmUrn a r s l d ink art),
      evalExpr_negInt256_var (bsDink_get_dink I evmUrn a r s l d ink art),
      evalExpr_negInt256_var (bsDink_get_dart I evmUrn a r s l d ink art),
      EvalResult.bind, bind, pure]
  have hGrabStmt :
      ExecStmt config { contract := contract, locals := bsDink I evmUrn a r s l d ink art } evmUrn
        (.externalCall (.storage vatRef) "grab" (.intLit 0)
          [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
            .unary .neg (asInt256 (.var "dart")) ] "_grabRet" (perm := true))
        (.ok { contract := contract, locals := btGrab I evmUrn a r s l d ink art } evmGrab) := by
    simpa [btGrab, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := bsDink I evmUrn a r s l d ink art })
        (evm := evmUrn) (evm' := evmGrab) (receiver := .storage vatRef) (name := "grab") (sendVal := 0)
        (target := biteVatAddr evmUrn)
        (args := [ .var "ilk", .var "urn", thisAddr, vowAddr, .unary .neg (asInt256 (.var "dink")),
            .unary .neg (asInt256 (.var "dart")) ])
        (argVals := [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn r art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn r art).toNat))])
        (out := grabOut) (perm := true) (value := [])
        (biteVatRead (bsDink_get_vat I evmUrn a r s l d ink art)) (by simp [evalExpr?, pure])
        hGrabArgs hGrabCall hGrabDec
  have hFessStmt :
      ExecStmt config { contract := contract, locals := btDartRate I evmUrn a r s l d ink art } evmGrab
        (.externalCall vowAddr "fess" (.intLit 0) [.var "dartRate"] "_fessRet" (perm := true))
        (.ok { contract := contract, locals := btFess I evmUrn a r s l d ink art } evmFess) := by
    simpa [btFess, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := btDartRate I evmUrn a r s l d ink art })
        (evm := evmGrab) (evm' := evmFess) (receiver := vowAddr) (name := "fess") (sendVal := 0)
        (target := biteVowAddrV evmGrab) (args := [.var "dartRate"])
        (argVals := [bw (biteDartRateV I evmUrn r art)]) (out := fessOut) (perm := true) (value := [])
        (biteVowRead (btDartRate_get_vow I evmUrn a r s l d ink art)) (by simp [evalExpr?, pure])
        (by simp [evalExprs?, evalExpr_varUInt256 (btDartRate_get_dartRate I evmUrn a r s l d ink art),
          EvalResult.bind, bind, pure])
        hFessCall hFessDec
  have hMilkFlipVal :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art }
        evmLit (.var "milkFlip") = .ok (.address (biteFlipAddrV I evmUrn)) :=
    evalExpr_varAddr (btLitterNew_get_milkFlip I evmUrn evmFess a r s l d ink art)
  have hKickGuard :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art }
        evmLit (.binary .gt (.extCodeSize (.var "milkFlip")) (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hMilkFlipVal, evalBinaryOp?, EVM.Word.ofNat, hflipCode]
  have hKickArgs :
      evalExprs? config
        { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art } evmLit
        [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0] =
        .ok [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn r art),
          bw (biteDinkV I evmUrn r art ink), .int 0] := by
    simp [evalExprs?, evalExpr_biteUrn I (btLitterNew_get_urn I evmUrn evmFess a r s l d ink art),
      evalExpr_vowAddr (btLitterNew_get_vow I evmUrn evmFess a r s l d ink art),
      evalExpr_varUInt256 (btLitterNew_get_tab I evmUrn evmFess a r s l d ink art),
      evalExpr_varUInt256 (btLitterNew_get_dink I evmUrn evmFess a r s l d ink art),
      evalExpr_intLit, EvalResult.bind, bind, pure]
  have hKickStmt :
      ExecStmt config
        { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art } evmLit
        (.externalCall (.var "milkFlip") "kick" (.intLit 0)
          [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0] "id" (perm := true))
        (.ok { contract := contract, locals := btKick I evmUrn evmFess a r s l d ink art id } evmKick) := by
    simpa [btKick, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config)
        (solm := { contract := contract, locals := btLitterNew I evmUrn evmFess a r s l d ink art })
        (evm := evmLit) (evm' := evmKick) (receiver := .var "milkFlip") (name := "kick") (sendVal := 0)
        (target := biteFlipAddrV I evmUrn)
        (args := [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0])
        (argVals := [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn r art),
          bw (biteDinkV I evmUrn r art ink), .int 0]) (out := kickOut) (perm := true) (value := [bw id])
        hMilkFlipVal (by simp [evalExpr?, pure]) hKickArgs hKickCall hKickDec
  -- assemble
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn a r s l d ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal hGrabStmt ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn a r s l d ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn a r s l d ink art))
      (btDartRate_get_dartRate I evmUrn a r s l d ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn a r s l d ink art) hvowCode)) ?_
  refine ExecBlock.consNormal hFessStmt ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btFess_get_dartRate I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (btFess_get_milkChop I evmUrn a r s l d ink art)) rfl hfitTabBase)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btTabBase_get_dartRate I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (btTabBase_get_milkChop I evmUrn a r s l d ink art))
      (btTabBase_get_tabBase I evmUrn a r s l d ink art) rfl hfitTabBase hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok (evalExpr_varUInt256 (btTabBase_get_tabBase I evmUrn a r s l d ink art))
      evalExpr_wad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_add256_ok (biteLitterRead (btTab_get_litter I evmUrn a r s l d ink art))
      (evalExpr_varUInt256 (btTab_get_tab I evmUrn a r s l d ink art)) rfl hfitLitterNew)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess a r s l d ink art))
      (biteLitterRead (btLitterNew_get_litter I evmUrn evmFess a r s l d ink art))
      (by simp only [biteLitterNewV]; rw [uadd_toNat, Nat.mod_eq_of_lt hfitLitterNew];
          exact Nat.le_add_right _ _))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess a r s l d ink art))
      (assignStorageRef_storage_scalar (er := { base := "litter", steps := [] }) (ty := uint256St)
        (loc := wordLoc ⟨6⟩) (btLitterNew_get_litter I evmUrn evmFess a r s l d ink art)
        (by simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St])
        rfl hLitStore)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hKickGuard) ?_
  refine ExecBlock.consNormal hKickStmt ?_
  exact ExecBlock.consReturn (ExecStmt.return
    (evalExprs?_singleton (evalExpr_varUInt256 (btKick_get_id I evmUrn evmFess a r s l d ink art id))))

/-! ## The full `bite` source-body success path -/

set_option maxHeartbeats 4000000 in
theorem catBiteSourceSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmIlk evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
    {ilksOut urnsOut grabOut fessOut kickOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art id : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hwv : I.weiValue = ⟨0⟩)
    -- ilks / urns view calls
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    -- arithmetic side-conditions
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat) (hartPos : 0 < art.toNat)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
    -- grab / fess / assign / kick
    (hvatCodeMid :
      0 < (UInt256.ofNat
        ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = some [bw id]) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body
      (.returned
        { contract := contract,
          locals := btKick I evmUrn evmFess iArt iRate iSpot iLine iDust ink art id }
        evmKick (some [bw id])) := by
  rw [ExecTransitionBody, biteBody_split]
  exact ExecFuncBody.execBlockRet
    (execBlock_append
      (catBiteSourcePreLive hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive)
      (execBlock_append
        (catBiteSourceArith1 hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox
          hroomGeDust)
        (execBlock_append
          (catBiteSourceArith2 hratePos hartPos hmilkChopPos hfitDunkRoomWad hfitInkDart hdartPos
            hdinkPos hdartLim hdinkLim)
          (catBiteSourceTail hratePos hmilkChopPos hfitDartRate hfitTabBase hfitLitterNew hvatCodeMid
            hGrabCall hGrabDec hvowCode hFessCall hFessDec hLitStore hflipCode hKickCall hKickDec))))

/-! ## Revert branches

Each threads `catBiteSourcePreLive` (+ arith checkpoints as needed), then diverges: an overflow
`.letDeclRevert`, a `/0` `.letDeclRevert`, a failing `require`, or a failed external call. -/

/-- The `checkedMul` guard `y == 0 || …` is `true` when `y = 0` (short-circuit). -/
theorem evalExpr_checkedMulCheck_yzero {evm : EVM.State} {locals : Store} {y rhs : Expr}
    {b : UInt256}
    (hy : evalExpr? config { contract := contract, locals := locals } evm y = .ok (bw b))
    (hb : b.toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .or (.binary .eq y (.intLit 0)) rhs) = .ok (.bool true) := by
  have hb0 : (bw b == Value.int 0) = true := by simp only [bw]; rw [hb]; rfl
  simp only [evalExpr?, EvalResult.bind, bind, hy, evalBinaryOp?, pure, hb0]

section Reverts
variable {cA gh bl σ σ₀ A I} {g : UInt256}
  {evmIlk evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
  {ilksOut urnsOut grabOut fessOut kickOut : ByteArray}
  {iArt iRate iSpot iLine iDust ink art : UInt256}
  (hwv : I.weiValue = ⟨0⟩)
  (hvatCode0 :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
  (hIlksCall :
    typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
      "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
  (hIlksDec :
    config.externalABI.decode? "ilks" ilksOut =
      some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
  (hvatCodeIlk :
    0 < (UInt256.ofNat
      ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
  (hUrnsCall :
    typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
      "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
  (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
  (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)

include hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive

/-- Reduce a body-revert goal to a revert of the arith₁ suffix (after `bsArt`). -/
private theorem biteRevert_afterPre
    (hblk : ExecBlock config { contract := contract, locals := bsArt I iArt iRate iSpot iLine iDust ink art }
      evmUrn (biteArith1Stmts ++ (biteArith2Stmts ++ biteTailStmts)) .reverted) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  rw [ExecTransitionBody, biteBody_split]
  exact ExecFuncBody.execBlockRevert
    (execBlock_append
      (catBiteSourcePreLive hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive)
      hblk)

theorem catBiteSourceInkSpotOverflowRevert
    (hover : UInt256.size ≤ ink.toNat * iSpot.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) hover))

theorem catBiteSourceArtRateOverflowRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size) (hspotPos : 0 < iSpot.toNat)
    (hover : UInt256.size ≤ art.toNat * iRate.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkSpot_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsInkSpot_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitInkSpot hspotPos)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) hover))

/-- **`artRate = art*rate` overflow revert with `spot = 0`.** Dual of `catBiteSourceArtRateOverflowRevert`
when `spot = 0` (the `inkSpot` `checkedMul` check passes via `_yzero`); the EVM short-circuits at the
`spot > 0` conjunct but Solm evaluates `art*rate` first and reverts on its overflow. -/
theorem catBiteSourceArtRateOverflowSpotZeroRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size) (hspot0 : iSpot.toNat = 0)
    (hover : UInt256.size ≤ art.toNat * iRate.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      hspot0)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) hover))

theorem catBiteSourceSpotZeroRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hratePos : 0 < iRate.toNat) (hspot0 : iSpot.toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      hspot0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsArtRate_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitArtRate hratePos)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseL (evalExpr_gtLit_false (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (by rw [hspot0]; decide))))

/-- **`spot = 0` revert with `rate = 0`.** Dual of `catBiteSourceSpotZeroRevert` when the
`artRate = art*rate` `checkedMul`'s multiplier is also zero (`_yzero`). -/
theorem catBiteSourceSpotZeroRateZeroRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hrate0 : iRate.toNat = 0) (hspot0 : iSpot.toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      hspot0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      hrate0)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseL (evalExpr_gtLit_false (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (by rw [hspot0]; decide))))

theorem catBiteSourceInkSpotGeRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hge : (art * iRate).toNat ≤ (ink * iSpot).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkSpot_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsInkSpot_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitInkSpot hspotPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsArtRate_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitArtRate hratePos)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseR
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hspotPos))
      (evalExpr_lt_uint256_false (evalExpr_varUInt256 (bsArtRate_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art)) hge)))

/-- **`ink*spot ≥ art*rate` revert with `rate = 0`.** Dual of `catBiteSourceInkSpotGeRevert` when the
`artRate = art*rate` `checkedMul`'s multiplier is zero (its overflow check passes trivially via
`_yzero`).  Reachable at the `unsafe` guard because `rate = 0 ⇒ art*rate = 0 ≥ ink*spot` fails the
`ink*spot < art*rate` conjunct. -/
theorem catBiteSourceInkSpotGeRateZeroRevert
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hrate0 : iRate.toNat = 0)
    (hge : (art * iRate).toNat ≤ (ink * iSpot).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive ?_
  simp only [biteArith1Stmts, checkedMulUintInto, checkedSubUintInto, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkSpot_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsInkSpot_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitInkSpot hspotPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      hrate0)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseR
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hspotPos))
      (evalExpr_lt_uint256_false (evalExpr_varUInt256 (bsArtRate_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art)) hge)))

/-- The passing arith₁ prefix through `milkDunk` (before the `room` subtraction). -/
private theorem biteArith1ToMilk (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat) {rest : List Stmt}
    (hdiv : ExecBlock config { contract := contract, locals := bsMilkDunk I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn (checkedSubUintInto "room" (.storage boxRef) (.storage litterRef) ++
        [ .require (.binary .and (.binary .lt (.storage litterRef) (.storage boxRef))
            (.binary .ge (.var "room") (.var "dust"))) ] ++ rest) .reverted) :
    ExecBlock config { contract := contract, locals := bsArt I iArt iRate iSpot iLine iDust ink art }
      evmUrn (biteArith1Stmts ++ rest) .reverted := by
  simp only [biteArith1Stmts, checkedMulUintInto, List.append_assoc, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsArt_get_ink I iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArt_get_spot I iArt iRate iSpot iLine iDust ink art)) rfl hfitInkSpot)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkSpot_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsInkSpot_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitInkSpot hspotPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsInkSpot_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkSpot_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitArtRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsArtRate_get_art I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsArtRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitArtRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true (evalExpr_gtLit_true (evalExpr_varUInt256 (bsArtRate_get_spot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hspotPos))
      (evalExpr_lt_uint256_true (evalExpr_varUInt256 (bsArtRate_get_inkSpot I evmUrn iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (bsArtRate_get_artRateUnsafe I evmUrn iArt iRate iSpot iLine iDust ink art)) hunsafe))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteFlipRead hsz36 (bsArtRate_get_ilks I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsArtRate_get_ilk I evmUrn iArt iRate iSpot iLine iDust ink art))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteChopRead hsz36 (bsMilkFlip_get_ilks I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsMilkFlip_get_ilk I evmUrn iArt iRate iSpot iLine iDust ink art))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (biteDunkRead hsz36 (bsMilkChop_get_ilks I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsMilkChop_get_ilk I evmUrn iArt iRate iSpot iLine iDust ink art))) ?_
  simpa only [List.append_assoc] using hdiv

theorem catBiteSourceRoomUnderflowRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitGtBox : (biteBoxW evmUrn).toNat < (biteLitW evmUrn).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    (biteArith1ToMilk hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive hsz36
      hfitInkSpot hfitArtRate hspotPos hratePos hunsafe ?_)
  simp only [checkedSubUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_sub256_revert (biteBoxRead (bsMilkDunk_get_box I evmUrn iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (bsMilkDunk_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art)) hlitGtBox))

theorem catBiteSourceLitterGeBoxRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitEqBox : (biteLitW evmUrn).toNat = (biteBoxW evmUrn).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  have hle : (biteLitW evmUrn).toNat ≤ (biteBoxW evmUrn).toNat := le_of_eq hlitEqBox
  have hroomLeBox : (biteRoomV evmUrn).toNat ≤ (biteBoxW evmUrn).toNat := by
    simp only [biteRoomV]; rw [usub_toNat hle]; exact Nat.sub_le _ _
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    (biteArith1ToMilk hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive hsz36
      hfitInkSpot hfitArtRate hspotPos hratePos hunsafe ?_)
  simp only [checkedSubUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sub256_ok (biteBoxRead (bsMilkDunk_get_box I evmUrn iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (bsMilkDunk_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hle)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_le_uint256_true (evalExpr_varUInt256 (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art))
      (biteBoxRead (bsRoom_get_box I evmUrn iArt iRate iSpot iLine iDust ink art)) hroomLeBox)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseL
      (evalExpr_lt_uint256_false (biteLitterRead (bsRoom_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art))
        (biteBoxRead (bsRoom_get_box I evmUrn iArt iRate iSpot iLine iDust ink art)) (le_of_eq hlitEqBox.symm))))

theorem catBiteSourceRoomLtDustRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomLtDust : (biteRoomV evmUrn).toNat < iDust.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  have hroomLeBox : (biteRoomV evmUrn).toNat ≤ (biteBoxW evmUrn).toNat := by
    simp only [biteRoomV]; rw [usub_toNat (le_of_lt hlitLtBox)]; exact Nat.sub_le _ _
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    (biteArith1ToMilk hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive hsz36
      hfitInkSpot hfitArtRate hspotPos hratePos hunsafe ?_)
  simp only [checkedSubUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sub256_ok (biteBoxRead (bsMilkDunk_get_box I evmUrn iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (bsMilkDunk_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl (le_of_lt hlitLtBox))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_le_uint256_true (evalExpr_varUInt256 (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art))
      (biteBoxRead (bsRoom_get_box I evmUrn iArt iRate iSpot iLine iDust ink art)) hroomLeBox)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseR
      (evalExpr_lt_uint256_true (biteLitterRead (bsRoom_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art))
        (biteBoxRead (bsRoom_get_box I evmUrn iArt iRate iSpot iLine iDust ink art)) hlitLtBox)
      (evalExpr_ge_uint256_false (evalExpr_varUInt256 (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art))
        (evalExpr_varUInt256 (bsRoom_get_dust I evmUrn iArt iRate iSpot iLine iDust ink art)) hroomLtDust)))

/-- Reduce a body-revert goal to a revert of the arith₂ suffix (after `bsRoom`). -/
private theorem biteRevert_afterArith1 (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hblk : ExecBlock config { contract := contract, locals := bsRoom I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn (biteArith2Stmts ++ biteTailStmts) .reverted) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterPre hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    (execBlock_append (catBiteSourceArith1 hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe
      hlitLtBox hroomGeDust) hblk)

theorem catBiteSourceDunkRoomWadOverflowRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hover : UInt256.size ≤ (biteDunkRoomV I evmUrn).toNat * wadU.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust ?_
  simp only [biteArith2Stmts, checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (execMinCall (bsRoom_get_milkDunk I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (bsDunkRoom_get_dunkRoom I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad hover))

theorem catBiteSourceMilkChopZeroRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChop0 : (biteChopW I evmUrn).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust ?_
  simp only [biteArith2Stmts, checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (execMinCall (bsRoom_get_milkDunk I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok
      (evalExpr_varUInt256 (bsDunkRoom_get_dunkRoom I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad rfl hfitDunkRoomWad)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoom I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad (bsDunkRoomWad_get_dunkRoomWad I evmUrn iArt iRate iSpot iLine iDust ink art) rfl
      hfitDunkRoomWad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoomWad I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDunkRoomWad_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) hratePos)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_div256_revert (evalExpr_varUInt256 (bsDartDenom_get_dartDenomRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDartDenom_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) hmilkChop0))

/-- The passing arith₂ prefix `bsRoom → bsDart` (min(dunkRoom) … min(dart)), leaving the remaining
    arith₂ statements to a continuation.  Used by the arith₂ reverts. -/
private theorem biteArith2ToDart
    (hratePos : 0 < iRate.toNat) (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size) {result : ExecResult}
    (hdiv : ExecBlock config { contract := contract, locals := bsDart I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dinkCandidate" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
          .internalCall "min" [.var "ink", .var "dinkCandidate"] "dink",
          .require (.binary .and (.binary .gt (.var "dart") (.intLit 0))
            (.binary .gt (.var "dink") (.intLit 0))),
          .require (.binary .and (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++ biteTailStmts) result) :
    ExecBlock config { contract := contract, locals := bsRoom I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn (biteArith2Stmts ++ biteTailStmts) result := by
  simp only [biteArith2Stmts, checkedMulUintInto, List.cons_append, List.nil_append,
    List.append_assoc]
  refine ExecBlock.consNormal
    (execMinCall (bsRoom_get_milkDunk I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsRoom_get_room I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok
      (evalExpr_varUInt256 (bsDunkRoom_get_dunkRoom I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad rfl hfitDunkRoomWad)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoom I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad (bsDunkRoomWad_get_dunkRoomWad I evmUrn iArt iRate iSpot iLine iDust ink art) rfl
      hfitDunkRoomWad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsDunkRoomWad_get_dunkRoomWad I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDunkRoomWad_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) hratePos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsDartDenom_get_dartDenomRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDartDenom_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (execMinCall (bsDartCand_get_art I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsDartCand_get_dartCandidate I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  simpa only [checkedMulUintInto, List.append_assoc, List.cons_append, List.nil_append] using hdiv

theorem catBiteSourceInkDartOverflowRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hover : UInt256.size ≤ ink.toNat * (biteDartV I evmUrn iRate art).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    (biteArith2ToDart hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
      hratePos hmilkChopPos hfitDunkRoomWad ?_)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (bsDart_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDart_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art)) hover))

theorem catBiteSourceDartZeroRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdart0 : (biteDartV I evmUrn iRate art).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    (biteArith2ToDart hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
      hratePos hmilkChopPos hfitDunkRoomWad ?_)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsDart_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDart_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitInkDart)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_yzero (evalExpr_varUInt256 (bsInkDart_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      hdart0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsInkDart_get_inkDart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkDart_get_art I evmUrn iArt iRate iSpot iLine iDust ink art)) hartPos)) ?_
  refine ExecBlock.consNormal
    (execMinCall (bsDinkCand_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsDinkCand_get_dinkCandidate I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseL (evalExpr_gtLit_false (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (by rw [hdart0]; decide))))

/-- The passing arith₂ segment `bsDart → bsDink` (checkedMul inkDart, dinkCandidate, min(dink)),
    leaving the two final `require`s to a continuation. -/
private theorem biteArith2DartToDink
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    {result : ExecResult}
    (hdiv : ExecBlock config { contract := contract, locals := bsDink I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn
      ([ .require (.binary .and (.binary .gt (.var "dart") (.intLit 0))
          (.binary .gt (.var "dink") (.intLit 0))),
        .require (.binary .and (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++ biteTailStmts) result) :
    ExecBlock config { contract := contract, locals := bsDart I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dinkCandidate" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
          .internalCall "min" [.var "ink", .var "dinkCandidate"] "dink",
          .require (.binary .and (.binary .gt (.var "dart") (.intLit 0))
            (.binary .gt (.var "dink") (.intLit 0))),
          .require (.binary .and (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++ biteTailStmts) result := by
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (bsDart_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsDart_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitInkDart)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (bsInkDart_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkDart_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (bsInkDart_get_inkDart I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitInkDart hdartPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok
      (evalExpr_varUInt256 (bsInkDart_get_inkDart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (bsInkDart_get_art I evmUrn iArt iRate iSpot iLine iDust ink art)) hartPos)) ?_
  refine ExecBlock.consNormal
    (execMinCall (bsDinkCand_get_ink I evmUrn iArt iRate iSpot iLine iDust ink art)
      (bsDinkCand_get_dinkCandidate I evmUrn iArt iRate iSpot iLine iDust ink art)) ?_
  exact hdiv

/-- Common wrapper: full arith₂ up to `bsDink`, then a continuation over the two final `require`s. -/
private theorem biteRevert_atFinalRequires (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdiv : ExecBlock config { contract := contract, locals := bsDink I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn
      ([ .require (.binary .and (.binary .gt (.var "dart") (.intLit 0))
          (.binary .gt (.var "dink") (.intLit 0))),
        .require (.binary .and (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++ biteTailStmts) .reverted) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted :=
  biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    (biteArith2ToDart hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
      hratePos hmilkChopPos hfitDunkRoomWad
      (biteArith2DartToDink hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
        hfitInkDart hartPos hdartPos hdiv))

theorem catBiteSourceDinkZeroRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdink0 : (biteDinkV I evmUrn iRate art ink).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_atFinalRequires hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec
    hlive hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    hfitDunkRoomWad hmilkChopPos hfitInkDart hartPos hdartPos ?_
  simp only [List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseR
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hdartPos))
      (evalExpr_gtLit_false (evalExpr_varUInt256 (bsDink_get_dink I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by rw [hdink0]; decide))))

theorem catBiteSourceDartLimitRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartGtLim : int256Limit < Int.ofNat (biteDartV I evmUrn iRate art).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_atFinalRequires hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec
    hlive hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    hfitDunkRoomWad hmilkChopPos hfitInkDart hartPos hdartPos ?_
  simp only [List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hdartPos))
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dink I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hdinkPos)))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseL (evalExpr_leLit_false (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      hdartGtLim)))

theorem catBiteSourceDinkLimitRevert (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkGtLim : int256Limit < Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_atFinalRequires hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec
    hlive hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    hfitDunkRoomWad hmilkChopPos hfitInkDart hartPos hdartPos ?_
  simp only [List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_and_true
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hdartPos))
      (evalExpr_gtLit_true (evalExpr_varUInt256 (bsDink_get_dink I evmUrn iArt iRate iSpot iLine iDust ink art))
        (by simpa using hdinkPos)))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_and_falseR
      (evalExpr_leLit_true (evalExpr_varUInt256 (bsDink_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art)) hdartLim)
      (evalExpr_leLit_false (evalExpr_varUInt256 (bsDink_get_dink I evmUrn iArt iRate iSpot iLine iDust ink art))
        hdinkGtLim)))

/-- Reduce a body-revert goal to a revert of the tail suffix (after `bsDink`). -/
private theorem biteRevert_afterArith2 (hsz36 : 36 ≤ I.calldata.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
    (hblk : ExecBlock config { contract := contract, locals := bsDink I evmUrn iArt iRate iSpot iLine iDust ink art }
      evmUrn biteTailStmts .reverted) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted :=
  biteRevert_afterArith1 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
    (execBlock_append (catBiteSourceArith2 hratePos hartPos hmilkChopPos hfitDunkRoomWad hfitInkDart
      hdartPos hdinkPos hdartLim hdinkLim) hblk)

variable (hsz36 : 36 ≤ I.calldata.size)
  (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
  (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
  (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat)
  (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
  (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
  (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
  (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
  (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
  (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
  (hartPos : 0 < art.toNat) (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
  (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
  (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
  (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
  (hvatCodeMid :
    0 < (UInt256.ofNat
      ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)

include hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust
  hfitDunkRoomWad hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim hvatCodeMid

theorem catBiteSourceGrabFailRevert
    (hGrabFailCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (false, evmGrab, grabOut) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure
    (biteVatRead (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art)) (by simp [evalExpr?, pure])
    (biteGrabArgsEval I evmUrn iArt iRate iSpot iLine iDust ink art) hGrabFailCall)

theorem catBiteSourceDartRateOverflowRevert
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hover : UInt256.size ≤ (biteDartV I evmUrn iRate art).toNat * iRate.toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) hover))

theorem catBiteSourceFessFailRevert
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessFailCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (false, evmFess, fessOut) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
  have hFessArgs :
      evalExprs? config { contract := contract, locals := btDartRate I evmUrn iArt iRate iSpot iLine iDust ink art }
        evmGrab [.var "dartRate"] = .ok [bw (biteDartRateV I evmUrn iRate art)] := by
    simp [evalExprs?, evalExpr_varUInt256 (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art),
      EvalResult.bind, bind, pure]
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure
    (biteVowRead (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art)) (by simp [evalExpr?, pure])
    hFessArgs hFessFailCall)

theorem catBiteSourceTabBaseOverflowRevert
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hover : UInt256.size ≤ (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
  refine ExecBlock.consNormal (biteFessSuccessStmt hFessCall hFessDec) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mul256_revert (evalExpr_varUInt256 (btFess_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btFess_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) hover))

theorem catBiteSourceKickFailRevert
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickFailCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (false, evmKick, kickOut) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
  refine ExecBlock.consNormal (biteFessSuccessStmt hFessCall hFessDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btFess_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btFess_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitTabBase)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btTabBase_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTabBase_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitTabBase hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok (evalExpr_varUInt256 (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_add256_ok (biteLitterRead (btTab_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTab_get_tab I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitLitterNew)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (by simp only [biteLitterNewV]; rw [uadd_toNat, Nat.mod_eq_of_lt hfitLitterNew];
          exact Nat.le_add_right _ _))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (assignStorageRef_storage_scalar (er := { base := "litter", steps := [] }) (ty := uint256St)
        (loc := wordLoc ⟨6⟩) (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
        (by simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) rfl hLitStore)) ?_
  have hMilkFlipVal :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.var "milkFlip") = .ok (.address (biteFlipAddrV I evmUrn)) :=
    evalExpr_varAddr (btLitterNew_get_milkFlip I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
  have hKickGuard :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.binary .gt (.extCodeSize (.var "milkFlip")) (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hMilkFlipVal, evalBinaryOp?, EVM.Word.ofNat, hflipCode]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hKickGuard) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure
    hMilkFlipVal (by simp [evalExpr?, pure])
    (biteKickArgsEval I evmUrn evmFess evmLit iArt iRate iSpot iLine iDust ink art) hKickFailCall)

/-- **kick return-decode revert.** `grab`/`fess` succeed, `litter` is stored, the `flip` guard passes,
and the `kick` CALL *succeeds* (`z = true`) but its return bytes do not ABI-decode to the single
`uint256` (`decode? "kick" = none`); solc's return decoder then reverts at the
`returndatasize < 32` guard. Deep dual of `catBiteSourceKickFailRevert` with the final statement
swapped for `ExecStmt.externalCallReturnDecodeRevert`. -/
theorem catBiteSourceKickDecodeRevert
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = none) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
  refine ExecBlock.consNormal (biteFessSuccessStmt hFessCall hFessDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btFess_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btFess_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitTabBase)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btTabBase_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTabBase_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitTabBase hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok (evalExpr_varUInt256 (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_add256_ok (biteLitterRead (btTab_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTab_get_tab I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitLitterNew)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (by simp only [biteLitterNewV]; rw [uadd_toNat, Nat.mod_eq_of_lt hfitLitterNew];
          exact Nat.le_add_right _ _))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (assignStorageRef_storage_scalar (er := { base := "litter", steps := [] }) (ty := uint256St)
        (loc := wordLoc ⟨6⟩) (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
        (by simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) rfl hLitStore)) ?_
  have hMilkFlipVal :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.var "milkFlip") = .ok (.address (biteFlipAddrV I evmUrn)) :=
    evalExpr_varAddr (btLitterNew_get_milkFlip I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
  have hKickGuard :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.binary .gt (.extCodeSize (.var "milkFlip")) (.intLit 0)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hMilkFlipVal, evalBinaryOp?, EVM.Word.ofNat, hflipCode]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hKickGuard) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
    hMilkFlipVal (by simp [evalExpr?, pure])
    (biteKickArgsEval I evmUrn evmFess evmLit iArt iRate iSpot iLine iDust ink art) hKickCall hKickDec)

/-- **fess no-code revert.** `grab` succeeds and `tab = dartRate * chop` is checked, but the
`EXTCODESIZE(vow)` guard solc inserts before the `vow.fess(...)` CALL is *false* (empty code), so the
`require(extcodesize(vow) > 0)` reverts before any call. This is the `checkedExternalCallNoCode`
outcome, distinct from `catBiteSourceFessFailRevert` (which needs `extcodesize(vow) > 0` and a failed
call). -/
theorem catBiteSourceFessNoCodeRevert
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode0 :
      (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (biteVowGuard_false (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode0))

/-- **kick no-code revert.** `grab`/`fess` succeed and `litter` is stored, but the
`EXTCODESIZE(flip)` guard solc inserts before the `flip.kick(...)` CALL is *false* (empty code), so
the `require(extcodesize(milkFlip) > 0)` reverts before any call. Distinct from
`catBiteSourceKickFailRevert` (which needs `extcodesize(flip) > 0` and a failed call). -/
theorem catBiteSourceKickNoCodeRevert
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode0 :
      (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (biteLocals I) biteTransition.body .reverted := by
  refine biteRevert_afterArith2 hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk hUrnsCall hUrnsDec hlive
    hsz36 hfitInkSpot hfitArtRate hspotPos hratePos hunsafe hlitLtBox hroomGeDust hfitDunkRoomWad
    hmilkChopPos hfitInkDart hartPos hdartPos hdinkPos hdartLim hdinkLim ?_
  simp only [biteTailStmts, checkedExternalCallStmts, checkedMulUintInto, checkedAddUintInto,
    List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVatGuard_true (bsDink_get_vat I evmUrn iArt iRate iSpot iLine iDust ink art) hvatCodeMid)) ?_
  refine ExecBlock.consNormal (biteGrabSuccessStmt hGrabCall hGrabDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btGrab_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btGrab_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitDartRate)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btDartRate_get_dart I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btDartRate_get_rate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btDartRate_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitDartRate hratePos)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (biteVowGuard_true (btDartRate_get_vow I evmUrn iArt iRate iSpot iLine iDust ink art) hvowCode)) ?_
  refine ExecBlock.consNormal (biteFessSuccessStmt hFessCall hFessDec) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_mul256_ok (evalExpr_varUInt256 (btFess_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btFess_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitTabBase)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_checkedMulCheck_true (evalExpr_varUInt256 (btTabBase_get_dartRate I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTabBase_get_milkChop I evmUrn iArt iRate iSpot iLine iDust ink art))
      (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art) rfl hfitTabBase hmilkChopPos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_div256_ok (evalExpr_varUInt256 (btTabBase_get_tabBase I evmUrn iArt iRate iSpot iLine iDust ink art))
      evalExpr_wad wadU_pos)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_add256_ok (biteLitterRead (btTab_get_litter I evmUrn iArt iRate iSpot iLine iDust ink art))
      (evalExpr_varUInt256 (btTab_get_tab I evmUrn iArt iRate iSpot iLine iDust ink art)) rfl hfitLitterNew)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (biteLitterRead (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (by simp only [biteLitterNewV]; rw [uadd_toNat, Nat.mod_eq_of_lt hfitLitterNew];
          exact Nat.le_add_right _ _))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_varUInt256 (btLitterNew_get_litterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art))
      (assignStorageRef_storage_scalar (er := { base := "litter", steps := [] }) (ty := uint256St)
        (loc := wordLoc ⟨6⟩) (btLitterNew_get_litter I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
        (by simp [litterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, uint256St]) rfl hLitStore)) ?_
  have hMilkFlipVal :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.var "milkFlip") = .ok (.address (biteFlipAddrV I evmUrn)) :=
    evalExpr_varAddr (btLitterNew_get_milkFlip I evmUrn evmFess iArt iRate iSpot iLine iDust ink art)
  have hKickGuardFalse :
      evalExpr? config { contract := contract, locals := btLitterNew I evmUrn evmFess iArt iRate iSpot iLine iDust ink art }
        evmLit (.binary .gt (.extCodeSize (.var "milkFlip")) (.intLit 0)) = .ok (.bool false) := by
    simp [evalExpr?, EvalResult.bind, bind, hMilkFlipVal, evalBinaryOp?, EVM.Word.ofNat, hflipCode0]
  exact ExecBlock.consRevert (ExecStmt.requireFalse hKickGuardFalse)

end Reverts

end Benchmarks.Dss.Cat
