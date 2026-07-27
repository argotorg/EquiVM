import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.ExternalCall
import Benchmarks.Dss.Clipper.GetStatusEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## Shared `getFeedPrice()` source and EVM helpers -/

abbrev clipperSpotterIlksSelectorWord : UInt256 :=
  ⟨3647180086⟩

abbrev clipperSpotterIlksSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperSpotterIlksSelectorWord ⟨224⟩

abbrev clipperPipPeekSelectorWord : UInt256 :=
  ⟨1507864023⟩

abbrev clipperPipPeekSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperPipPeekSelectorWord ⟨224⟩

abbrev clipperSpotterTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ I ⟨3⟩)

abbrev clipperGetFeedPriceSpotterAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofUInt256 (clipperSpotterTarget evm.accountMap evm.executionEnv)

abbrev clipperIlkWord (v : ClipperImmutables) : UInt256 :=
  EVM.Word.ofNat (fromBytesBigEndian (match v.ilk with
    | .fixedBytes _ bs => bs
    | _ => []))

theorem clipperEvalGetFeedPriceSpotterTarget (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "spotter" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage spotterRef) = .ok (.address (clipperGetFeedPriceSpotterAddress evm)) := by
  let er : EvaledStorageRef := { base := "spotter", steps := [] }
  have her : evalStorageRef (config v) { contract := contract v, locals := locals } evm
      spotterRef = .ok er := by
    unfold evalStorageRef spotterRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, addrSt]
  have hloc : (config v).storage.layout er = fun _ => some (addrLoc ⟨3⟩) := by
    funext evm'
    rfl
  have hload := evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_address evm ⟨3⟩)
  simpa [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget,
    accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm] using hload

theorem clipperEvalGetFeedPriceSpotterCodeGuard_false
    (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "spotter" = none)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage spotterRef)) (.intLit 0)) =
        .ok (.bool false) := by
  have hnoCode' :
      (EVM.Word.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    simpa using hnoCode
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalGetFeedPriceSpotterTarget v evm locals hbase, evalBinaryOp?, hnoCode']

theorem clipperEvalGetFeedPriceSpotterCodeGuard_true
    (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "spotter" = none)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage spotterRef)) (.intLit 0)) =
        .ok (.bool true) := by
  have hcode' :
      0 < (EVM.Word.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat := by
    simpa using hcode
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalGetFeedPriceSpotterTarget v evm locals hbase, evalBinaryOp?, hcode']

theorem clipperLookupGetFeedPriceFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "getFeedPrice" = some (getFeedPriceFunction v).toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction, wmulFunction, rmulFunction,
    rdivFunction, getFeedPriceFunction, statusFunction]

theorem clipperBindParamsGetFeedPrice (v : ClipperImmutables) :
    bindParams? (getFeedPriceFunction v).params [] = some (∅ : Store) := by
  simp [getFeedPriceFunction, bindParams?]

theorem clipperGetFeedPriceSpotterIlksNoCode (v : ClipperImmutables) (evm : EVM.State)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      (checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
        [ilkExpr v] "spotterIlk") .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config v) (C := contract v) (evm := evm)
      (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
      (name := "spotterIlks") (sendVal := 0) (args := [ilkExpr v]) (perm := true)
      (clipperEvalGetFeedPriceSpotterCodeGuard_false v evm ∅ (by simp) hnoCode)

theorem clipperGetFeedPriceFunctionRevertsSpotterIlksNoCode (v : ClipperImmutables)
    (evm : EVM.State)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let tailStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
    checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ] ++
    checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]
  have hcallBlock :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        callStmts .reverted := by
    simpa [callStmts] using clipperGetFeedPriceSpotterIlksNoCode v evm hnoCode
  have hbody :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        (callStmts ++ tailStmts) .reverted := by
    exact Reasoning.Refinement.execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  apply ExecFuncBody.execBlockRevert
  simpa [getFeedPriceFunction, checkedExternalCallStmts, callStmts, tailStmts] using hbody

theorem clipperGetFeedPriceCallRevertsSpotterIlksNoCode
    (v : ClipperImmutables) (evm : EVM.State) (locals : Store) (retVar : Ident)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsSpotterIlksNoCode v evm hnoCode)

theorem clipperEvalGetFeedPriceIlkArg (v : ClipperImmutables) (evm : EVM.State) :
    evalExpr? (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      (ilkExpr v) = .ok v.ilk := by
  obtain ⟨bs, hbs, _hlen⟩ := v.ilk_wf
  unfold ilkExpr
  rw [hbs]
  unfold evalExpr?
  rfl

theorem clipperEvalGetFeedPriceIlkArgs (v : ClipperImmutables) (evm : EVM.State) :
    evalExprs? (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      [ilkExpr v] = .ok [v.ilk] := by
  exact evalExprs?_singleton (clipperEvalGetFeedPriceIlkArg v evm)

theorem clipperGetFeedPriceSpotterIlksCallFailure (v : ClipperImmutables)
    {evm evm' : EVM.State} {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (false, evm', out) true) :
    ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      (checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
        [ilkExpr v] "spotterIlk") .reverted := by
  have hguard := clipperEvalGetFeedPriceSpotterCodeGuard_true v evm ∅ (by simp) hcode
  have hreceiver := clipperEvalGetFeedPriceSpotterTarget v evm ∅ (by simp)
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
      (name := "spotterIlks") (target := clipperGetFeedPriceSpotterAddress evm)
      (sendVal := 0) (args := [ilkExpr v]) (argVals := [v.ilk]) (out := out)
      (perm := true) hguard hreceiver (clipperEvalGetFeedPriceIlkArgs v evm) hcall

theorem clipperGetFeedPriceFunctionRevertsSpotterIlksCallFailure
    (v : ClipperImmutables) {evm evm' : EVM.State} {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (false, evm', out) true) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let tailStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
    checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ] ++
    checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]
  have hcallBlock :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        callStmts .reverted := by
    simpa [callStmts] using
      clipperGetFeedPriceSpotterIlksCallFailure v hcode hcall
  have hbody :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        (callStmts ++ tailStmts) .reverted := by
    exact Reasoning.Refinement.execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  apply ExecFuncBody.execBlockRevert
  simpa [getFeedPriceFunction, checkedExternalCallStmts, callStmts, tailStmts] using hbody

theorem clipperGetFeedPriceCallRevertsSpotterIlksCallFailure
    (v : ClipperImmutables) {evm evm' : EVM.State} (locals : Store) (retVar : Ident)
    {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (false, evm', out) true) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsSpotterIlksCallFailure v hcode hcall)

noncomputable def clipperSpotterIlksSelectorMem (mem : ByteArray) : ByteArray :=
  clipperSpotterIlksSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperSpotterIlksCalldataMem
    (ilk : UInt256) (mem : ByteArray) : ByteArray :=
  ilk.toByteArray.write 0 (clipperSpotterIlksSelectorMem mem) 132 32

noncomputable def clipperSpotterIlksPostCallMem
    (v : ClipperImmutables) (mem out : ByteArray) : ByteArray :=
  out.write 0 (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev clipperSpotterIlksPipWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev clipperSpotterIlksMatWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev clipperSpotterIlksPipTarget (out : ByteArray) : UInt256 :=
  UInt256.land (clipperSpotterIlksPipWord out) solcAddrMask

abbrev clipperSpotterIlksPipAddress (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (clipperSpotterIlksPipWord out).toNat

abbrev clipperSpotterIlksValues (out : ByteArray) : List Value :=
  [.address (clipperSpotterIlksPipAddress out),
    .int (Int.ofNat (clipperSpotterIlksMatWord out).toNat)]

noncomputable def clipperPipPeekSelectorMem (mem : ByteArray) : ByteArray :=
  clipperPipPeekSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperPipPeekPostCallMem (mem out : ByteArray) : ByteArray :=
  out.write 0 mem 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev clipperPipPeekValueBytes (out : ByteArray) : List UInt8 :=
  (out.toList.drop 0).take 32

abbrev clipperPipPeekValueWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev clipperPipPeekHasWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev clipperPipPeekValues (out : ByteArray) : List Value :=
  [.fixedBytes abiBytes32Width (clipperPipPeekValueBytes out),
    .bool (clipperPipPeekHasWord out != ⟨0⟩)]

theorem clipperSpotterIlksPipAddress_eq_target (out : ByteArray) :
    clipperSpotterIlksPipAddress out =
      AccountAddress.ofUInt256 (clipperSpotterIlksPipTarget out) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp only [clipperSpotterIlksPipAddress, AccountAddress.ofNat, Fin.ofNat]
  change (clipperSpotterIlksPipWord out).toNat % AccountAddress.size =
    (Nat.land (clipperSpotterIlksPipWord out).toNat solcAddrMask.toNat % UInt256.size) %
      AccountAddress.size
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : (clipperSpotterIlksPipWord out).toNat % 2 ^ 160 < UInt256.size := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hsmall]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))).symm

theorem clipperGetFeedPriceHashPostMem_size_ge_164
    (key top age : UInt256) {baseMem out : ByteArray}
    (hbase : baseMem.size = 96) (hout : out.size < UInt256.size) :
    164 ≤
      (twoWordHashMem key (⟨12⟩ : UInt256)
        (clipperStatusPricePostCallMem top age baseMem out)).size := by
  rw [twoWordHashMem_size_of_ge_64]
  · rw [clipperStatusPricePostCallMem_size top age hbase hout]
    omega
  · rw [clipperStatusPricePostCallMem_size top age hbase hout]
    omega

theorem clipperGetFeedPriceHashPostMem_read64
    (key top age : UInt256) {baseMem out : ByteArray}
    (hbase : baseMem.size = 96)
    (hread64 : baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (twoWordHashMem key (⟨12⟩ : UInt256)
        (clipperStatusPricePostCallMem top age baseMem out)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64_of_ge key (⟨12⟩ : UInt256)
    (by
      rw [clipperStatusPricePostCallMem_size top age hbase hout]
      omega)
    (clipperStatusPricePostCallMem_read64 top age hbase hread64 hout)

theorem clipperSpotterIlksSelectorMem_size_of_ge {mem : ByteArray}
    (hmem : 160 ≤ mem.size) :
    (clipperSpotterIlksSelectorMem mem).size = mem.size := by
  unfold clipperSpotterIlksSelectorMem
  exact toByteArray_write32_size_of_le mem clipperSpotterIlksSelectorShifted 128
    mem.size mem.size rfl (by omega) (by simp [Nat.max_eq_left hmem])

theorem clipperSpotterIlksSelectorMem_read64 {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperSpotterIlksSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperSpotterIlksSelectorShifted mem 128 64
    (by omega) (by omega) (by exact lt_usize _ (by omega)), hread64]

theorem clipperSpotterIlksCalldataMem_size_of_ge (ilk : UInt256) {mem : ByteArray}
    (hmem : 164 ≤ mem.size) :
    (clipperSpotterIlksCalldataMem ilk mem).size = mem.size := by
  unfold clipperSpotterIlksCalldataMem
  have hsel := clipperSpotterIlksSelectorMem_size_of_ge (mem := mem) (by omega)
  exact toByteArray_write32_size_of_le (clipperSpotterIlksSelectorMem mem) ilk 132
    mem.size mem.size hsel (by omega) (by simp [Nat.max_eq_left hmem])

theorem clipperSpotterIlksCalldataMem_read64 (ilk : UInt256) {mem : ByteArray}
    (hmem : 164 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperSpotterIlksSelectorMem_size_of_ge (mem := mem) (by omega)]; omega)
    (by omega),
    clipperSpotterIlksSelectorMem_read64 (mem := mem) (by omega) hread64]

theorem clipperSpotterIlksSelectorPrefix :
    clipperSpotterIlksSelectorShifted.toByteArray.extract 0 4 = spotterIlksSelector := by
  native_decide

theorem clipperPipPeekSelectorPrefix :
    clipperPipPeekSelectorShifted.toByteArray.extract 0 4 = pipPeekSelector := by
  native_decide

theorem clipperSpotterIlksCalldataMem_read128_36 (ilk : UInt256) {mem : ByteArray}
    (hmem : 164 ≤ mem.size) :
    (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 128 36 =
      spotterIlksSelector ++ ilk.toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [clipperSpotterIlksCalldataMem_size_of_ge ilk hmem]; omega)]
  have hleft :
      (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 128 4 =
        spotterIlksSelector := by
    unfold clipperSpotterIlksCalldataMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [clipperSpotterIlksSelectorMem_size_of_ge (mem := mem) (by omega)]; omega)
      (by omega) (by
        rw [clipperSpotterIlksSelectorMem_size_of_ge (mem := mem) (by omega)]
        omega)
      (by norm_num) (by norm_num)]
    unfold clipperSpotterIlksSelectorMem
    rw [toByteArray_write_read_window_of_gap clipperSpotterIlksSelectorShifted mem
      128 0 4 (by norm_num) (by norm_num) (by norm_num)
      (by exact lt_usize _ (by omega))]
    exact clipperSpotterIlksSelectorPrefix
  have hright :
      (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 132 32 =
        ilk.toByteArray := by
    unfold clipperSpotterIlksCalldataMem
    rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
      (by rw [clipperSpotterIlksSelectorMem_size_of_ge (mem := mem) (by omega)]; omega)]
    rw [toByteArray_extract_all]
  rw [hleft, show 128 + 4 = 132 by norm_num, hright]

theorem clipperSpotterIlksEncode_eq (v : ClipperImmutables) {mem : ByteArray}
    (hmem : 164 ≤ mem.size) :
    (config v).externalABI.encode? "spotterIlks" [v.ilk] =
      some ((clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).readWithPadding 128 36) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperIlkWord, hilk]
  rw [hilkWord]
  change (config v).externalABI.encode? "spotterIlks" [.fixedBytes ⟨31, by decide⟩ bs] =
    some ((clipperSpotterIlksCalldataMem (EVM.Word.ofNat (fromBytesBigEndian bs))
      mem).readWithPadding 128 36)
  rw [clipperSpotterIlksCalldataMem_read128_36 _ hmem]
  have hbytes :
      bs = EVM.Word.toBytesBE (EVM.Word.ofNat (fromBytesBigEndian bs)) := by
    have hword : ABI.bytesToWord bs = EVM.Word.ofNat (fromBytesBigEndian bs) := by
      unfold ABI.bytesToWord fromByteArrayBigEndian
      simp [byteArray_toList_eq, EVM.Word.ofNat]
    rw [← hword]
    exact (toBytesBE_bytesToWord_of_length hlen).symm
  have hwordBytes :
      (EVM.Word.ofNat (fromBytesBigEndian bs)).toByteArray =
        { data := bs.toArray } := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray
      (EVM.Word.ofNat (fromBytesBigEndian bs)), ← hbytes]
    apply ByteArray.ext
    simp
  have hbsByteArray : bs.toByteArray = { data := bs.toArray } := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_data_toByteArray]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width,
    spotterIlksSelector, selectorBytes, hlen, ABI.zeroBytes, hwordBytes, hbsByteArray]

theorem clipperPipPeekSelectorMem_read128_4 {mem : ByteArray}
    (hmem : 132 ≤ mem.size) :
    (clipperPipPeekSelectorMem mem).readWithPadding 128 4 = pipPeekSelector := by
  unfold clipperPipPeekSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperPipPeekSelectorShifted mem
    128 0 4 (by norm_num) (by norm_num) (by norm_num)
    (by exact lt_usize _ (by omega))]
  exact clipperPipPeekSelectorPrefix

theorem clipperPipPeekEncode_eq (v : ClipperImmutables) {mem : ByteArray}
    (hmem : 132 ≤ mem.size) :
    (config v).externalABI.encode? "peek" [] =
      some ((clipperPipPeekSelectorMem mem).readWithPadding 128 4) := by
  rw [clipperPipPeekSelectorMem_read128_4 hmem]
  simp [config, externalABI]

theorem clipperGetFeedPriceBytesToWord_drop_take32_eq_extract
    (out : ByteArray) (start : Nat) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]

theorem clipperSpotterIlksDecode_none_short_aux {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiAddress, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiAddress, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress, abiUInt256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [abiAddress, abiUInt256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [abiAddress, abiUInt256] out.toList 0 with
  | none => rfl
  | some values =>
      have hlenDecoded :=
        decodeScalarWordsWithMode?_some_length (mode := DecodeMode.legacySolc05)
          (types := [abiAddress, abiUInt256]) (bytes := out.toList)
          (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDecoded
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlenDecoded
      omega

theorem clipperSpotterIlksDecode_none_short {v : ClipperImmutables} {out : ByteArray}
    (hshort : out.size < 64) :
    (config v).externalABI.decode? "spotterIlks" out = none := by
  have h := clipperSpotterIlksDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI, addr, uint256, uint256Int, abiAddress, abiUInt256] using h

theorem clipperSpotterIlksDecode_ok_aux {out : ByteArray} (hlo : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiAddress, abiUInt256] out =
      some (clipperSpotterIlksValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 : ABI.bytesToWord ((out.toList.drop 0).take 32) =
      clipperSpotterIlksPipWord out := by
    simpa [clipperSpotterIlksPipWord] using
      clipperGetFeedPriceBytesToWord_drop_take32_eq_extract out 0
  have hword1 : ABI.bytesToWord ((out.toList.drop 32).take 32) =
      clipperSpotterIlksMatWord out := by
    simpa [clipperSpotterIlksMatWord] using
      clipperGetFeedPriceBytesToWord_drop_take32_eq_extract out 32
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiAddress, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiAddress, abiUInt256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 32) htake32]
  rw [hword0, hword1]
  rfl

theorem clipperSpotterIlksDecode_ok {v : ClipperImmutables} {out : ByteArray}
    (hlo : 64 ≤ out.size) :
    (config v).externalABI.decode? "spotterIlks" out =
      some (clipperSpotterIlksValues out) := by
  have h := clipperSpotterIlksDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, addr, uint256, uint256Int, abiAddress, abiUInt256] using h

theorem clipperPipPeekDecode_none_short_aux {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiBytes32, abiBool] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [abiBytes32, abiBool] = some 64 by native_decide]
  simp only [bind, Option.bind]
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiBool, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, decodeABIValue?, readBytes?, bind,
    Option.bind, readWord?, decodeABIWord?]
  by_cases h32 : out.size < 32
  · have hnot : ¬ (List.take 32 (List.drop 0 out.toList)).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    rw [if_neg hnot]
  · have htake0 : (List.take 32 (List.drop 0 out.toList)).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    rw [if_pos htake0]
    norm_num
    have hnot : ¬ 32 ≤ out.toList.length - 32 := by
      rw [hlen]
      omega
    rw [if_neg hnot]

theorem clipperPipPeekDecode_none_short {v : ClipperImmutables} {out : ByteArray}
    (hshort : out.size < 64) :
    (config v).externalABI.decode? "peek" out = none := by
  have h := clipperPipPeekDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI, bytes32, bytes32Width, boolTy, abiBytes32, abiBytes32Width,
    abiBool] using h

theorem clipperPipPeekDecode_ok_aux {out : ByteArray} (hlo : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiBytes32, abiBool] out =
      some (clipperPipPeekValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword1 : ABI.bytesToWord ((out.toList.drop 32).take 32) =
      clipperPipPeekHasWord out := by
    simpa [clipperPipPeekHasWord] using
      clipperGetFeedPriceBytesToWord_drop_take32_eq_extract out 32
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [abiBytes32, abiBool] = some 64 by native_decide]
  simp only [bind, Option.bind]
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiBool, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, decodeABIValue?, readBytes?, bind,
    Option.bind, readWord?, decodeABIWord?]
  rw [if_pos htake0]
  norm_num
  rw [if_pos (by rw [hlen]; omega)]
  dsimp only [Option.bind]
  rw [hword1]
  by_cases hzero : clipperPipPeekHasWord out = ⟨0⟩
  · simp [hzero, clipperPipPeekValues, clipperPipPeekValueBytes, abiBytes32Width]
  · have hnzNat : ¬ (clipperPipPeekHasWord out).toNat = 0 := by
      intro h
      exact hzero (uint256_toNat_eq_zero h)
    rw [if_neg (by simpa [UInt256.toNat] using hnzNat)]
    simp [hzero, clipperPipPeekValues, clipperPipPeekValueBytes, abiBytes32Width]

theorem clipperPipPeekDecode_ok {v : ClipperImmutables} {out : ByteArray}
    (hlo : 64 ≤ out.size) :
    (config v).externalABI.decode? "peek" out = some (clipperPipPeekValues out) := by
  have h := clipperPipPeekDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, bytes32, bytes32Width, boolTy, abiBytes32, abiBytes32Width,
    abiBool] using h

abbrev clipperGetFeedPriceSpotterIlkLocals (out : ByteArray) : Store :=
  (∅ : Store).insert "spotterIlk" (collapseReturns (clipperSpotterIlksValues out))

abbrev clipperGetFeedPricePipLocals (out : ByteArray) : Store :=
  (clipperGetFeedPriceSpotterIlkLocals out).insert "pip"
    (.address (clipperSpotterIlksPipAddress out))

abbrev clipperGetFeedPricePeekLocals (outIlks outPeek : ByteArray) : Store :=
  (clipperGetFeedPricePipLocals outIlks).insert "peekRet"
    (collapseReturns (clipperPipPeekValues outPeek))

abbrev clipperGetFeedPriceValLocals (outIlks outPeek : ByteArray) : Store :=
  (clipperGetFeedPricePeekLocals outIlks outPeek).insert "val"
    (.fixedBytes abiBytes32Width (clipperPipPeekValueBytes outPeek))

abbrev clipperGetFeedPriceHasLocals (outIlks outPeek : ByteArray) : Store :=
  (clipperGetFeedPriceValLocals outIlks outPeek).insert "has"
    (.bool (clipperPipPeekHasWord outPeek != ⟨0⟩))

theorem clipperEvalGetFeedPricePipFromSpotterIlk
    (v : ClipperImmutables) (evm : EVM.State) (out : ByteArray) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetFeedPriceSpotterIlkLocals out } evm
      (tuple0 (.var "spotterIlk")) = .ok (.address (clipperSpotterIlksPipAddress out)) := by
  simp [clipperGetFeedPriceSpotterIlkLocals, collapseReturns, tuple0, evalExpr?,
    tupleGetValue?, EvalResult.ofOption, EvalResult.bind, bind]

theorem clipperEvalGetFeedPricePipCodeGuard_false
    (v : ClipperImmutables) (evm : EVM.State) (out : ByteArray)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress out)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := clipperGetFeedPricePipLocals out }
      evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) =
        .ok (.bool false) := by
  have hnoCode' :
      (EVM.Word.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress out)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
    simpa using hnoCode
  simpa [clipperGetFeedPricePipLocals, evalExpr?, EvalResult.bind, bind,
    EvalResult.ofOption, evalBinaryOp?] using hnoCode'

theorem clipperEvalGetFeedPricePipCodeGuard_true
    (v : ClipperImmutables) (evm : EVM.State) (out : ByteArray)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress out)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperGetFeedPricePipLocals out }
      evm (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) =
        .ok (.bool true) := by
  have hcode' :
      0 < (EVM.Word.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress out)).option 0
        (fun acc => acc.code.size))).toNat := by
    simpa using hcode
  simpa [clipperGetFeedPricePipLocals, evalExpr?, EvalResult.bind, bind,
    EvalResult.ofOption, evalBinaryOp?] using hcode'

theorem clipperEvalGetFeedPricePeekVal
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetFeedPricePeekLocals outIlks outPeek } evm
      (tuple0 (.var "peekRet")) =
        .ok (.fixedBytes abiBytes32Width (clipperPipPeekValueBytes outPeek)) := by
  simp [clipperGetFeedPricePeekLocals, collapseReturns, tuple0, evalExpr?, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind]

theorem clipperEvalGetFeedPricePeekHas
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetFeedPriceValLocals outIlks outPeek } evm
      (tuple1 (.var "peekRet")) =
        .ok (.bool (clipperPipPeekHasWord outPeek != ⟨0⟩)) := by
  simp only [tuple1, evalExpr?, EvalResult.bind, bind]
  rw [store_get_ne]
  · simp [clipperGetFeedPricePeekLocals, collapseReturns, tupleGetValue?,
      EvalResult.ofOption]
  · decide

theorem clipperEvalGetFeedPriceHas_false
    (v : ClipperImmutables) (evm : EVM.State) (outIlks outPeek : ByteArray)
    (hzero : clipperPipPeekHasWord outPeek = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperGetFeedPriceHasLocals outIlks outPeek } evm
      (.var "has") = .ok (.bool false) := by
  simp [clipperGetFeedPriceHasLocals, hzero, evalExpr?, EvalResult.ofOption]

theorem clipperGetFeedPricePipPeekNoCode
    (v : ClipperImmutables) (evm : EVM.State) (outIlks : ByteArray)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperGetFeedPricePipLocals outIlks } : Frame)
      evm (checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallVarNoCode
      (cfg := config v) (C := contract v) (evm := evm)
      (locals := clipperGetFeedPricePipLocals outIlks) (receiver := "pip")
      (retVar := "peekRet") (name := "peek") (sendVal := 0) (args := [])
      (perm := true)
      (clipperEvalGetFeedPricePipCodeGuard_false v evm outIlks hnoCode)

theorem clipperGetFeedPricePipPeekCallFailure
    (v : ClipperImmutables) {evm evm' : EVM.State} {outIlks outPeek : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (false, evm', outPeek) true) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperGetFeedPricePipLocals outIlks } : Frame)
      evm (checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet")
      .reverted := by
  have hguard := clipperEvalGetFeedPricePipCodeGuard_true v evm outIlks hcode
  have hreceiver :
      (clipperGetFeedPricePipLocals outIlks).get? "pip" =
        some (.address (clipperSpotterIlksPipAddress outIlks)) := by
    simp [clipperGetFeedPricePipLocals]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallVarFailure
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := clipperGetFeedPricePipLocals outIlks) (receiver := "pip")
      (retVar := "peekRet") (name := "peek")
      (target := clipperSpotterIlksPipAddress outIlks)
      (sendVal := 0) (args := []) (argVals := []) (out := outPeek)
      (perm := true) hguard hreceiver (by rfl) hcall

theorem clipperGetFeedPricePipPeekDecodeRevert
    (v : ClipperImmutables) {evm evm' : EVM.State} {outIlks outPeek : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evm', outPeek) true)
    (hdec : (config v).externalABI.decode? "peek" outPeek = none) :
    ExecBlock (config v)
      ({ contract := contract v, locals := clipperGetFeedPricePipLocals outIlks } : Frame)
      evm (checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet")
      .reverted := by
  have hguard := clipperEvalGetFeedPricePipCodeGuard_true v evm outIlks hcode
  have hreceiver :
      (clipperGetFeedPricePipLocals outIlks).get? "pip" =
        some (.address (clipperSpotterIlksPipAddress outIlks)) := by
    simp [clipperGetFeedPricePipLocals]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallVarDecodeRevert
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := clipperGetFeedPricePipLocals outIlks) (receiver := "pip")
      (retVar := "peekRet") (name := "peek")
      (target := clipperSpotterIlksPipAddress outIlks)
      (sendVal := 0) (args := []) (argVals := []) (out := outPeek)
      (perm := true) hguard hreceiver (by rfl) hcall hdec

theorem clipperGetFeedPriceFunctionRevertsPipPeekBlock
    (v : ClipperImmutables) {evm evmIlks : EVM.State} {outIlks : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hpeek :
      ExecBlock (config v)
        ({ contract := contract v, locals := clipperGetFeedPricePipLocals outIlks } : Frame)
        evmIlks
        (checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet")
        .reverted) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let pipLetStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ]
  let peekStmts := checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet"
  let tailStmts : List Stmt :=
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ] ++
    checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]
  let emptyFrame : Frame := { contract := contract v, locals := ∅ }
  let spotterFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceSpotterIlkLocals outIlks }
  let pipFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPricePipLocals outIlks }
  have hguard := clipperEvalGetFeedPriceSpotterCodeGuard_true v evm ∅ (by simp) hcode
  have hreceiver := clipperEvalGetFeedPriceSpotterTarget v evm ∅ (by simp)
  have hcallBlock :
      ExecBlock (config v) emptyFrame evm callStmts (.ok spotterFrame evmIlks) := by
    simpa [emptyFrame, spotterFrame, callStmts, clipperGetFeedPriceSpotterIlkLocals] using
      checkedExternalCallSuccess
        (cfg := config v) (C := contract v) (evm := evm) (evm' := evmIlks)
        (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
        (name := "spotterIlks") (target := clipperGetFeedPriceSpotterAddress evm)
        (sendVal := 0) (args := [ilkExpr v]) (argVals := [v.ilk]) (out := outIlks)
        (perm := true) (value := clipperSpotterIlksValues outIlks)
        hguard hreceiver (clipperEvalGetFeedPriceIlkArgs v evm) hcallIlks hdecIlks
  have hpipStmt :
      ExecStmt (config v) spotterFrame
        evmIlks (.letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")))
        (.ok pipFrame evmIlks) := by
    simpa [spotterFrame, pipFrame, clipperGetFeedPricePipLocals] using
      ExecStmt.letDecl
        (cfg := config v)
        (solm := spotterFrame)
        (evm := evmIlks) (name := "pip") (ty := some addr)
        (expr := tuple0 (.var "spotterIlk"))
        (value := .address (clipperSpotterIlksPipAddress outIlks))
        (clipperEvalGetFeedPricePipFromSpotterIlk v evmIlks outIlks)
  have hpipBlock :
      ExecBlock (config v) spotterFrame evmIlks pipLetStmts (.ok pipFrame evmIlks) := by
    exact ExecBlock.consNormal hpipStmt ExecBlock.nil
  have hpeekBlock :
      ExecBlock (config v) pipFrame evmIlks peekStmts .reverted := by
    simpa [pipFrame, peekStmts] using hpeek
  have hpeekTail :
      ExecBlock (config v) pipFrame evmIlks (peekStmts ++ tailStmts) .reverted := by
    exact Reasoning.Refinement.execBlock_append_term
      (s1 := peekStmts) (s2 := tailStmts) hpeekBlock (by intro f e h; cases h)
  have hafterPip :
      ExecBlock (config v) spotterFrame evmIlks
        (pipLetStmts ++ (peekStmts ++ tailStmts)) .reverted := by
    exact Reasoning.Refinement.execBlock_append hpipBlock hpeekTail
  have hbody :
      ExecBlock (config v) emptyFrame evm
        (callStmts ++ (pipLetStmts ++ (peekStmts ++ tailStmts))) .reverted := by
    exact Reasoning.Refinement.execBlock_append hcallBlock hafterPip
  apply ExecFuncBody.execBlockRevert
  simpa [emptyFrame, getFeedPriceFunction, checkedExternalCallStmts, callStmts, pipLetStmts,
    peekStmts, tailStmts, List.append_assoc] using hbody

theorem clipperGetFeedPriceFunctionRevertsPipPeekNoCode
    (v : ClipperImmutables) {evm evmIlks : EVM.State} {outIlks : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hnoCode :
      (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  exact clipperGetFeedPriceFunctionRevertsPipPeekBlock v hcode hcallIlks hdecIlks
    (clipperGetFeedPricePipPeekNoCode v evmIlks outIlks hnoCode)

theorem clipperGetFeedPriceFunctionRevertsPipPeekCallFailure
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (false, evmPeek, outPeek) true) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  exact clipperGetFeedPriceFunctionRevertsPipPeekBlock v hcodeIlks hcallIlks hdecIlks
    (clipperGetFeedPricePipPeekCallFailure v hcodePip hcallPeek)

theorem clipperGetFeedPriceFunctionRevertsPipPeekDecode
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek = none) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  exact clipperGetFeedPriceFunctionRevertsPipPeekBlock v hcodeIlks hcallIlks hdecIlks
    (clipperGetFeedPricePipPeekDecodeRevert v hcodePip hcallPeek hdecPeek)

theorem clipperGetFeedPriceFunctionRevertsPipPeekHasFalse
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek =
      some (clipperPipPeekValues outPeek))
    (hhasFalse : clipperPipPeekHasWord outPeek = ⟨0⟩) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let pipLetStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ]
  let peekStmts := checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet"
  let tailStmts : List Stmt :=
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ] ++
    checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]
  let emptyFrame : Frame := { contract := contract v, locals := ∅ }
  let spotterFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceSpotterIlkLocals outIlks }
  let pipFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPricePipLocals outIlks }
  let peekFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPricePeekLocals outIlks outPeek }
  let valFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceValLocals outIlks outPeek }
  let hasFrame : Frame :=
    { contract := contract v, locals := clipperGetFeedPriceHasLocals outIlks outPeek }
  have hguard := clipperEvalGetFeedPriceSpotterCodeGuard_true v evm ∅ (by simp) hcodeIlks
  have hreceiver := clipperEvalGetFeedPriceSpotterTarget v evm ∅ (by simp)
  have hcallBlock :
      ExecBlock (config v) emptyFrame evm callStmts (.ok spotterFrame evmIlks) := by
    simpa [emptyFrame, spotterFrame, callStmts, clipperGetFeedPriceSpotterIlkLocals] using
      checkedExternalCallSuccess
        (cfg := config v) (C := contract v) (evm := evm) (evm' := evmIlks)
        (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
        (name := "spotterIlks") (target := clipperGetFeedPriceSpotterAddress evm)
        (sendVal := 0) (args := [ilkExpr v]) (argVals := [v.ilk]) (out := outIlks)
        (perm := true) (value := clipperSpotterIlksValues outIlks)
        hguard hreceiver (clipperEvalGetFeedPriceIlkArgs v evm) hcallIlks hdecIlks
  have hpipStmt :
      ExecStmt (config v) spotterFrame
        evmIlks (.letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")))
        (.ok pipFrame evmIlks) := by
    simpa [spotterFrame, pipFrame, clipperGetFeedPricePipLocals] using
      ExecStmt.letDecl
        (cfg := config v)
        (solm := spotterFrame)
        (evm := evmIlks) (name := "pip") (ty := some addr)
        (expr := tuple0 (.var "spotterIlk"))
        (value := .address (clipperSpotterIlksPipAddress outIlks))
        (clipperEvalGetFeedPricePipFromSpotterIlk v evmIlks outIlks)
  have hpipBlock :
      ExecBlock (config v) spotterFrame evmIlks pipLetStmts (.ok pipFrame evmIlks) := by
    exact ExecBlock.consNormal hpipStmt ExecBlock.nil
  have hpipGuard := clipperEvalGetFeedPricePipCodeGuard_true v evmIlks outIlks hcodePip
  have hpipReceiver :
      (clipperGetFeedPricePipLocals outIlks).get? "pip" =
        some (.address (clipperSpotterIlksPipAddress outIlks)) := by
    simp [clipperGetFeedPricePipLocals]
  have hpeekBlock :
      ExecBlock (config v) pipFrame evmIlks peekStmts (.ok peekFrame evmPeek) := by
    simpa [pipFrame, peekFrame, peekStmts, clipperGetFeedPricePeekLocals] using
      checkedExternalCallVarSuccess
        (cfg := config v) (C := contract v) (evm := evmIlks) (evm' := evmPeek)
        (locals := clipperGetFeedPricePipLocals outIlks) (receiver := "pip")
        (retVar := "peekRet") (name := "peek")
        (target := clipperSpotterIlksPipAddress outIlks)
        (sendVal := 0) (args := []) (argVals := []) (out := outPeek)
        (perm := true) (value := clipperPipPeekValues outPeek)
        hpipGuard hpipReceiver (by rfl) hcallPeek hdecPeek
  have hvalStmt :
      ExecStmt (config v) peekFrame evmPeek
        (.letDecl "val" (some bytes32) (tuple0 (.var "peekRet")))
        (.ok valFrame evmPeek) := by
    simpa [peekFrame, valFrame, clipperGetFeedPriceValLocals] using
      ExecStmt.letDecl
        (cfg := config v) (solm := peekFrame) (evm := evmPeek)
        (name := "val") (ty := some bytes32) (expr := tuple0 (.var "peekRet"))
        (value := .fixedBytes abiBytes32Width (clipperPipPeekValueBytes outPeek))
        (clipperEvalGetFeedPricePeekVal v evmPeek outIlks outPeek)
  have hhasStmt :
      ExecStmt (config v) valFrame evmPeek
        (.letDecl "has" (some boolTy) (tuple1 (.var "peekRet")))
        (.ok hasFrame evmPeek) := by
    simpa [valFrame, hasFrame, clipperGetFeedPriceHasLocals] using
      ExecStmt.letDecl
        (cfg := config v) (solm := valFrame) (evm := evmPeek)
        (name := "has") (ty := some boolTy) (expr := tuple1 (.var "peekRet"))
        (value := .bool (clipperPipPeekHasWord outPeek != ⟨0⟩))
        (clipperEvalGetFeedPricePeekHas v evmPeek outIlks outPeek)
  have hrequire :
      ExecStmt (config v) hasFrame evmPeek (.require (.var "has")) .reverted := by
    exact ExecStmt.requireFalse
      (clipperEvalGetFeedPriceHas_false v evmPeek outIlks outPeek hhasFalse)
  have htail :
      ExecBlock (config v) peekFrame evmPeek tailStmts .reverted := by
    simpa [tailStmts] using
      (ExecBlock.consNormal hvalStmt
        (ExecBlock.consNormal hhasStmt (ExecBlock.consRevert hrequire)))
  have hpeekTail :
      ExecBlock (config v) pipFrame evmIlks (peekStmts ++ tailStmts) .reverted := by
    exact Reasoning.Refinement.execBlock_append hpeekBlock htail
  have hafterPip :
      ExecBlock (config v) spotterFrame evmIlks
        (pipLetStmts ++ (peekStmts ++ tailStmts)) .reverted := by
    exact Reasoning.Refinement.execBlock_append hpipBlock hpeekTail
  have hbody :
      ExecBlock (config v) emptyFrame evm
        (callStmts ++ (pipLetStmts ++ (peekStmts ++ tailStmts))) .reverted := by
    exact Reasoning.Refinement.execBlock_append hcallBlock hafterPip
  apply ExecFuncBody.execBlockRevert
  simpa [emptyFrame, getFeedPriceFunction, checkedExternalCallStmts, callStmts, pipLetStmts,
    peekStmts, tailStmts, List.append_assoc] using hbody

theorem clipperGetFeedPriceCallRevertsPipPeekHasFalse
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    (locals : Store) (retVar : Ident) {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek =
      some (clipperPipPeekValues outPeek))
    (hhasFalse : clipperPipPeekHasWord outPeek = ⟨0⟩) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsPipPeekHasFalse v hcodeIlks hcallIlks
      hdecIlks hcodePip hcallPeek hdecPeek hhasFalse)

theorem clipperGetFeedPriceCallRevertsPipPeekNoCode
    (v : ClipperImmutables) {evm evmIlks : EVM.State} (locals : Store) (retVar : Ident)
    {outIlks : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hnoCode :
      (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsPipPeekNoCode v hcode hcallIlks hdecIlks hnoCode)

theorem clipperGetFeedPriceCallRevertsPipPeekCallFailure
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    (locals : Store) (retVar : Ident) {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (false, evmPeek, outPeek) true) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsPipPeekCallFailure v hcodeIlks hcallIlks hdecIlks
      hcodePip hcallPeek)

theorem clipperGetFeedPriceCallRevertsPipPeekDecode
    (v : ClipperImmutables) {evm evmIlks evmPeek : EVM.State}
    (locals : Store) (retVar : Ident) {outIlks outPeek : ByteArray}
    (hcodeIlks :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evmIlks, outIlks) true)
    (hdecIlks :
      (config v).externalABI.decode? "spotterIlks" outIlks =
        some (clipperSpotterIlksValues outIlks))
    (hcodePip :
      0 < (UInt256.ofNat ((evmIlks.lookupAccount (clipperSpotterIlksPipAddress outIlks)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallPeek :
      typedCallViaEVM (config v) evmIlks
        (EVM.address (clipperSpotterIlksPipAddress outIlks)) "peek" 0 []
        (true, evmPeek, outPeek) true)
    (hdecPeek : (config v).externalABI.decode? "peek" outPeek = none) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsPipPeekDecode v hcodeIlks hcallIlks hdecIlks
      hcodePip hcallPeek hdecPeek)

theorem clipperGetFeedPriceSpotterIlksDecodeRevert
    (v : ClipperImmutables) {evm evm' : EVM.State} {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evm', out) true)
    (hdec : (config v).externalABI.decode? "spotterIlks" out = none) :
    ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
      (checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
        [ilkExpr v] "spotterIlk") .reverted := by
  have hguard := clipperEvalGetFeedPriceSpotterCodeGuard_true v evm ∅ (by simp) hcode
  have hreceiver := clipperEvalGetFeedPriceSpotterTarget v evm ∅ (by simp)
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config v) (C := contract v) (evm := evm) (evm' := evm')
      (locals := ∅) (receiver := .storage spotterRef) (retVar := "spotterIlk")
      (name := "spotterIlks") (target := clipperGetFeedPriceSpotterAddress evm)
      (sendVal := 0) (args := [ilkExpr v]) (argVals := [v.ilk]) (out := out)
      (perm := true) hguard hreceiver (clipperEvalGetFeedPriceIlkArgs v evm) hcall hdec

theorem clipperGetFeedPriceFunctionRevertsSpotterIlksDecode
    (v : ClipperImmutables) {evm evm' : EVM.State} {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evm', out) true)
    (hdec : (config v).externalABI.decode? "spotterIlks" out = none) :
    ExecFuncBody (config v) ({ contract := contract v, locals := ∅ } : Frame)
      evm (getFeedPriceFunction v).body .reverted := by
  let callStmts := checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
    [ilkExpr v] "spotterIlk"
  let tailStmts : List Stmt :=
    [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
    checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
    [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
      .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
      .require (.var "has") ] ++
    checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
    checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
    [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
      .return [.var "feedPrice"] ]
  have hcallBlock :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        callStmts .reverted := by
    simpa [callStmts] using
      clipperGetFeedPriceSpotterIlksDecodeRevert v hcode hcall hdec
  have hbody :
      ExecBlock (config v) ({ contract := contract v, locals := ∅ } : Frame) evm
        (callStmts ++ tailStmts) .reverted := by
    exact Reasoning.Refinement.execBlock_append_term (s1 := callStmts) (s2 := tailStmts)
      hcallBlock (by intro f e h; cases h)
  apply ExecFuncBody.execBlockRevert
  simpa [getFeedPriceFunction, checkedExternalCallStmts, callStmts, tailStmts] using hbody

theorem clipperGetFeedPriceCallRevertsSpotterIlksDecode
    (v : ClipperImmutables) {evm evm' : EVM.State} (locals : Store) (retVar : Ident)
    {out : ByteArray}
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperGetFeedPriceSpotterAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm
        (EVM.address (clipperGetFeedPriceSpotterAddress evm)) "spotterIlks" 0 [v.ilk]
        (true, evm', out) true)
    (hdec : (config v).externalABI.decode? "spotterIlks" out = none) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.internalCall "getFeedPrice" [] retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := locals })
    (evm := evm)
    (name := "getFeedPrice") (retVar := retVar)
    (args := []) (argVals := [])
    (callee := getFeedPriceFunction v)
    (locals := ∅)
    (by rfl)
    (clipperLookupGetFeedPriceFunction v)
    (clipperBindParamsGetFeedPrice v)
    (clipperGetFeedPriceFunctionRevertsSpotterIlksDecode v hcode hcall hdec)

theorem byteArray_write_read_first_word_back (src base : ByteArray)
    (destAddr len : ℕ) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 32 ≤ len) (hin : destAddr + len ≤ base.size) :
    (src.write 0 base destAddr len).readWithPadding destAddr 32 =
      src.extract 0 32 := by
  rw [write_eq_gen src base destAddr len hlen hsrc hin]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  have htail : (base.extract (destAddr + len) base.size).size = base.size - (destAddr + len) := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ destAddr (by
    rw [ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_append, hprefix,
      hsrcPrefix, htail]
    omega)]
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window (base.extract 0 destAddr)
    (src.extract 0 len ++ base.extract (destAddr + len) base.size)
    destAddr (destAddr + 32) (by rw [hprefix])]
  rw [show destAddr - (base.extract 0 destAddr).size = 0 by rw [hprefix]; omega]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  rw [extract_append_left (src.extract 0 len)
    (base.extract (destAddr + len) base.size) 0 32 (by rw [hsrcPrefix]; omega)]
  exact extract_prefix src len 0 32 hword

theorem byteArray_write_read_second_word_back (src base : ByteArray)
    (destAddr len : ℕ) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 64 ≤ len) (hin : destAddr + len ≤ base.size) :
    (src.write 0 base destAddr len).readWithPadding (destAddr + 32) 32 =
      src.extract 32 64 := by
  rw [write_eq_gen src base destAddr len hlen hsrc hin]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  have htail : (base.extract (destAddr + len) base.size).size = base.size - (destAddr + len) := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ (destAddr + 32) (by
    rw [ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_append, hprefix,
      hsrcPrefix, htail]
    omega)]
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window (base.extract 0 destAddr)
    (src.extract 0 len ++ base.extract (destAddr + len) base.size)
    (destAddr + 32) (destAddr + 32 + 32) (by rw [hprefix]; omega)]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  rw [show destAddr + 32 + 32 - (base.extract 0 destAddr).size = 64 by
    rw [hprefix]; omega]
  rw [extract_append_left (src.extract 0 len)
    (base.extract (destAddr + len) base.size) 32 64 (by rw [hsrcPrefix]; omega)]
  exact extract_prefix src len 32 64 hword

theorem clipperSpotterIlksPostCallMem_size_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).size = 196 := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 196 := by
    rw [clipperSpotterIlksCalldataMem_size_of_ge (clipperIlkWord v)
      (mem := mem) (by rw [hmem]; omega), hmem]
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  rw [write_eq_gen out (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
    128 64 (by omega) (by omega) (by rw [hbase]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hbase]
  omega

theorem clipperSpotterIlksPostCallMem_read64_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 196 := by
    rw [clipperSpotterIlksCalldataMem_size_of_ge (clipperIlkWord v)
      (mem := mem) (by rw [hmem]; omega), hmem]
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  rw [write_read_below_gen_extend out
    (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
    128 64 64 (by omega) (by omega) (by rw [hbase]; omega) (by omega)]
  exact clipperSpotterIlksCalldataMem_read64 (clipperIlkWord v)
    (by rw [hmem]; omega) hread64

theorem clipperSpotterIlksPostCallMem_size
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).size = 196 := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 196 := by
    rw [clipperSpotterIlksCalldataMem_size_of_ge (clipperIlkWord v)
      (mem := mem) (by rw [hmem]; omega), hmem]
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hbase]
    · rw [write_eq_gen out (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
        128 out.size hzero le_rfl (by rw [hbase]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega
  · have hlo : 64 ≤ out.size := by omega
    exact clipperSpotterIlksPostCallMem_size_long v hmem hlo hout

theorem clipperSpotterIlksPostCallMem_read64
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 196 := by
    rw [clipperSpotterIlksCalldataMem_size_of_ge (clipperIlkWord v)
      (mem := mem) (by rw [hmem]; omega), hmem]
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact clipperSpotterIlksCalldataMem_read64 (clipperIlkWord v)
        (by rw [hmem]; omega) hread64
    · rw [write_read_below_gen_extend out
        (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
        128 out.size 64 hzero le_rfl (by rw [hbase]; omega) (by omega)]
      exact clipperSpotterIlksCalldataMem_read64 (clipperIlkWord v)
        (by rw [hmem]; omega) hread64
  · have hlo : 64 ≤ out.size := by omega
    exact clipperSpotterIlksPostCallMem_read64_long v hmem hread64 hlo hout

theorem clipperSpotterIlksPostCallMem_mload64
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperSpotterIlksPostCallMem_size v hmem hout]; decide)
    (by decide)
    (clipperSpotterIlksPostCallMem_read64 v hmem hread64 hout)

theorem clipperSpotterIlksPostCallMem_mload64_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperSpotterIlksPostCallMem_size_long v hmem hlo hout]; decide)
    (by decide)
    (clipperSpotterIlksPostCallMem_read64_long v hmem hread64 hlo hout)

theorem clipperSpotterIlksPostCallMem_read128_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 196 := by
    rw [clipperSpotterIlksCalldataMem_size_of_ge (clipperIlkWord v)
      (mem := mem) (by rw [hmem]; omega), hmem]
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact byteArray_write_read_first_word_back out
    (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
    128 64 (by omega) (by omega) (by omega) (by rw [hbase]; omega)

theorem clipperSpotterIlksPostCallMem_mload128_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      clipperSpotterIlksPipWord out := by
  have hsize := clipperSpotterIlksPostCallMem_size_long v hmem hlo hout
  have hread := clipperSpotterIlksPostCallMem_read128_long v hmem hlo hout
  have hcond :
      ¬ ((⟨128⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
    rw [hsize]
    decide
  rw [if_neg hcond]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding 128 32)) =
    clipperSpotterIlksPipWord out
  rw [hread]

theorem clipperPipPeekSelectorMem_size_of_ge {mem : ByteArray}
    (hmem : 160 ≤ mem.size) :
    (clipperPipPeekSelectorMem mem).size = mem.size := by
  unfold clipperPipPeekSelectorMem
  exact toByteArray_write32_size_of_le mem clipperPipPeekSelectorShifted 128
    mem.size mem.size rfl (by omega) (by simp [Nat.max_eq_left hmem])

theorem clipperPipPeekSelectorMem_read64 {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperPipPeekSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperPipPeekSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperPipPeekSelectorShifted mem 128 64
    (by omega) (by omega) (by exact lt_usize _ (by omega)), hread64]

theorem clipperPipPeekSelectorMem_mload64 {mem : ByteArray}
    (hmem : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperPipPeekSelectorMem mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperPipPeekSelectorMem mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperPipPeekSelectorMem_size_of_ge hmem]; omega)
    (by decide)
    (clipperPipPeekSelectorMem_read64 (by omega) hread64)

theorem clipperPipPeekPostCallMem_size {mem out : ByteArray}
    (hmem : mem.size = 196) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).size = 196 := by
  unfold clipperPipPeekPostCallMem
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hmem]
    · rw [write_eq_gen out mem 128 out.size hzero le_rfl (by rw [hmem]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hmem]
      omega
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_eq_gen out mem 128 64 (by omega) (by omega) (by rw [hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem]
    omega

theorem clipperPipPeekPostCallMem_read64 {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperPipPeekPostCallMem
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hread64
    · rw [write_read_below_gen_extend out mem 128 out.size 64 hzero le_rfl
        (by rw [hmem]; omega) (by omega)]
      exact hread64
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_read_below_gen_extend out mem 128 64 64 (by omega) (by omega)
      (by rw [hmem]; omega) (by omega)]
    exact hread64

theorem clipperPipPeekPostCallMem_read128_long {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperPipPeekPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact byteArray_write_read_first_word_back out mem 128 64
    (by omega) (by omega) (by omega) (by rw [hmem]; omega)

theorem clipperPipPeekPostCallMem_read160_long {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 160 32 =
      out.extract 32 64 := by
  unfold clipperPipPeekPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  simpa [show 128 + 32 = 160 by norm_num] using
    byteArray_write_read_second_word_back out mem 128 64
      (by omega) (by omega) (by omega) (by rw [hmem]; omega)

theorem clipperPipPeekPostCallMem_mload128_long {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      clipperPipPeekValueWord out := by
  have hsize := clipperPipPeekPostCallMem_size hmem hout
  have hread := clipperPipPeekPostCallMem_read128_long hmem hlo hout
  have hcond :
      ¬ ((⟨128⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
    rw [hsize]
    decide
  rw [if_neg hcond]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding 128 32)) =
    clipperPipPeekValueWord out
  rw [hread]

theorem clipperPipPeekPostCallMem_mload160_long {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      clipperPipPeekHasWord out := by
  have hsize := clipperPipPeekPostCallMem_size hmem hout
  have hread := clipperPipPeekPostCallMem_read160_long hmem hlo hout
  have hcond :
      ¬ ((⟨160⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
    rw [hsize]
    decide
  rw [if_neg hcond]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding 160 32)) =
    clipperPipPeekHasWord out
  rw [hread]

theorem solcErrorStringMem0_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem0 mem).size = 196 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem solcErrorStringMem1_size_of_size196 {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem1 mem).size = 196 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size196 hmem]

theorem solcErrorStringMem2_size_of_size196 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem1_size_of_size196 hmem]

theorem solcErrorStringMem3_size_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size196 len hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem2_size_of_size196 len hmem]

theorem solcErrorStringMem3_read64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size196 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size196 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size196 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size196 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size196 len word hmem hread64)

theorem clipperGetFeedPriceIlkPatchPayload8747 (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 8747 8779 =
      ({ data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray } :
        ByteArray) := by
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : ilkBytes.size = 32 := by
    simpa [ilkBytes] using
      word_toBytesBE_toByteArray_size (EVM.Word.ofNat (fromBytesBigEndian bs))
  have hpost :
      PatchesWindowDisjoint32 8747 8779
        [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
          (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
          (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes)])
    (post :=
      [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
        (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes),
        (7936, vatBytes)])
    (off := 8747) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperGetFeedPriceIlkPush32Decode8746 (v : ClipperImmutables)
    {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨8746⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperRuntimePatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 8747 8779), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperGetFeedPriceIlkPatchPayload8747 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperGetFeedPriceJumpDest8836 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8836⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest8856 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8856⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest8878 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8878⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest8949 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8949⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest8969 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8969⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest8991 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8991⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9100) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetFeedPriceJumpDest9079 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9079⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9100) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceToSpotterIlksExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {ret scratch lot tab : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨8728⟩ (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : 164 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8824⟩
      (clipperSpotterTarget σ ee :: clipperSpotterTarget σ ee ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨164⟩ ::
        clipperSpotterIlksSelectorWord :: clipperSpotterTarget σ ee ::
        ⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by omega) (by decide) hread64
  have hselectorShift :
      UInt256.shiftLeft (⟨1823590043⟩ : UInt256) ⟨225⟩ =
        clipperSpotterIlksSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcallRead64 :
      (clipperSpotterIlksCalldataMem ilkWord mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [ilkWord] using clipperSpotterIlksCalldataMem_read64 ilkWord hmem hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksCalldataMem ilkWord mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperSpotterIlksCalldataMem ilkWord mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [clipperSpotterIlksCalldataMem_size_of_ge ilkWord hmem]; omega)
      (by decide) hcallRead64
  obtain ⟨_, _, rdSpotter⟩ := (evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov)]).sload
      (by clipper_runtime_decode) (by evm_ov)
  have rdSelector := evm_run rdSpotter with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨1823590043⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselectorShift] at rdSelector
  have rdSelectorMem := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (clipperSpotterIlksSelectorMem mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdIlk := rdSelectorMem.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperGetFeedPriceIlkPush32Decode8746 v hpatch hilk hlen)
    (by evm_ov)
  have rdCalldata := evm_run rdIlk with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (clipperSpotterIlksCalldataMem ilkWord mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdPreCall := evm_run rdCalldata with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperSpotterIlksSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [clipperSpotterTarget, clipperSpotterIlksCalldataMem, clipperIlkWord,
      ilkWord, hilk, clipperSpotterIlksSelectorWord, haddrMask, u256_land_comm,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨36⟩ = ⟨36⟩
        from by native_decide] using rdPreCall⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceSpotterIlksNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨8728⟩
      (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcodeSize : uniswapExtCodeSizeWord σ (clipperSpotterTarget σ ee) = ⟨0⟩)
    (hmem : 164 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 60 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd8824⟩ :=
    RD.clipperGetFeedPriceToSpotterIlksExtcodesizeGuard (v := v) (hpatch := hpatch)
      h hmem hread64 hov
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨8824⟩) (okPc := ⟨8836⟩)
    rd8824 hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceSpotterIlksPostCall {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State} {cA σ I} {g : UInt256}
    {ret scratch lot tab : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code I (Sat256.ofUInt256 g) s0 ⟨8728⟩
      (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (clipperSpotterTarget σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true)
    (hmem : 164 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 80 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I (Sat256.ofUInt256 g)
        s0 ⟨8840⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: clipperSpotterIlksSelectorWord ::
          clipperSpotterTarget σ I :: ⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
        (clipperSpotterIlksPostCallMem v mem o)
        (UInt256.ofNat 7) o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v)
        {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}
        (EVM.address (AccountAddress.ofUInt256 (clipperSpotterTarget σ I)))
        "spotterIlks" 0 [v.ilk]
        (z, { {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I} with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd8824⟩ :=
    RD.clipperGetFeedPriceToSpotterIlksExtcodesizeGuard (v := v) (hpatch := hpatch)
      h hmem hread64 (by omega)
  obtain ⟨gasWord, _, _, rd8839⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨8824⟩) (okPc := ⟨8836⟩)
      rd8824 hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest8836 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k8840, C8840, hΘpack, rd8840raw, hosz⟩ :=
    RD.call rd8839 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k8840, C8840, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) =
          UInt256.ofNat 7 := by
      native_decide
    simpa [clipperSpotterIlksPostCallMem, clipperIlkWord] using haw ▸ rd8840raw
  · refine callCoincides (cfg := config v)
      (evm := {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I})
      (name := "spotterIlks") (args := [v.ilk])
      (tgt := EVM.address (AccountAddress.ofUInt256 (clipperSpotterTarget σ I)))
      (targetWord := clipperSpotterTarget σ I)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := true)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (by simpa using clipperSpotterIlksEncode_eq v (mem := mem) hmem) ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [hperm] using hΘ

theorem RD.clipperGetFeedPriceSpotterIlksCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8840⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨8840⟩) (okPc := ⟨8856⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperGetFeedPriceSpotterIlksCallSuccessToDecode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target ret scratch lot tab : UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {R : List UInt256}
    (rd : RD code ee g s0 ⟨8840⟩
      (⟨1⟩ :: ⟨164⟩ :: clipperSpotterIlksSelectorWord :: target ::
        ⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8861⟩
      (⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd8858⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨8840⟩) (okPc := ⟨8856⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperGetFeedPriceJumpDest8856 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using
      (evm_run rd8858 with [
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov)])⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceSpotterIlksDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8861⟩
      (d0 :: d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksPostCallMem v mem o) (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : o.size < 64) (hout : o.size < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem o).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperSpotterIlksPostCallMem_mload64 v hmem hread64 hout
  have hlt :
      UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hshort
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8878⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := rdGuardPre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceSpotterIlksDecodeOkToPipPeekExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8861⟩
      (d0 :: d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksPostCallMem v mem o) (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8937⟩
      (clipperSpotterIlksPipTarget o :: clipperSpotterIlksPipTarget o ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨132⟩ ::
        clipperPipPeekSelectorWord :: clipperSpotterIlksPipTarget o ::
        ⟨0⟩ :: ⟨0⟩ :: clipperSpotterIlksPipWord o ::
        d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperPipPeekSelectorMem (clipperSpotterIlksPostCallMem v mem o))
      (UInt256.ofNat 7) o acc k' C' := by
  have hpostRead64 :
      (clipperSpotterIlksPostCallMem v mem o).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    clipperSpotterIlksPostCallMem_read64_long v hmem hread64 hlo hout
  have hpostSize :
      (clipperSpotterIlksPostCallMem v mem o).size = 196 :=
    clipperSpotterIlksPostCallMem_size_long v hmem hlo hout
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperSpotterIlksPostCallMem v mem o).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperSpotterIlksPostCallMem_mload64_long v hmem hread64 hlo hout
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperSpotterIlksPostCallMem v mem o).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        clipperSpotterIlksPipWord o :=
    clipperSpotterIlksPostCallMem_mload128_long v hmem hlo hout
  have hmload64Selector :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperPipPeekSelectorMem (clipperSpotterIlksPostCallMem v mem o)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperPipPeekSelectorMem
              (clipperSpotterIlksPostCallMem v mem o)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    clipperPipPeekSelectorMem_mload64
      (mem := clipperSpotterIlksPostCallMem v mem o)
      (by rw [hpostSize]; decide)
      hpostRead64
  have hlt :
      UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have hselectorShift :
      UInt256.shiftLeft clipperPipPeekSelectorWord ⟨224⟩ =
        clipperPipPeekSelectorShifted := by
    rfl
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8878⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8878 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8878 v hpatch) (by evm_ov)
  have rdPip := evm_run rd8878 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperSpotterIlksPipWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov)]
  have rdSelector := evm_run rdPip with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 clipperPipPeekSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselectorShift] at rdSelector
  have rdSelectorMem := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (clipperPipPeekSelectorMem (clipperSpotterIlksPostCallMem v mem o))
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdPreExt := evm_run rdSelectorMem with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64Selector (by decide) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperPipPeekSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [clipperSpotterIlksPipTarget, clipperPipPeekSelectorMem, haddrMask,
      u256_land_comm,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨4⟩ = ⟨4⟩
        from by native_decide] using rdPreExt⟩

theorem RD.clipperGetFeedPricePipPeekNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {target : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (rd : RD code ee g s0 ⟨8937⟩ (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨8937⟩) (okPc := ⟨8949⟩)
    rd hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) hov

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPricePipPeekPostCall {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State} {cA σ I} {g : UInt256}
    {target pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD code I (Sat256.ofUInt256 g) s0 ⟨8937⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨64⟩ ::
        ⟨132⟩ :: clipperPipPeekSelectorWord :: target :: ⟨0⟩ :: ⟨0⟩ ::
        pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcodeSize : uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true)
    (hcalldata :
      (config v).externalABI.encode? "peek" [] = some (mem.readWithPadding 128 4))
    (htarget : AccountAddress.ofUInt256 target = clipperSpotterIlksPipAddress rdata)
    (hov : R.length + 80 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I (Sat256.ofUInt256 g) s0 ⟨8953⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: clipperPipPeekSelectorWord ::
          target :: ⟨0⟩ :: ⟨0⟩ :: pipWord :: ret :: scratch :: lot :: tab :: R)
        (clipperPipPeekPostCallMem mem o) (UInt256.ofNat 7) o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v)
        {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}
        (EVM.address (clipperSpotterIlksPipAddress rdata)) "peek" 0 []
        (z, { {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I} with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd8952⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨8937⟩) (okPc := ⟨8949⟩)
      rd hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest8949 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k8953, C8953, hΘpack, rd8953raw, hosz⟩ :=
    RD.call rd8952 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k8953, C8953, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨4⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) =
          UInt256.ofNat 7 := by
      native_decide
    simpa [clipperPipPeekPostCallMem] using haw ▸ rd8953raw
  · refine callCoincides (cfg := config v)
      (evm := {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I})
      (name := "peek") (args := [])
      (tgt := EVM.address (clipperSpotterIlksPipAddress rdata))
      (targetWord := target)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := mem)
      (inOff := ⟨128⟩) (inSize := ⟨4⟩) (callPerm := true)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (by simpa using hcalldata) ?_
    · rw [← htarget]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [hperm] using hΘ

theorem RD.clipperGetFeedPricePipPeekCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8953⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨8953⟩) (okPc := ⟨8969⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperGetFeedPricePipPeekCallSuccessToDecode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target pipWord ret scratch lot tab : UInt256} {mem o : ByteArray}
    {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8953⟩
      (⟨1⟩ :: ⟨132⟩ :: clipperPipPeekSelectorWord :: target :: ⟨0⟩ :: ⟨0⟩ ::
        pipWord :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8974⟩
      (⟨0⟩ :: ⟨0⟩ :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd8971⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨8953⟩) (okPc := ⟨8969⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperGetFeedPriceJumpDest8969 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using
      (evm_run rd8971 with [
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov)])⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPricePipPeekDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : o.size < 64) (hout : o.size < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    rw [hmem, hread64]
    native_decide
  have hlt :
      UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hshort
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := rdGuardPre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPricePipPeekHasFalseReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = o.extract 0 32)
    (hread160 : mem.readWithPadding 160 32 = o.extract 32 64)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hhasFalse : clipperPipPeekHasWord o = ⟨0⟩)
    (hov : R.length + 80 ≤ 1024) :
    RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    rw [hmem, hread64]
    native_decide
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        clipperPipPeekValueWord o := by
    have hcond :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
      rw [hmem]
      decide
    rw [if_neg hcond]
    change UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 128 32)) =
      clipperPipPeekValueWord o
    rw [hread128]
  have hmload160 :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
        clipperPipPeekHasWord o := by
    have hcond :
        ¬ ((⟨160⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
      rw [hmem]
      decide
    rw [if_neg hcond]
    change UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 160 32)) =
      clipperPipPeekHasWord o
    rw [hread160]
  have hlt :
      UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8991 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8991 v hpatch) (by simp only [List.length_cons]; omega)
  have rdHasCheck := evm_run rd8991 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekValueWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekHasWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9079⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdRevert0 := rdHasCheck.jumpiNT (by clipper_runtime_decode) hhasFalse
    (by simp only [List.length_cons]; omega)
  let invalidPriceWord : UInt256 :=
    UInt256.shiftLeft
      ⟨98539532077487810267029201284522128899303115678565⟩ ⟨88⟩
  have hselector :
      UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ = solcErrorStringSelector := by
    rfl
  have hInvalidPrice :
      UInt256.shiftLeft
        ⟨98539532077487810267029201284522128899303115678565⟩ ⟨88⟩ =
        invalidPriceWord := by
    rfl
  have rdMload := evm_run rdRevert0 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdSelector := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselector] at rdSelector
  have rdPrefix := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨21⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨21⟩ mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨98539532077487810267029201284522128899303115678565⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨88⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hInvalidPrice] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨21⟩ invalidPriceWord mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 ⟨21⟩ invalidPriceWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

end Benchmarks.Dss.Clipper
