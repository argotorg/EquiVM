import Tests.Pipeline.VyperWrapper.CallHelpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `unwrap(uint256)`

Dispatcher bucket 6, arm entry pc 909: the guard, `require(shares[msg.sender] >= sharesOut)` (pc
919, revert at 941), `held = staticcall TOKEN.balanceOf(self)` (pc 1053, the `STATICCALL` at
1085, bubble 1090, `returndatasize` 1097), `sharesOut * held` (pc 1106), the divisor (pc 1136),
the division and `shares[msg.sender] -= sharesOut` (pc 1149/1186), `totalShares -= sharesOut`
and `ok = extcall TOKEN.transfer(msg.sender, amount)` (pc 1209, the `CALL` at 1254, bubble 1259,
the decode checks 1266/1289), `require(ok)` (pc 1300, revert 1321) and the `RETURN` (pc 1435).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperCalls
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

abbrev shRef : StorageRef := { base := "shares", steps := [.mindex (.env .caller)] }

theorem unwrapBody_eq : unwrapTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .ge (.storage shRef) (.var "sharesOut")),
     .letDecl "__a0" (some (.elem .address)) (.immutable "TOKEN"),
     .externalCall (.var "__a0") "balanceOf" (.intLit 0) [.env .this] "held" false,
     .letDecl "amount" (some (.elem (.int (.uint ⟨256, by decide⟩))))
       (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "sharesOut") (.var "held"))) (.storage tsRef)),
     .assign .storage shRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage shRef) (.var "sharesOut"))),
     .assign .storage tsRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage tsRef) (.var "sharesOut"))),
     .letDecl "__a2" (some (.elem .address)) (.immutable "TOKEN"),
     .externalCall (.var "__a2") "transfer" (.intLit 0) [.env .caller, .var "amount"] "ok" true,
     .require (.var "ok"),
     .emit "Unwrapped" [.env .caller, .var "amount"],
     .return [.var "amount"]] := by rfl

abbrev uStore (I : ExecutionEnv) : Store := (∅ : Store).insert "sharesOut" (uint256Value (argWord I))

theorem uDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (unwrapTransition.params.map Param.name)
      (transitionSignature unwrapTransition).paramTypes I.calldata = some (uStore I) := by
  simpa [config, contract, Syntax.contractSyntax, unwrapTransition, uStore, argWord_eq] using
    decodeMode_uint256_ok "sharesOut" I.calldata hsz36

theorem uDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (unwrapTransition.params.map Param.name)
      (transitionSignature unwrapTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, unwrapTransition] using
    decodeMode_uint256_none_short "sharesOut" I.calldata hsz hshort

/-- `shares[msg.sender] := v` through the backend. -/
theorem assignSharesCaller (imms L : Store) (evm : EVM.State) (v : UInt256) (hL : L.get? "shares" = none) :
    assignStorageRef? config (frame imms L) evm .storage shRef (uint256Value v) =
      .ok (frame imms L, Stele.EVM.storageStore evm evm.executionEnv.codeOwner (sharesSlot evm.executionEnv.source) v) := by
  apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
    (er := { base := "shares", steps := [.mindex (.address evm.executionEnv.source)] })
    (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (sharesSlot evm.executionEnv.source))
    (hbase := hL)
    (her := by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax]) (hloc := rfl)
  erw [storageLocStore_uint256]

/-- `totalShares := v` through the backend. -/
theorem assignTs (imms L : Store) (evm : EVM.State) (v : UInt256) (hL : L.get? "totalShares" = none) :
    assignStorageRef? config (frame imms L) evm .storage tsRef (uint256Value v) =
      .ok (frame imms L, Stele.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 2) v) := by
  apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
    (er := { base := "totalShares", steps := [] })
    (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 2))
    (hbase := hL) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
  erw [storageLocStore_uint256]

/-! ### The memories along the body -/

/-- After the `balanceOf` call, `held` at 64 and `amount` at 96, then the caller's hash scratch. -/
abbrev uM4 (t : UInt256) (I : ExecutionEnv) (hw : UInt256) : ByteArray :=
  hw.toByteArray.write 0 (hw.toByteArray.write 0 (balMem t I (hashMem (wrapperDispatchMem 6) I)) 96 32) 64 32
abbrev uM5 (t : UInt256) (I : ExecutionEnv) (hw amt : UInt256) : ByteArray := amt.toByteArray.write 0 (uM4 t I hw) 96 32
abbrev uM6 (t : UInt256) (I : ExecutionEnv) (hw amt : UInt256) : ByteArray := hashMem (uM5 t I hw amt) I

theorem uM_sizes (t : UInt256) (I : ExecutionEnv) (hw amt : UInt256) :
    (hashMem (wrapperDispatchMem 6) I).size = 64 ∧
    (balMem t I (hashMem (wrapperDispatchMem 6) I)).size = 160 ∧
    (hw.toByteArray.write 0 (balMem t I (hashMem (wrapperDispatchMem 6) I)) 96 32).size = 160 ∧
    (uM4 t I hw).size = 160 ∧ (uM5 t I hw amt).size = 160 ∧ (uM6 t I hw amt).size = 160 := by
  have h0 : (hashMem (wrapperDispatchMem 6) I).size = 64 := hashMem_size32 _ _ (dispatchMem_size 6 (by decide))
  have h1 : (balMem t I (hashMem (wrapperDispatchMem 6) I)).size = 160 :=
    (balMem_sizes t I _ (by rw [h0]; decide)).2.2
  have h2 : (hw.toByteArray.write 0 (balMem t I (hashMem (wrapperDispatchMem 6) I)) 96 32).size = 160 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]; exact h1
  have h3 : (uM4 t I hw).size = 160 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h2] <;> omega)]; exact h2
  have h4 : (uM5 t I hw amt).size = 160 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h3] <;> omega)]; exact h3
  exact ⟨h0, h1, h2, h3, h4, by rw [hashMem_size_ge _ _ (by rw [h4] <;> omega)]; exact h4⟩

theorem uM6_read96 (t : UInt256) (I : ExecutionEnv) (hw amt : UInt256) :
    (uM6 t I hw amt).readWithPadding 96 32 = amt.toByteArray := by
  obtain ⟨-, -, -, h3, h4, -⟩ := uM_sizes t I hw amt
  rw [hashMem_read_above _ _ 96 (by decide) (by rw [h4] <;> omega),
    toByteArray_write_read_back_of_gap _ _ 96 (by rw [h3]; exact lt_usize _ (by decide))]

/-- `unwrap(uint256)`: the theorem `Correct.lean` routes selector 5 to. -/
theorem wrapperUnwrapBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 5)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 5) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := token_of_fit hfit
  obtain ⟨_, _, rd⟩ := wrapperReachUnwrapBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some unwrapTransition :=
    wrapperDispatch_unwrap (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := wrapperBlocks.wrapper_block_909_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (uDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := wrapperBlocks.wrapper_block_909_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [unwrapBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := wrapperBlocks.wrapper_block_909_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have hdec := uDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame imms (uStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hso0 : ∀ evm, evalExpr? config (frame imms (uStore I)) evm (.var "sharesOut") = .ok (uint256Value (argWord I)) :=
    fun evm => evalVar imms _ _ "sharesOut" _ (store_get_self _ _ _)
  have hsh0 : evalExpr? config (frame imms (uStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage shRef) =
      .ok (uint256Value (solcSlotWordAt (sharesSlot I.source) σ I)) := by
    rw [evalSharesCallerRead imms _ _ (by simp), storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  have hge := evalExpr_ge_words hsh0 (hso0 _)
  -- pc 919: `shares[msg.sender] >= sharesOut`
  have hkec0 := keccak_hashMem32 (wrapperDispatchMem 6) I (dispatchMem_size 6 (by decide))
  by_cases hbal : (argWord I).toNat ≤ (solcSlotWordAt (sharesSlot I.source) σ I).toNat
  swap
  · obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_919_fallthrough (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hkec0, slotWord_eq, ult_one (by show (solcSlotWordAt (sharesSlot I.source) σ I).toNat < (argWord I).toNat; omega)]
        decide) rd1
    have rd3 := wrapperBlocks.wrapper_block_941 (by simp) rd2
    refine RDrev.reEquivExecutionRevert hcode' rd3 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.requireFalse (by rw [hge, decide_eq_false hbal]))))
  have hgeT : evalExpr? config (frame imms (uStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ge (.storage shRef) (.var "sharesOut")) = .ok (.bool true) := by
    rw [hge, decide_eq_true hbal]
  obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_919_taken (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec0, slotWord_eq, ult_zero hbal]
      decide)
    (by apply D_J_contains_append_left; jump_dest) rd1
  simp only [wrapperBlocks.wrapper_block_919_taken_memory, ulit_toNat' 32 (by decide),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd2
  -- pc 1053: the `STATICCALL` at 1085
  have rd3 := wrapperBlocks.wrapper_block_1053 (immWords := wordsOf imms) (by simp) rd2
  simp only [wrapperBlocks.wrapper_block_1053_stack, wrapperBlocks.wrapper_block_1053_memory, wordsOf_TOKEN' hget,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 96 (by decide), ulit_toNat' 128 (by decide)] at rd3
  have hM0 : 32 ≤ (hashMem (wrapperDispatchMem 6) I).size ∧ (hashMem (wrapperDispatchMem 6) I).size ≤ 96 := by
    rw [hashMem_size32 _ _ (dispatchMem_size 6 (by decide))]; decide
  obtain ⟨evm', σ', z, out, _, _, hcall, hs', rd4, hsize1⟩ :=
    typedStaticCallBridge (cfg := config) (name := "balanceOf") (args := [.address I.codeOwner]) rd3 SourceState.init
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1085⟩ : UInt256), .STATICCALL, none))
      (by rw [encode_balanceOf, ulit_toNat' 124 (by decide), ulit_toNat' 36 (by decide), balMem_input _ _ _ hM0])
      (by rw [ulit_toNat' 36 (by decide)]; norm_num) (by simp)
  rw [ofUInt256_ofNat_eq_address] at hcall
  have rd5 := RD.normalizePC (pc' := UInt256.ofNat 1086) rd4 (by native_decide)
  set L1 : Store := (uStore I).insert "__a0" (.address a) with hL1
  have hrecv : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") = .ok (.address a) :=
    evalVar imms _ _ "__a0" _ (by rw [hL1]; exact store_get_self _ _ _)
  have heth : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) = .ok (.int 0) := by
    rw [evalExpr?]; rfl
  have hargs : evalExprs? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.env .this] =
      .ok [.address I.codeOwner] := by
    rw [evalExprs?, evalThis, evalExprs?]; rfl
  cases z with
  | false =>
    have rd6 := wrapperBlocks.wrapper_block_1086_fallthrough (by simp) (by decide) rd5
    have rd7 := wrapperBlocks.wrapper_block_1090 (by simp [wrapperBlocks.wrapper_block_1086_fallthrough_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode' rd7 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hrecv heth hargs hcall)))))
  | true =>
  have rd6 := wrapperBlocks.wrapper_block_1086_taken (by simp) (by decide)
    (by apply D_J_contains_append_left; jump_dest) rd5
  simp only [wrapperBlocks.wrapper_block_1086_taken_stack] at rd6
  have hout : out.size < UInt256.size := lt_size_of_lt_sign (by omega)
  by_cases hshortR : out.size < 32
  · have rd7 := wrapperBlocks.wrapper_block_1097_taken (by simp)
      (by rw [ult_one (by rw [ulit_toNat' _ hout, ulit_toNat' 32 (by decide)]; exact hshortR)]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd6
    have rd8 := wrapperBlocks.wrapper_block_1760 (by simp) rd7
    refine RDrev.reEquivExecutionRevert hcode' rd8 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv heth hargs hcall
            (by rw [decode_balanceOf, decodeReturn_uint256_short out hshortR]; rfl))))))
  have h32 : 32 ≤ out.size := by omega
  have rd7 := wrapperBlocks.wrapper_block_1097_fallthrough (by simp)
    (by exact ult_zero (by rw [ulit_toNat' _ hout, ulit_toNat' 32 (by decide)]; omega)) rd6
  obtain ⟨hw, hhw⟩ : ∃ hw, retWord out = hw := ⟨_, rfl⟩
  obtain ⟨hu0, hu1, hu2, hu3, -, -⟩ := uM_sizes (addrWord a) I hw ⟨0⟩
  rw [ulit_toNat' 96 (by decide), min32_toNat out.size h32 hout,
    write_out_eq_word out _ 96 h32 (by rw [hu1] <;> decide), hhw] at rd7
  have hload96 : memLoad (UInt256.ofNat 96) (hw.toByteArray.write 0 (balMem (addrWord a) I (hashMem (wrapperDispatchMem 6) I)) 96 32) = hw :=
    memLoad_write_back _ _ 96 (by decide) (by rw [hu1]; exact lt_usize _ (by decide))
  have hload64 : memLoad (UInt256.ofNat 64) (uM4 (addrWord a) I hw) = hw :=
    memLoad_write_back _ _ 64 (by decide) (by rw [hu2]; exact lt_usize _ (by decide))
  -- Stele after the first call
  set L2 : Store := L1.insert "held" (uint256Value hw) with hL2
  have hdecode : config.externalABI.decode? "balanceOf" out = some [uint256Value hw] := by
    rw [decode_balanceOf, decodeReturn_uint256_ok out h32 (by omega), hhw]; rfl
  have hcallS : ExecStmt fork config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.externalCall (.var "__a0") "balanceOf" (.intLit 0) [.env .this] "held" false) (.ok (frame imms L2) evm') :=
    @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") a
      (.intLit 0) [.env .this] [.address I.codeOwner] "balanceOf" evm' out false [uint256Value hw] "held"
      hrecv heth hargs hcall hdecode
  have hso : ∀ evm, evalExpr? config (frame imms L2) evm (.var "sharesOut") = .ok (uint256Value (argWord I)) := fun evm =>
    evalVar imms _ _ "sharesOut" _ (by rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide)]; exact store_get_self _ _ _)
  have hheld : ∀ evm, evalExpr? config (frame imms L2) evm (.var "held") = .ok (uint256Value hw) := fun evm =>
    evalVar imms _ _ "held" _ (by rw [hL2]; exact store_get_self _ _ _)
  have htsPost : evalExpr? config (frame imms L2) evm' (.storage tsRef) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ' I)) := by
    rw [evalTsRead imms _ _ (by simp [hL2, hL1]), hs'.storageRead]; rfl
  -- pc 1106: `sharesOut * held`
  by_cases hfit : (argWord I).toNat * hw.toNat < UInt256.size
  swap
  · have rd8 := wrapperBlocks.wrapper_block_1106_taken (by simp)
      (by
        simp only [ulit_toNat' 64 (by decide)]
        rw [hload96, hload64]
        exact mulCheck_overflow _ _ (by show UInt256.size ≤ (argWord I).toNat * hw.toNat; omega))
      (by apply D_J_contains_append_left; jump_dest) rd7
    have rd9 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1106_taken_stack]) rd8
    refine RDrev.reEquivExecutionRevert hcode' rd9 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consRevert (ExecStmt.letDeclRevert
              (evalExpr_binary_revert_left (by decide) (by decide)
                (evalExpr_uint256_mul_overflow (hso _) (hheld _) (by omega)))))))))
  have rd8 := wrapperBlocks.wrapper_block_1106_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 64 (by decide)]
      rw [hload96, hload64]
      exact mulCheck_ok _ _ hfit) rd7
  simp only [wrapperBlocks.wrapper_block_1106_fallthrough_stack, wrapperBlocks.wrapper_block_1106_fallthrough_memory,
    ulit_toNat' 64 (by decide)] at rd8
  rw [hload96, hload64] at rd8
  have hmul := evalExpr_uint256_mul (hso evm') (hheld evm') hfit
  -- pc 1136: the divisor
  by_cases hts' : solcSlotWordAt (UInt256.ofNat 2) σ' I = ⟨0⟩
  · obtain ⟨_, _, rd9⟩ := wrapperBlocks.wrapper_block_1136_taken (by simp) (by rw [slotWord_eq, hts']; decide)
      (by apply D_J_contains_append_left; jump_dest) rd8
    have rd10 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1136_taken_stack]) rd9
    refine RDrev.reEquivExecutionRevert hcode' rd10 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consRevert (ExecStmt.letDeclRevert (evalExpr_div_zero hmul (by rw [htsPost, hts']))))))))
  obtain ⟨_, _, rd9⟩ := wrapperBlocks.wrapper_block_1136_fallthrough (by simp)
    (by rw [slotWord_eq]; exact isZero_eq_zero_of_ne hts') rd8
  simp only [wrapperBlocks.wrapper_block_1136_fallthrough_stack] at rd9
  rw [slotWord_eq] at rd9
  -- pc 1149: `amount`, then `shares[msg.sender] - sharesOut`
  obtain ⟨amt, hamt⟩ : ∃ amt, UInt256.div (UInt256.mul (argWord I) hw) (solcSlotWordAt (UInt256.ofNat 2) σ' I) = amt := ⟨_, rfl⟩
  have hdiv : evalExpr? config (frame imms L2) evm'
      (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "sharesOut") (.var "held"))) (.storage tsRef)) =
      .ok (uint256Value amt) := by
    rw [evalExpr_uint256_div hmul htsPost hts', hamt]
  set L3 : Store := L2.insert "amount" (uint256Value amt) with hL3
  have hamtV : ∀ evm, evalExpr? config (frame imms L3) evm (.var "amount") = .ok (uint256Value amt) := fun evm =>
    evalVar imms _ _ "amount" _ (by rw [hL3]; exact store_get_self _ _ _)
  have hso3 : ∀ evm, evalExpr? config (frame imms L3) evm (.var "sharesOut") = .ok (uint256Value (argWord I)) := fun evm =>
    evalVar imms _ _ "sharesOut" _ (by rw [hL3, store_get_ne _ _ (by decide), hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide)]; exact store_get_self _ _ _)
  have hsh' : evalExpr? config (frame imms L3) evm' (.storage shRef) =
      .ok (uint256Value (solcSlotWordAt (sharesSlot I.source) σ' I)) := by
    rw [evalSharesCallerRead imms _ _ (by simp [hL3, hL2, hL1]), hs'.storageRead, hs'.env]
    rfl
  obtain ⟨-, -, -, -, hu4, hu5⟩ := uM_sizes (addrWord a) I hw amt
  have hkec5 := keccak_hashMem_ge (uM5 (addrWord a) I hw amt) I (by rw [hu4]; decide)
  by_cases hund : (argWord I).toNat ≤ (solcSlotWordAt (sharesSlot I.source) σ' I).toNat
  swap
  · obtain ⟨_, _, rd10⟩ := wrapperBlocks.wrapper_block_1149_taken (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hamt, hkec5, slotWord_eq, ugt_one (by
          show (solcSlotWordAt (sharesSlot I.source) σ' I).toNat < (UInt256.sub (solcSlotWordAt (sharesSlot I.source) σ' I) (argWord I)).toNat
          rw [usub_toNat_underflow (by omega)]
          have hlt := (argWord I).val.isLt
          change (argWord I).toNat < UInt256.size at hlt
          omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd9
    have rd11 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1149_taken_stack]) rd10
    refine RDrev.reEquivExecutionRevert hcode' rd11 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consRevert (ExecStmt.assignExprRevert
                (evalExpr_uint256_sub_underflow hsh' (hso3 _) (by omega)))))))))
  obtain ⟨_, _, rd10⟩ := wrapperBlocks.wrapper_block_1149_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hamt, hkec5, slotWord_eq]
      exact ugt_zero (by
        show (UInt256.sub (solcSlotWordAt (sharesSlot I.source) σ' I) (argWord I)).toNat ≤ (solcSlotWordAt (sharesSlot I.source) σ' I).toNat
        rw [usub_toNat hund]; omega)) rd9
  simp only [wrapperBlocks.wrapper_block_1149_fallthrough_stack, wrapperBlocks.wrapper_block_1149_fallthrough_memory,
    ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd10
  rw [hamt, hkec5, slotWord_eq] at rd10
  have hsub1 := evalExpr_uint256_sub hsh' (hso3 _) hund
  set sh1 := UInt256.sub (solcSlotWordAt (sharesSlot I.source) σ' I) (argWord I) with hsh1
  have hassign1 : assignStorageRef? config (frame imms L3) evm' .storage shRef (uint256Value sh1) =
      .ok (frame imms L3, Stele.EVM.storageStore evm' I.codeOwner (sharesSlot I.source) sh1) := by
    rw [assignSharesCaller imms _ _ _ (by simp [hL3, hL2, hL1]), hs'.env]
  set evm1 := Stele.EVM.storageStore evm' I.codeOwner (sharesSlot I.source) sh1 with hevm1
  have hs1 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (sstoreAccountMap I.codeOwner σ' (sharesSlot I.source) sh1) evm1 :=
    hs'.storageWrite _ _
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the `shares` store (pc 1191) halts
    have hpf : I.perm = false := by simpa using hperm
    have r1 := rd10.swap1
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1186⟩ : UInt256), .SWAP1, none)) (by evm_ov)
    have r2 := r1.pop
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1187⟩ : UInt256), .POP, none)) (by evm_ov)
    have r3 := r2.swap1
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1188⟩ : UInt256), .SWAP1, none)) (by evm_ov)
    have r4 := r3.pop
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1189⟩ : UInt256), .POP, none)) (by evm_ov)
    have r5 := r4.dup2
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1190⟩ : UInt256), .DUP2, none)) (by evm_ov)
    have rs := r5.sstoreStatic hpf
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1191⟩ : UInt256), .SSTORE, none)) (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consStatic (ExecStmt.assignStatic hsub1 hassign1 (by rw [hs'.env]; exact hpf))))))))
  -- pc 1186: the `shares` store, then `totalShares - sharesOut`
  have hts1 : evalExpr? config (frame imms L3) evm1 (.storage tsRef) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) (sstoreAccountMap I.codeOwner σ' (sharesSlot I.source) sh1) I)) := by
    rw [evalTsRead imms _ _ (by simp [hL3, hL2, hL1]), hs1.storageRead]; rfl
  set ts1 := solcSlotWordAt (UInt256.ofNat 2) (sstoreAccountMap I.codeOwner σ' (sharesSlot I.source) sh1) I with hts1def
  by_cases hund2 : (argWord I).toNat ≤ ts1.toNat
  swap
  · obtain ⟨_, _, rd11⟩ := wrapperBlocks.wrapper_block_1186_taken (by simp) hperm
      (by
        rw [slotWord_eq, ugt_one (by
          show ts1.toNat < (UInt256.sub ts1 (argWord I)).toNat
          rw [usub_toNat_underflow (by omega)]
          have hlt := (argWord I).val.isLt
          change (argWord I).toNat < UInt256.size at hlt
          omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd10
    have rd12 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1186_taken_stack]) rd11
    refine RDrev.reEquivExecutionRevert hcode' rd12 hd hdec ?_
    rw [unwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs'.env] using hperm)) hsub1 hassign1)
                (ExecBlock.consRevert (ExecStmt.assignExprRevert
                  (evalExpr_uint256_sub_underflow hts1 (hso3 _) (by omega))))))))))
  obtain ⟨_, _, rd11⟩ := wrapperBlocks.wrapper_block_1186_fallthrough (by simp) hperm
    (by
      rw [slotWord_eq]
      exact ugt_zero (by
        show (UInt256.sub ts1 (argWord I)).toNat ≤ ts1.toNat
        rw [usub_toNat hund2]; omega)) rd10
  simp only [wrapperBlocks.wrapper_block_1186_fallthrough_stack] at rd11
  rw [slotWord_eq] at rd11
  have hsub2 := evalExpr_uint256_sub hts1 (hso3 _) hund2
  set ts2 := UInt256.sub ts1 (argWord I) with hts2
  have hassign2 : assignStorageRef? config (frame imms L3) evm1 .storage tsRef (uint256Value ts2) =
      .ok (frame imms L3, Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 2) ts2) := by
    rw [assignTs imms _ _ _ (by simp [hL3, hL2, hL1]), hs1.env]
  set evm2 := Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 2) ts2 with hevm2
  have hs2 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ' (sharesSlot I.source) sh1) (UInt256.ofNat 2) ts2) evm2 :=
    hs1.storageWrite _ _
  -- pc 1209: the `totalShares` store and the `CALL` at 1254
  obtain ⟨_, _, _, rd12⟩ := wrapperBlocks.wrapper_block_1209 (immWords := wordsOf imms) (by simp) hperm rd11
  simp only [wrapperBlocks.wrapper_block_1209_stack, wrapperBlocks.wrapper_block_1209_memory, wordsOf_TOKEN' hget,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 96 (by decide), ulit_toNat' 160 (by decide),
    ulit_toNat' 192 (by decide), ulit_toNat' 224 (by decide)] at rd12
  have hamtLoad : memLoad (UInt256.ofNat 96) ((callerWord I).toByteArray.write 0 (selT.toByteArray.write 0
      ((addrWord a).toByteArray.write 0 (uM6 (addrWord a) I hw amt) 0 32) 160 32) 192 32) = amt :=
    memLoad_of_read _ 96 amt (by decide) (by rw [(trMem_sizes (addrWord a) I amt _ hu5).2.2.1]; decide)
      (by rw [trMem_pre_read96 _ _ _ hu5, uM6_read96])
  rw [hamtLoad] at rd12
  obtain ⟨ht0, ht1, ht2, ht3⟩ := trMem_sizes (addrWord a) I amt (uM6 (addrWord a) I hw amt) hu5
  obtain ⟨evm3, σ3, z2, out2, _, _, hcall2, hs3, rd13, hsize2⟩ :=
    typedCallBridge (cfg := config) (name := "transfer") (args := [.address I.source, uint256Value amt]) rd12 hs2
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1254⟩ : UInt256), .CALL, none))
      (by rw [encode_transfer, ulit_toNat' 188 (by decide), ulit_toNat' 68 (by decide), trMem_input _ _ _ _ hu5])
      (by rw [ulit_toNat' 68 (by decide)]; norm_num) (by simp)
  rw [ofUInt256_ofNat_eq_address] at hcall2
  have rd14 := RD.normalizePC (pc' := UInt256.ofNat 1255) rd13 (by native_decide)
  set L4 : Store := L3.insert "__a2" (.address a) with hL4
  have hrecv2 : evalExpr? config (frame imms L4) evm2 (.var "__a2") = .ok (.address a) :=
    evalVar imms _ _ "__a2" _ (by rw [hL4]; exact store_get_self _ _ _)
  have heth2 : evalExpr? config (frame imms L4) evm2 (.intLit 0) = .ok (.int 0) := by
    rw [evalExpr?]; rfl
  have hargs2 : evalExprs? config (frame imms L4) evm2 [.env .caller, .var "amount"] =
      .ok [.address I.source, uint256Value amt] := by
    rw [evalExprs?, evalExpr_caller, hs2.env, evalExprs?,
      evalVar imms _ _ "amount" _ (by rw [hL4, store_get_ne _ _ (by decide), hL3]; exact store_get_self _ _ _), evalExprs?]
    rfl
  -- the body up to the second call
  have hprefix : ∀ result, ExecBlock fork config (frame imms L4) evm2
      [.externalCall (.var "__a2") "transfer" (.intLit 0) [.env .caller, .var "amount"] "ok" true,
       .require (.var "ok"), .emit "Unwrapped" [.env .caller, .var "amount"], .return [.var "amount"]] result →
      ExecBlock fork config (frame imms (uStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) unwrapTransition.body result := by
    intro result h
    rw [unwrapBody_eq]
    exact ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcallS
            (ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs'.env] using hperm)) hsub1 hassign1)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) hsub2 hassign2)
                  (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _)) h)))))))
  cases z2 with
  | false =>
    have rd15 := wrapperBlocks.wrapper_block_1255_fallthrough (by simp) (by decide) rd14
    have rd16 := wrapperBlocks.wrapper_block_1259 (by simp [wrapperBlocks.wrapper_block_1255_fallthrough_stack]) rd15
    exact RDrev.reEquivExecutionRevert hcode' rd16 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hrecv2 heth2 hargs2 hcall2))))
  | true =>
  have rd15 := wrapperBlocks.wrapper_block_1255_taken (by simp) (by decide)
    (by apply D_J_contains_append_left; jump_dest) rd14
  simp only [wrapperBlocks.wrapper_block_1255_taken_stack] at rd15
  have hout2 : out2.size < UInt256.size := lt_size_of_lt_sign (by omega)
  have h192 : 160 + 32 < UInt256.size := lt_size_of_lt_sign (by norm_num)
  by_cases hshort2 : out2.size < 32
  · have rd16 := wrapperBlocks.wrapper_block_1266_taken (by simp) (rdsCheck_short 160 192 out2.size rfl h192 hshort2)
      (by apply D_J_contains_append_left; jump_dest) rd15
    have rd17 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1266_taken_stack]) rd16
    exact RDrev.reEquivExecutionRevert hcode' rd17 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv2 heth2 hargs2 hcall2
        (by rw [decode_transfer, decodeReturn_bool_short out2 hshort2]; rfl)))))
  have h32' : 32 ≤ out2.size := by omega
  have rd16 := wrapperBlocks.wrapper_block_1266_fallthrough (by simp)
    (rdsCheck_ok 160 192 out2.size rfl h192 h32' hout2) rd15
  simp only [wrapperBlocks.wrapper_block_1266_fallthrough_stack] at rd16
  obtain ⟨bw, hbw⟩ : ∃ bw, retWord out2 = bw := ⟨_, rfl⟩
  rw [ulit_toNat' 160 (by decide), min32_toNat out2.size h32' hout2,
    write_out_eq_word out2 _ 160 h32' (by rw [ht3] <;> omega), hbw] at rd16
  set M8 := bw.toByteArray.write 0 (trMem (addrWord a) I amt (uM6 (addrWord a) I hw amt)) 160 32 with hM8
  have hM8size : M8.size = 256 := by
    rw [hM8, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [ht3] <;> omega)]; exact ht3
  have hload160 : memLoad (UInt256.ofNat 160) M8 = bw :=
    memLoad_write_back _ _ 160 (by decide) (by rw [ht3]; exact lt_usize _ (by decide))
  -- pc 1289: the bool validation
  by_cases hbool : bw.toNat < 2
  swap
  · have rd17 := wrapperBlocks.wrapper_block_1289_taken (by simp)
      (by rw [hload160]; intro h; exact hbool (u256_lt_two_of_shiftRight1_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd16
    have rd18 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1289_taken_stack]) rd17
    exact RDrev.reEquivExecutionRevert hcode' rd18 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv2 heth2 hargs2 hcall2
        (by
          rw [decode_transfer, decodeReturn_bool_noncanon out2 h32' (by omega)
            (by rw [hbw]; intro h; apply hbool; rw [h]; decide) (by rw [hbw]; intro h; apply hbool; rw [h]; decide)]
          rfl)))))
  have rd17 := wrapperBlocks.wrapper_block_1289_fallthrough (by simp)
    (by rw [hload160]; exact u256_shiftRight1_zero_of_lt _ hbool) rd16
  simp only [wrapperBlocks.wrapper_block_1289_fallthrough_stack] at rd17
  rw [hload160] at rd17
  have hM8'size : (bw.toByteArray.write 0 M8 256 32).size = 288 :=
    toByteArray_write32_size_of_ge _ _ 256 256 288 hM8size (by omega) (lt_usize _ (by decide)) rfl
  have hload256 : memLoad (UInt256.ofNat 256) (bw.toByteArray.write 0 M8 256 32) = bw :=
    memLoad_write_back _ _ 256 (by decide) (by rw [hM8size]; exact lt_usize _ (by decide))
  have hload128 : memLoad (UInt256.ofNat 128) (bw.toByteArray.write 0 (bw.toByteArray.write 0 M8 256 32) 128 32) = bw :=
    memLoad_write_back _ _ 128 (by decide) (by rw [hM8'size]; exact lt_usize _ (by decide))
  -- pc 1300: `require(ok)`
  by_cases hok : bw = ⟨0⟩
  · have rd18 := wrapperBlocks.wrapper_block_1300_fallthrough (by simp)
      (by simp only [ulit_toNat' 256 (by decide), ulit_toNat' 128 (by decide)]; rw [hload256, hload128, hok]; rfl) rd17
    have rd19 := wrapperBlocks.wrapper_block_1321 (by simp [wrapperBlocks.wrapper_block_1300_fallthrough_stack]) rd18
    have hdec2 : config.externalABI.decode? "transfer" out2 = some [.bool false] := by
      rw [decode_transfer, decodeReturn_bool_zero out2 h32' (by omega) (by rw [hbw]; exact hok)]; rfl
    have hcall2S : ExecStmt fork config (frame imms L4) evm2
        (.externalCall (.var "__a2") "transfer" (.intLit 0) [.env .caller, .var "amount"] "ok" true)
        (.ok (frame imms (L4.insert "ok" (.bool false))) evm3) :=
      @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L4) evm2 (.var "__a2") a (.intLit 0)
        [.env .caller, .var "amount"] [.address I.source, uint256Value amt] "transfer" evm3 out2 true [.bool false] "ok"
        hrecv2 heth2 hargs2 hcall2 hdec2
    exact RDrev.reEquivExecutionRevert hcode' rd19 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consNormal hcall2S (ExecBlock.consRevert (ExecStmt.requireFalse
        (evalVar imms _ _ "ok" _ (store_get_self _ _ _)))))))
  have hone : bw = ⟨1⟩ := by
    have h0 : bw.toNat ≠ 0 := fun h => hok (u256_inj (by rw [h]; rfl))
    exact u256_inj (by show bw.toNat = 1; omega)
  have rd18 := wrapperBlocks.wrapper_block_1300_taken (by simp)
    (by simp only [ulit_toNat' 256 (by decide), ulit_toNat' 128 (by decide)]; rw [hload256, hload128, hone]; decide)
    (by apply D_J_contains_append_left; jump_dest) rd17
  simp only [wrapperBlocks.wrapper_block_1300_taken_stack, wrapperBlocks.wrapper_block_1300_taken_memory,
    ulit_toNat' 256 (by decide), ulit_toNat' 128 (by decide)] at rd18
  rw [hload256] at rd18
  have rd19 := wrapperBlocks.wrapper_block_1435 (by simp) hperm rd18
  set M9 := bw.toByteArray.write 0 (bw.toByteArray.write 0 M8 256 32) 128 32 with hM9
  have hM9size : M9.size = 288 := by
    rw [hM9, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM8'size] <;> omega)]; exact hM8'size
  have hread96 : M9.readWithPadding 96 32 = amt.toByteArray := by
    rw [hM9, write32_read_below _ _ 128 96 (by rw [toByteArray_size]) (by rw [hM8'size] <;> omega) (by decide),
      write32_read_below _ _ 256 96 (by rw [toByteArray_size]) (by rw [hM8size] <;> omega) (by decide), hM8,
      write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [ht3] <;> omega) (by decide),
      trMem_read96 _ _ _ _ hu5, uM6_read96]
  have hload96' : memLoad (UInt256.ofNat 96) M9 = amt :=
    memLoad_of_read _ 96 amt (by decide) (by rw [hM9size]; decide) hread96
  rw [ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide), ulit_toNat' 160 (by decide), hload96',
    write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [hM9size] <;> omega) (by decide), hread96] at rd19
  -- Stele: `ok = true`, the event and the return
  have hdec2 : config.externalABI.decode? "transfer" out2 = some [.bool true] := by
    rw [decode_transfer, decodeReturn_bool_one out2 h32' (by omega) (by rw [hbw]; exact hone)]; rfl
  set L5 : Store := L4.insert "ok" (.bool true) with hL5
  have hcall2S : ExecStmt fork config (frame imms L4) evm2
      (.externalCall (.var "__a2") "transfer" (.intLit 0) [.env .caller, .var "amount"] "ok" true)
      (.ok (frame imms L5) evm3) :=
    @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L4) evm2 (.var "__a2") a (.intLit 0)
      [.env .caller, .var "amount"] [.address I.source, uint256Value amt] "transfer" evm3 out2 true [.bool true] "ok"
      hrecv2 heth2 hargs2 hcall2 hdec2
  have hokT : evalExpr? config (frame imms L5) evm3 (.var "ok") = .ok (.bool true) :=
    evalVar imms _ _ "ok" _ (by rw [hL5]; exact store_get_self _ _ _)
  have hamt5 : evalExpr? config (frame imms L5) evm3 (.var "amount") = .ok (uint256Value amt) :=
    evalVar imms _ _ "amount" _ (by rw [hL5, store_get_ne _ _ (by decide), hL4, store_get_ne _ _ (by decide), hL3]; exact store_get_self _ _ _)
  have hemit : evalExprs? config (frame imms L5) evm3 [.env .caller, .var "amount"] = .ok [.address I.source, uint256Value amt] := by
    rw [evalExprs?, evalExpr_caller, hs3.env, evalExprs?, hamt5, evalExprs?]
    rfl
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (uStore I) unwrapTransition.body
      (.returned (frame imms L5) evm3 (some [uint256Value amt])) (restrictImmutables contract imms) :=
    ExecFuncBody.execBlockRet (hprefix _ (ExecBlock.consNormal hcall2S
      (ExecBlock.consNormal (ExecStmt.requireTrue hokT)
        (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [hs3.env] using hperm) hemit)
          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hamt5)))))))
  exact rd19.reEquivExecutionGen hcode' hd hdec hbody hs3.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperWrapper
