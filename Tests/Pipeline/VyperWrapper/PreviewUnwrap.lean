import Tests.Pipeline.VyperWrapper.CallHelpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `previewUnwrap(uint256)`

Dispatcher bucket 6, arm entry pc 1498: the guard, `if totalShares == 0: return 0` (pc 1508/1515),
`held = staticcall TOKEN.balanceOf(self)` (pc 1527, the `STATICCALL` at 1559, the bubble at 1564,
the `returndatasize` check at 1571), `sharesOut * held` with its overflow check (pc 1580), the
divisor check (pc 1610) and the division and `RETURN` (pc 1623/1637).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperCalls
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem previewUnwrapBody_eq : previewUnwrapTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .ite (.binary .eq (.storage tsRef) (.intLit 0)) [.return [.intLit 0]] [],
     .letDecl "__a0" (some (.elem .address)) (.immutable "TOKEN"),
     .externalCall (.var "__a0") "balanceOf" (.intLit 0) [.env .this] "held" false,
     .return [.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "sharesOut") (.var "held")))
       (.storage tsRef)]] := by rfl

abbrev pStore (I : ExecutionEnv) : Store := (∅ : Store).insert "sharesOut" (uint256Value (argWord I))

theorem pDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (previewUnwrapTransition.params.map Param.name)
      (transitionSignature previewUnwrapTransition).paramTypes I.calldata = some (pStore I) := by
  simpa [config, contract, Syntax.contractSyntax, previewUnwrapTransition, pStore, argWord_eq] using
    decodeMode_uint256_ok "sharesOut" I.calldata hsz36

theorem pDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (previewUnwrapTransition.params.map Param.name)
      (transitionSignature previewUnwrapTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, previewUnwrapTransition] using
    decodeMode_uint256_none_short "sharesOut" I.calldata hsz hshort

/-- `previewUnwrap(uint256)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem wrapperPreviewUnwrapBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 3)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 3) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := token_of_fit hfit
  obtain ⟨_, _, rd⟩ := wrapperReachPreviewUnwrapBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some previewUnwrapTransition :=
    wrapperDispatch_previewUnwrap (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := wrapperBlocks.wrapper_block_1498_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (pDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := wrapperBlocks.wrapper_block_1498_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [previewUnwrapBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := wrapperBlocks.wrapper_block_1498_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have hdec := pDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hts : evalExpr? config (frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.storage tsRef) (.intLit 0)) = .ok (.bool (decide ((solcSlotWordAt (UInt256.ofNat 2) σ I).toNat = 0))) := by
    rw [evalExpr_eq_zero_word (evalTsRead imms _ _ (by simp)), storageLoad_initState_ofUInt256_solcSlotWordAt]
  by_cases hts0 : solcSlotWordAt (UInt256.ofNat 2) σ I = ⟨0⟩
  · -- `totalShares == 0`: return 0
    obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_1508_fallthrough (by simp) (by rw [slotWord_eq, hts0]; rfl) rd1
    have rd3 := wrapperBlocks.wrapper_block_1515 (by simp) (by apply D_J_contains_append_left; jump_dest) rd2
    simp only [wrapperBlocks.wrapper_block_1515_stack, wrapperBlocks.wrapper_block_1515_memory,
      ulit_toNat' 64 (by decide)] at rd3
    have rd4 := wrapperBlocks.wrapper_block_1637 (by simp) rd3
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (wrapperDispatchMem 6) 64
        (by rw [dispatchMem_size 6 (by decide)]; exact lt_usize _ (by decide))] at rd4
    have h0 : evalExpr? config (frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) =
        .ok (uint256Value ⟨0⟩) := by
      have h := evalExpr_intLit_word (cfg := config) (stele := frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) 0 (by decide)
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by decide] at h
      exact h
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (pStore I)
        previewUnwrapTransition.body
        (.returned (frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [uint256Value ⟨0⟩]))
        (restrictImmutables contract imms) := by
      rw [previewUnwrapBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consReturn (ExecStmt.iteTrue (by rw [hts, hts0]; rfl)
          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton h0))))))
    exact rd4.reEquivExecution hcode' hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  have hiteF : evalExpr? config (frame imms (pStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.storage tsRef) (.intLit 0)) = .ok (.bool false) := by
    rw [hts, decide_eq_false (fun h => hts0 (u256_inj (by rw [h]; rfl)))]
  obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_1508_taken (by simp) (by rw [slotWord_eq]; exact fun h => hts0 h)
    (by apply D_J_contains_append_left; jump_dest) rd1
  have rd3 := wrapperBlocks.wrapper_block_1527 (immWords := wordsOf imms) (by simp) rd2
  simp only [wrapperBlocks.wrapper_block_1527_stack, wrapperBlocks.wrapper_block_1527_memory, wordsOf_TOKEN' hget,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 96 (by decide), ulit_toNat' 128 (by decide)] at rd3
  -- the `STATICCALL` at pc 1559
  have hM0 : 32 ≤ (wrapperDispatchMem 6).size ∧ (wrapperDispatchMem 6).size ≤ 96 := by
    rw [dispatchMem_size 6 (by decide)]; decide
  obtain ⟨hs0, hs1, hs2⟩ := balMem_sizes (addrWord a) I (wrapperDispatchMem 6) hM0
  obtain ⟨evm', σ', z, out, _, _, hcall, hs', rd4, hsize⟩ :=
    typedStaticCallBridge (cfg := config) (name := "balanceOf") (args := [.address I.codeOwner]) rd3 SourceState.init
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1559⟩ : UInt256), .STATICCALL, none))
      (by rw [encode_balanceOf, ulit_toNat' 124 (by decide), ulit_toNat' 36 (by decide), balMem_input _ _ _ hM0])
      (by rw [ulit_toNat' 36 (by decide)]; norm_num) (by simp)
  rw [ofUInt256_ofNat_eq_address] at hcall
  have rd5 := RD.normalizePC (pc' := UInt256.ofNat 1560) rd4 (by native_decide)
  set L1 : Store := (pStore I).insert "__a0" (.address a) with hL1
  have hrecv : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") = .ok (.address a) :=
    evalVar imms _ _ "__a0" _ (by rw [hL1]; exact store_get_self _ _ _)
  have heth : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) = .ok (.int 0) := by
    rw [evalExpr?]; rfl
  have hargs : evalExprs? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.env .this] =
      .ok [.address I.codeOwner] := by
    rw [evalExprs?, evalThis, evalExprs?]; rfl
  cases z with
  | false =>
    -- the call failed: the bubble revert
    have rd6 := wrapperBlocks.wrapper_block_1560_fallthrough (by simp) (by decide) rd5
    have rd7 := wrapperBlocks.wrapper_block_1564 (by simp [wrapperBlocks.wrapper_block_1560_fallthrough_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode' rd7 hd hdec ?_
    rw [previewUnwrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.iteFalse hiteF ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hrecv heth hargs hcall)))))
  | true =>
    have rd6 := wrapperBlocks.wrapper_block_1560_taken (by simp) (by decide)
      (by apply D_J_contains_append_left; jump_dest) rd5
    simp only [wrapperBlocks.wrapper_block_1560_taken_stack] at rd6
    have hout : out.size < UInt256.size := lt_size_of_lt_sign (by omega)
    by_cases hshortR : out.size < 32
    · -- short return data: the decode check reverts
      have rd7 := wrapperBlocks.wrapper_block_1571_taken (by simp)
        (by rw [ult_one (by rw [ulit_toNat' _ hout, ulit_toNat' 32 (by decide)]; exact hshortR)]; decide)
        (by apply D_J_contains_append_left; jump_dest) rd6
      have rd8 := wrapperBlocks.wrapper_block_1760 (by simp) rd7
      refine RDrev.reEquivExecutionRevert hcode' rd8 hd hdec ?_
      rw [previewUnwrapBody_eq]
      exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.iteFalse hiteF ExecBlock.nil)
          (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
            (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv heth hargs hcall
              (by rw [decode_balanceOf, decodeReturn_uint256_short out hshortR]; rfl))))))
    have h32 : 32 ≤ out.size := by omega
    have rd7 := wrapperBlocks.wrapper_block_1571_fallthrough (by simp)
      (by exact ult_zero (by rw [ulit_toNat' _ hout, ulit_toNat' 32 (by decide)]; omega)) rd6
    obtain ⟨hw, hhw⟩ : ∃ hw, retWord out = hw := ⟨_, rfl⟩
    rw [ulit_toNat' 96 (by decide), min32_toNat out.size h32 hout,
      write_out_eq_word out _ 96 h32 (by rw [hs2] <;> decide), hhw] at rd7
    set M1 := hw.toByteArray.write 0 (balMem (addrWord a) I (wrapperDispatchMem 6)) 96 32 with hM1
    have hM1size : M1.size = 160 := by
      rw [hM1, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hs2] <;> decide)]; exact hs2
    have hload96 : memLoad (UInt256.ofNat 96) M1 = hw :=
      memLoad_write_back _ _ 96 (by decide) (by rw [hs2]; exact lt_usize _ (by decide))
    have hload64 : memLoad (UInt256.ofNat 64) (hw.toByteArray.write 0 M1 64 32) = hw :=
      memLoad_write_back _ _ 64 (by decide) (by rw [hM1size]; exact lt_usize _ (by decide))
    have hM2size : (hw.toByteArray.write 0 M1 64 32).size = 160 := by
      rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM1size] <;> decide)]; exact hM1size
    -- Stele after the call
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
    -- pc 1580: `sharesOut * held`
    by_cases hfit : (argWord I).toNat * hw.toNat < UInt256.size
    swap
    · have rd8 := wrapperBlocks.wrapper_block_1580_taken (by simp)
        (by
          simp only [ulit_toNat' 64 (by decide)]
          rw [hload96, hload64]
          exact mulCheck_overflow _ _ (by show UInt256.size ≤ (argWord I).toNat * hw.toNat; omega))
        (by apply D_J_contains_append_left; jump_dest) rd7
      have rd9 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1580_taken_stack]) rd8
      refine RDrev.reEquivExecutionRevert hcode' rd9 hd hdec ?_
      rw [previewUnwrapBody_eq]
      exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.iteFalse hiteF ExecBlock.nil)
          (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
            (ExecBlock.consNormal hcallS
              (ExecBlock.consRevert (ExecStmt.returnRevert (by
                rw [evalExprs?, evalExpr_binary_revert_left (by decide) (by decide)
                  (evalExpr_uint256_mul_overflow (hso _) (hheld _) (by omega))]
                rfl)))))))
    have rd8 := wrapperBlocks.wrapper_block_1580_fallthrough (by simp)
      (by
        simp only [ulit_toNat' 64 (by decide)]
        rw [hload96, hload64]
        exact mulCheck_ok _ _ hfit) rd7
    simp only [wrapperBlocks.wrapper_block_1580_fallthrough_stack, wrapperBlocks.wrapper_block_1580_fallthrough_memory,
      ulit_toNat' 64 (by decide)] at rd8
    rw [hload96, hload64] at rd8
    have hmul := evalExpr_uint256_mul (hso evm') (hheld evm') hfit
    -- pc 1610: the divisor
    by_cases hts' : solcSlotWordAt (UInt256.ofNat 2) σ' I = ⟨0⟩
    · obtain ⟨_, _, rd9⟩ := wrapperBlocks.wrapper_block_1610_taken (by simp) (by rw [slotWord_eq, hts']; decide)
        (by apply D_J_contains_append_left; jump_dest) rd8
      have rd10 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1610_taken_stack]) rd9
      refine RDrev.reEquivExecutionRevert hcode' rd10 hd hdec ?_
      rw [previewUnwrapBody_eq]
      exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.iteFalse hiteF ExecBlock.nil)
          (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
            (ExecBlock.consNormal hcallS
              (ExecBlock.consRevert (ExecStmt.returnRevert (by
                rw [evalExprs?, evalExpr_div_zero hmul (by rw [htsPost, hts'])]
                rfl)))))))
    obtain ⟨_, _, rd9⟩ := wrapperBlocks.wrapper_block_1610_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_eq_zero_of_ne hts') rd8
    simp only [wrapperBlocks.wrapper_block_1610_fallthrough_stack] at rd9
    rw [slotWord_eq] at rd9
    have rd10 := wrapperBlocks.wrapper_block_1623 (by simp) rd9
    simp only [wrapperBlocks.wrapper_block_1623_stack, wrapperBlocks.wrapper_block_1623_memory,
      ulit_toNat' 96 (by decide)] at rd10
    have rd11 := wrapperBlocks.wrapper_block_1637 (by simp) rd10
    rw [ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ _ 96 (by rw [hM2size]; exact lt_usize _ (by decide))] at rd11
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (pStore I)
        previewUnwrapTransition.body
        (.returned (frame imms L2) evm'
          (some [uint256Value (UInt256.div (UInt256.mul (argWord I) hw) (solcSlotWordAt (UInt256.ofNat 2) σ' I))]))
        (restrictImmutables contract imms) := by
      rw [previewUnwrapBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.iteFalse hiteF ExecBlock.nil)
          (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
            (ExecBlock.consNormal hcallS
              (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
                (evalExpr_uint256_div hmul htsPost hts'))))))))
    exact rd11.reEquivExecutionGen hcode' hd hdec hbody hs'.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperWrapper
