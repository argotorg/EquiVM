import Tests.Pipeline.VyperWrapper.Unwrap

variable {fork : Ethereum.Fork}

/-!
# Wrapper `wrap(uint256)`

Dispatcher bucket 0, arm entry pc 225: the guard, `require(amount > 0)` (pc 235, revert 242),
`ok = extcall TOKEN.transferFrom(msg.sender, self, amount)` (pc 354, the `CALL` at 397, bubble
402, the decode checks 409/432), `require(ok)` (pc 443, revert 462), `minted = amount` and
`held = staticcall TOKEN.balanceOf(self)` (pc 574, the `STATICCALL` at 612, bubble 617,
`returndatasize` 624), the short-circuit `totalShares > 0 and held > amount` (pc 633/649/660/662),
`minted = amount * totalShares // (held - amount)` with its checks (pc 668/690/710/720), then the
shared tail `wrapTail` from pc 730: `shares[msg.sender] += minted`, `totalShares += minted`
(pc 730/758/781), the optional hook call (pc 795/822, the `CALL` at 832, bubble 837) and the
`RETURN` (pc 846).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperCalls
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

abbrev wrapTailStmts : List Stmt :=
  [.assign .storage shRef (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage shRef) (.var "minted"))),
   .assign .storage tsRef (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage tsRef) (.var "minted"))),
   .ite (.binary .ne (.storage hookRef) (.cast (.intLit 0) (.elem .address)))
     [.require (.binary .gt (.extCodeSize (.storage hookRef)) (.intLit 0)),
      .externalCall (.storage hookRef) "onWrap" (.intLit 0) [.env .caller, .var "minted"] "__c4" true] [],
   .emit "Wrapped" [.env .caller, .var "minted"],
   .return [.var "minted"]]

theorem wrapBody_eq : wrapTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .gt (.var "amount") (.intLit 0)),
     .letDecl "__a0" (some (.elem .address)) (.immutable "TOKEN"),
     .externalCall (.var "__a0") "transferFrom" (.intLit 0) [.env .caller, .env .this, .var "amount"] "ok" true,
     .require (.var "ok"),
     .letDecl "minted" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.var "amount"),
     .letDecl "__a2" (some (.elem .address)) (.immutable "TOKEN"),
     .externalCall (.var "__a2") "balanceOf" (.intLit 0) [.env .this] "held" false,
     .ite (.binary .and (.binary .gt (.storage tsRef) (.intLit 0)) (.binary .gt (.var "held") (.var "amount")))
       [.assign .localVar { base := "minted", steps := [] }
         (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "amount") (.storage tsRef)))
           (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "held") (.var "amount"))))] [],
     .assign .storage shRef (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage shRef) (.var "minted"))),
     .assign .storage tsRef (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage tsRef) (.var "minted"))),
     .ite (.binary .ne (.storage hookRef) (.cast (.intLit 0) (.elem .address)))
       [.require (.binary .gt (.extCodeSize (.storage hookRef)) (.intLit 0)),
        .externalCall (.storage hookRef) "onWrap" (.intLit 0) [.env .caller, .var "minted"] "__c4" true] [],
     .emit "Wrapped" [.env .caller, .var "minted"],
     .return [.var "minted"]] := by rfl

abbrev wStore (I : ExecutionEnv) : Store := (∅ : Store).insert "amount" (uint256Value (argWord I))

theorem wDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (wrapTransition.params.map Param.name)
      (transitionSignature wrapTransition).paramTypes I.calldata = some (wStore I) := by
  simpa [config, contract, Syntax.contractSyntax, wrapTransition, wStore, argWord_eq] using
    decodeMode_uint256_ok "amount" I.calldata hsz36

theorem wDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (wrapTransition.params.map Param.name)
      (transitionSignature wrapTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, wrapTransition] using
    decodeMode_uint256_none_short "amount" I.calldata hsz hshort

abbrev selO : UInt256 := UInt256.ofNat 2721273594

/-- The tail from pc 730: the two stores, the optional hook call, the event and the return.
`M` is the memory at pc 730 with `minted` at offset 96; `L` the locals holding `minted`. -/
theorem wrapTail {σ σ₀ A I} {g : UInt256} (imms : Store) (hwf : storageWF σ I)
    (hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms))
    (hd : dispatchMsg contract I.calldata = some wrapTransition)
    (hdec : config.externalABI.decodeCalldata? (wrapTransition.params.map Param.name)
      (transitionSignature wrapTransition).paramTypes I.calldata = some (wStore I))
    (σ2 : AccountMap) (evm2 : EVM.State) (hs2 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ2 evm2)
    (hcanon2 : (solcSlotWordAt ⟨0⟩ σ2 I).toNat < EVM.addressModulus)
    (minted : UInt256) (M : ByteArray) (hM : M.size = 256) (hMr : M.readWithPadding 96 32 = minted.toByteArray)
    {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (rd : RD fork (wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms)) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 730) [solcSelectorWord I] M aw rdata σ2 k C)
    (L : Store) (hLm : L.get? "minted" = some (uint256Value minted)) (hLsh : L.get? "shares" = none)
    (hLts : L.get? "totalShares" = none) (hLhook : L.get? "hook" = none)
    (hprefix : ∀ result, ExecBlock fork config (frame imms L) evm2 wrapTailStmts result →
      ExecBlock fork config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) wrapTransition.body result) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hW9 : (hashMem M I).size = 256 := by rw [hashMem_size_ge _ _ (by rw [hM]; decide)]; exact hM
  have hkec := keccak_hashMem_ge M I (by rw [hM]; decide)
  have hW9r : (hashMem M I).readWithPadding 96 32 = minted.toByteArray := by
    rw [hashMem_read_above _ _ 96 (by decide) (by rw [hM] <;> decide), hMr]
  have hload96 : memLoad (UInt256.ofNat 96) (hashMem M I) = minted :=
    memLoad_of_read _ 96 minted (by decide) (by rw [hW9]; decide) hW9r
  have hmv : ∀ evm, evalExpr? config (frame imms L) evm (.var "minted") = .ok (uint256Value minted) := fun evm =>
    evalVar imms _ _ "minted" _ hLm
  have hsh2 : evalExpr? config (frame imms L) evm2 (.storage shRef) =
      .ok (uint256Value (solcSlotWordAt (sharesSlot I.source) σ2 I)) := by
    rw [evalSharesCallerRead imms _ _ hLsh, hs2.storageRead, hs2.env]; rfl
  obtain ⟨sh2, hsh2eq⟩ : ∃ x, solcSlotWordAt (sharesSlot I.source) σ2 I = x := ⟨_, rfl⟩
  rw [hsh2eq] at hsh2
  -- pc 730: `shares[msg.sender] + minted`
  by_cases hfit1 : sh2.toNat + minted.toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd1⟩ := wrapperBlocks.wrapper_block_730_taken (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hkec, slotWord_eq, hload96, hsh2eq, u256_add_overflow_lt sh2 minted (by omega)]
        decide) (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_730_taken_stack]) rd1
    exact RDrev.reEquivExecutionRevert hcode' rd2 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consRevert (ExecStmt.assignExprRevert (evalExpr_uint256_add_overflow hsh2 (hmv _) (by omega))))))
  obtain ⟨_, _, rd1⟩ := wrapperBlocks.wrapper_block_730_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec, slotWord_eq, hload96, hsh2eq]
      exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hfit1]; omega)) rd
  simp only [wrapperBlocks.wrapper_block_730_fallthrough_stack, wrapperBlocks.wrapper_block_730_fallthrough_memory,
    ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd1
  rw [hkec, slotWord_eq, hload96, hsh2eq] at rd1
  have hadd1 := evalExpr_uint256_add hsh2 (hmv _) hfit1
  have hassign1 : assignStorageRef? config (frame imms L) evm2 .storage shRef (uint256Value (sh2 + minted)) =
      .ok (frame imms L, Stele.EVM.storageStore evm2 I.codeOwner (sharesSlot I.source) (sh2 + minted)) := by
    rw [assignSharesCaller imms _ _ _ hLsh, hs2.env]
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the `shares` store (pc 763) halts
    have hpf : I.perm = false := by simpa using hperm
    have r1 := rd1.swap1
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨758⟩ : UInt256), .SWAP1, none)) (by evm_ov)
    have r2 := r1.pop
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨759⟩ : UInt256), .POP, none)) (by evm_ov)
    have r3 := r2.swap1
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨760⟩ : UInt256), .SWAP1, none)) (by evm_ov)
    have r4 := r3.pop
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨761⟩ : UInt256), .POP, none)) (by evm_ov)
    have r5 := r4.dup2
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨762⟩ : UInt256), .DUP2, none)) (by evm_ov)
    have rs := r5.sstoreStatic hpf
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨763⟩ : UInt256), .SSTORE, none)) (by evm_ov)
    exact RDstatic.reEquivStaticHalt hcode' rs hd hdec (ExecFuncBody.execBlockStatic (hprefix _
      (ExecBlock.consStatic (ExecStmt.assignStatic hadd1 hassign1 (by rw [hs2.env]; exact hpf)))))
  set evm3 := Stele.EVM.storageStore evm2 I.codeOwner (sharesSlot I.source) (sh2 + minted) with hevm3
  have hs3 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
      (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted)) evm3 := hs2.storageWrite _ _
  have hts3 : evalExpr? config (frame imms L) evm3 (.storage tsRef) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted)) I)) := by
    rw [evalTsRead imms _ _ hLts, hs3.storageRead]; rfl
  obtain ⟨ts3, hts3eq⟩ : ∃ x, solcSlotWordAt (UInt256.ofNat 2) (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted)) I = x := ⟨_, rfl⟩
  rw [hts3eq] at hts3
  -- pc 758: the `shares` store, `totalShares + minted`
  by_cases hfit2 : ts3.toNat + minted.toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_758_taken (by simp) hperm
      (by rw [slotWord_eq, hload96, hts3eq, u256_add_overflow_lt ts3 minted (by omega)]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_758_taken_stack]) rd2
    exact RDrev.reEquivExecutionRevert hcode' rd3 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) hadd1 hassign1)
        (ExecBlock.consRevert (ExecStmt.assignExprRevert (evalExpr_uint256_add_overflow hts3 (hmv _) (by omega)))))))
  obtain ⟨_, _, rd2⟩ := wrapperBlocks.wrapper_block_758_fallthrough (by simp) hperm
    (by
      rw [slotWord_eq, hload96, hts3eq]
      exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hfit2]; omega)) rd1
  simp only [wrapperBlocks.wrapper_block_758_fallthrough_stack] at rd2
  rw [slotWord_eq, hload96, hts3eq] at rd2
  have hadd2 := evalExpr_uint256_add hts3 (hmv _) hfit2
  have hassign2 : assignStorageRef? config (frame imms L) evm3 .storage tsRef (uint256Value (ts3 + minted)) =
      .ok (frame imms L, Stele.EVM.storageStore evm3 I.codeOwner (UInt256.ofNat 2) (ts3 + minted)) := by
    rw [assignTs imms _ _ _ hLts, hs3.env]
  set evm4 := Stele.EVM.storageStore evm3 I.codeOwner (UInt256.ofNat 2) (ts3 + minted) with hevm4
  have hs4 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted))
        (UInt256.ofNat 2) (ts3 + minted)) evm4 := hs3.storageWrite _ _
  -- pc 781: the `totalShares` store, then `hook != empty(address)`
  have hhook4 : solcSlotWordAt ⟨0⟩ (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted))
      (UInt256.ofNat 2) (ts3 + minted)) I = solcSlotWordAt ⟨0⟩ σ2 I := by
    rw [solcSlotWordAt_sstore_ne _ _ _ _ _ (by decide), solcSlotWordAt_sstore_ne _ _ _ _ _ (Ne.symm hwf.2.1)]
  obtain ⟨hk, hhk⟩ : ∃ x, solcSlotWordAt ⟨0⟩ (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted))
      (UInt256.ofNat 2) (ts3 + minted)) I = x := ⟨_, rfl⟩
  have hcanon4 : hk.toNat < EVM.addressModulus := by rw [← hhk, hhook4]; exact hcanon2
  have hk_read : Stele.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨0⟩ = hk := by
    rw [hs4.storageRead]; exact hhk
  have hhookRead : evalExpr? config (frame imms L) evm4 (.storage hookRef) = .ok (.address (AccountAddress.ofNat hk.toNat)) := by
    rw [evalHookRead imms _ _ hLhook, hk_read]
  have hne : evalExpr? config (frame imms L) evm4 (.binary .ne (.storage hookRef) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (!decide (hk = ⟨0⟩))) := by
    rw [evalHookNeZero imms _ _ hLhook (by rw [hk_read]; exact hcanon4), hk_read]
  by_cases hk0 : hk = ⟨0⟩
  · -- no hook: the event and the return
    obtain ⟨_, _, rd3⟩ := wrapperBlocks.wrapper_block_781_taken (by simp) hperm
      (by rw [slotWord_eq, hhk, hk0]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd2
    have rd4 := wrapperBlocks.wrapper_block_846 (by simp [wrapperBlocks.wrapper_block_781_taken_stack]) hperm rd3
    rw [ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide), ulit_toNat' 160 (by decide), hload96,
      write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [hW9] <;> omega) (by decide), hW9r] at rd4
    have hemit : evalExprs? config (frame imms L) evm4 [.env .caller, .var "minted"] = .ok [.address I.source, uint256Value minted] := by
      rw [evalExprs?, evalExpr_caller, hs4.env, evalExprs?, hmv, evalExprs?]; rfl
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (wStore I) wrapTransition.body
        (.returned (frame imms L) evm4 (some [uint256Value minted])) (restrictImmutables contract imms) :=
      ExecFuncBody.execBlockRet (hprefix _ (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) hadd1 hassign1)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs3.env] using hperm)) hadd2 hassign2)
          (ExecBlock.consNormal (ExecStmt.iteFalse (by rw [hne, hk0]; decide) ExecBlock.nil)
            (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [hs4.env] using hperm) hemit)
              (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (hmv _)))))))))
    exact rd4.reEquivExecutionGen hcode' hd hdec hbody hs4.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))
  -- the hook is set: `require(hook.code.length > 0)`
  obtain ⟨_, _, rd3⟩ := wrapperBlocks.wrapper_block_781_fallthrough (by simp) hperm
    (by rw [slotWord_eq, hhk]; exact isZero_eq_zero_of_ne hk0) rd2
  simp only [wrapperBlocks.wrapper_block_781_fallthrough_stack] at rd3
  have hneT : evalExpr? config (frame imms L) evm4 (.binary .ne (.storage hookRef) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool true) := by
    rw [hne, decide_eq_false hk0]; rfl
  have hcs : evalExpr? config (frame imms L) evm4 (.extCodeSize (.storage hookRef)) =
      .ok (.int (Int.ofNat (extCodeSizeWord _ hk).toNat)) :=
    extCodeSource hs4.accounts (by rw [hhookRead, accountAddress_ofUInt256_eq_ofNat_toNat])
  have hgtcs := evalExpr_gt_zero (a := extCodeSizeWord _ hk) hcs
  by_cases hcode0 : extCodeSizeWord (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ2 (sharesSlot I.source) (sh2 + minted))
      (UInt256.ofNat 2) (ts3 + minted)) hk = ⟨0⟩
  · obtain ⟨_, _, rd4⟩ := wrapperBlocks.wrapper_block_795_taken (by simp)
      (by rw [slotWord_eq, hhk, hcode0]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd3
    have rd5 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_795_taken_stack]) rd4
    exact RDrev.reEquivExecutionRevert hcode' rd5 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) hadd1 hassign1)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs3.env] using hperm)) hadd2 hassign2)
          (ExecBlock.consRevert (ExecStmt.iteTrue hneT (ExecBlock.consRevert (ExecStmt.requireFalse
            (by rw [hgtcs, hcode0]; rfl)))))))))
  obtain ⟨_, _, rd4⟩ := wrapperBlocks.wrapper_block_795_fallthrough (by simp)
    (by rw [slotWord_eq, hhk]; exact isZero_eq_zero_of_ne hcode0) rd3
  simp only [wrapperBlocks.wrapper_block_795_fallthrough_stack, wrapperBlocks.wrapper_block_795_fallthrough_memory,
    ulit_toNat' 160 (by decide), ulit_toNat' 192 (by decide), ulit_toNat' 224 (by decide)] at rd4
  rw [slotWord_eq, hhk] at rd4
  have hpre96 : memLoad (UInt256.ofNat 96) ((callerWord I).toByteArray.write 0 (selO.toByteArray.write 0 (hashMem M I) 160 32) 192 32) = minted :=
    memLoad_of_read _ 96 minted (by decide) (by rw [(callMem2_sizes selO I minted _ hW9).2.1]; decide)
      (by rw [callMem2_pre_read96 _ _ _ hW9, hW9r])
  rw [hpre96] at rd4
  have rd5 := wrapperBlocks.wrapper_block_822 (by simp) rd4
  simp only [wrapperBlocks.wrapper_block_822_stack] at rd5
  have hgtcsT : evalExpr? config (frame imms L) evm4 (.binary .gt (.extCodeSize (.storage hookRef)) (.intLit 0)) =
      .ok (.bool true) := by
    rw [hgtcs, decide_eq_true (Nat.pos_of_ne_zero (fun h => hcode0 (u256_inj (by rw [h]; rfl))))]
  -- the `CALL` at 832
  obtain ⟨hc1, hc2, hc3⟩ := callMem2_sizes selO I minted (hashMem M I) hW9
  obtain ⟨evm5, σ5, z, out, _, _, hcall, hs5, rd6, hsize, -⟩ :=
    typedCallBridge (cfg := config) (name := "onWrap") (args := [.address I.source, uint256Value minted]) rd5 hs4
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨832⟩ : UInt256), .CALL, none))
      (by rw [encode_onWrap, ulit_toNat' 188 (by decide), ulit_toNat' 68 (by decide),
        callMem2_input selO I minted _ hW9 (selectorBytes 0xa2 0x33 0x56 0xfa) (by native_decide)])
      (by rw [ulit_toNat' 68 (by decide)]; norm_num) (by simp)
  have hw' : AccountAddress.ofUInt256 hk = EVM.address (AccountAddress.ofNat hk.toNat).val := by
    conv_lhs => rw [← word_roundtrip hcanon4]
    exact ofUInt256_ofNat_eq_address _
  rw [hw'] at hcall
  have rd7 := RD.normalizePC (pc' := UInt256.ofNat 833) rd6 (by native_decide)
  rw [write_out_zero] at rd7
  have heth5 : evalExpr? config (frame imms L) evm4 (.intLit 0) = .ok (.int 0) := by rw [evalExpr?]; rfl
  have hargs5 : evalExprs? config (frame imms L) evm4 [.env .caller, .var "minted"] = .ok [.address I.source, uint256Value minted] := by
    rw [evalExprs?, evalExpr_caller, hs4.env, evalExprs?, hmv, evalExprs?]; rfl
  cases z with
  | false =>
    have rd8 := wrapperBlocks.wrapper_block_833_fallthrough (by simp) (by decide) rd7
    have rd9 := wrapperBlocks.wrapper_block_837 (by simp [wrapperBlocks.wrapper_block_833_fallthrough_stack]) rd8
    exact RDrev.reEquivExecutionRevert hcode' rd9 hd hdec (ExecFuncBody.execBlockRevert (hprefix _
      (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) hadd1 hassign1)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs3.env] using hperm)) hadd2 hassign2)
          (ExecBlock.consRevert (ExecStmt.iteTrue hneT (ExecBlock.consNormal (ExecStmt.requireTrue hgtcsT)
            (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hhookRead heth5 hargs5 hcall)))))))))
  | true =>
  have rd8 := wrapperBlocks.wrapper_block_833_taken (by simp) (by decide)
    (by apply D_J_contains_append_left; jump_dest) rd7
  simp only [wrapperBlocks.wrapper_block_833_taken_stack] at rd8
  have rd9 := wrapperBlocks.wrapper_block_844 (by simp) rd8
  simp only [wrapperBlocks.wrapper_block_844_stack] at rd9
  have rd10 := wrapperBlocks.wrapper_block_846 (by simp) hperm rd9
  have hpost96r : (callMem2 selO I minted (hashMem M I)).readWithPadding 96 32 = minted.toByteArray := by
    rw [callMem2_read96 _ _ _ _ hW9, hW9r]
  have hpost96 : memLoad (UInt256.ofNat 96) (callMem2 selO I minted (hashMem M I)) = minted :=
    memLoad_of_read _ 96 minted (by decide) (by rw [hc3]; decide) hpost96r
  rw [ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide), ulit_toNat' 160 (by decide), hpost96,
    write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [hc3] <;> omega) (by decide), hpost96r] at rd10
  set L6 : Store := L.insert "__c4" .unit with hL6
  have hcallS : ExecStmt fork config (frame imms L) evm4
      (.externalCall (.storage hookRef) "onWrap" (.intLit 0) [.env .caller, .var "minted"] "__c4" true)
      (.ok (frame imms L6) evm5) :=
    @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L) evm4 (.storage hookRef) (AccountAddress.ofNat hk.toNat) (.intLit 0)
      [.env .caller, .var "minted"] [.address I.source, uint256Value minted] "onWrap" evm5 out true [] "__c4"
      hhookRead heth5 hargs5 hcall (decode_onWrap out)
  have hmv6 : evalExpr? config (frame imms L6) evm5 (.var "minted") = .ok (uint256Value minted) :=
    evalVar imms _ _ "minted" _ (by rw [hL6, store_get_ne _ _ (by decide)]; exact hLm)
  have hemit6 : evalExprs? config (frame imms L6) evm5 [.env .caller, .var "minted"] = .ok [.address I.source, uint256Value minted] := by
    rw [evalExprs?, evalExpr_caller, hs5.env, evalExprs?, hmv6, evalExprs?]; rfl
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (wStore I) wrapTransition.body
      (.returned (frame imms L6) evm5 (some [uint256Value minted])) (restrictImmutables contract imms) :=
    ExecFuncBody.execBlockRet (hprefix _ (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) hadd1 hassign1)
      (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs3.env] using hperm)) hadd2 hassign2)
        (ExecBlock.consNormal (ExecStmt.iteTrue hneT (ExecBlock.consNormal (ExecStmt.requireTrue hgtcsT)
          (ExecBlock.consNormal hcallS ExecBlock.nil)))
          (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [hs5.env] using hperm) hemit6)
            (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hmv6))))))))
  exact rd10.reEquivExecutionGen hcode' hd hdec hbody hs5.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))

/-- `wrap(uint256)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem wrapperWrapBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 6) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := token_of_fit hfit
  obtain ⟨_, _, rd⟩ := wrapperReachWrapBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some wrapTransition :=
    wrapperDispatch_wrap (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := wrapperBlocks.wrapper_block_225_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (wDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := wrapperBlocks.wrapper_block_225_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [wrapBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := wrapperBlocks.wrapper_block_225_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have hdec := wDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hamt0 : ∀ evm, evalExpr? config (frame imms (wStore I)) evm (.var "amount") = .ok (uint256Value (argWord I)) :=
    fun evm => evalVar imms _ _ "amount" _ (store_get_self _ _ _)
  have hgt := evalExpr_gt_zero (hamt0 (initState σ σ₀ (Sat256.ofUInt256 g) A I))
  -- pc 235: `amount > 0`
  by_cases hz : argWord I = ⟨0⟩
  · have rd2 := wrapperBlocks.wrapper_block_235_fallthrough (by simp) (by show argWord I = _; rw [hz]; rfl) rd1
    have rd3 := wrapperBlocks.wrapper_block_242 (by simp) rd2
    refine RDrev.reEquivExecutionRevert hcode' rd3 hd hdec ?_
    rw [wrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.requireFalse (by rw [hgt, hz]; rfl))))
  have hposN : 0 < (argWord I).toNat := by
    rcases Nat.eq_zero_or_pos (argWord I).toNat with h | h
    · exact absurd (u256_inj (b := (⟨0⟩ : UInt256)) h) hz
    · exact h
  have hgtT : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.var "amount") (.intLit 0)) = .ok (.bool true) := by
    rw [hgt, decide_eq_true hposN]
  have rd2 := wrapperBlocks.wrapper_block_235_taken (by simp) (by show argWord I ≠ _; exact fun h => hz h)
    (by apply D_J_contains_append_left; jump_dest) rd1
  -- pc 354: the `transferFrom` call at 397
  have rd3 := wrapperBlocks.wrapper_block_354 (immWords := wordsOf imms) (by simp) rd2
  simp only [wrapperBlocks.wrapper_block_354_stack, wrapperBlocks.wrapper_block_354_memory, wordsOf_TOKEN' hget,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 96 (by decide), ulit_toNat' 128 (by decide),
    ulit_toNat' 160 (by decide), ulit_toNat' 192 (by decide)] at rd3
  obtain ⟨hf0, hf1, hf2, hf3, hf4⟩ := tfMem_sizes (addrWord a) I (argWord I) (wrapperDispatchMem 0) (dispatchMem_size 0 (by decide))
  obtain ⟨evm1, σ1, z1, out1, _, _, hcall1, hs1, rd4, hsize1, hΘ1⟩ :=
    typedCallBridge (cfg := config) (name := "transferFrom")
      (args := [.address I.source, .address I.codeOwner, uint256Value (argWord I)]) rd3 SourceState.init
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨397⟩ : UInt256), .CALL, none))
      (by rw [encode_transferFrom, ulit_toNat' 124 (by decide), ulit_toNat' 100 (by decide),
        tfMem_input _ _ _ _ (dispatchMem_size 0 (by decide))])
      (by rw [ulit_toNat' 100 (by decide)]; norm_num) (by simp)
  have hcanon1 : (solcSlotWordAt ⟨0⟩ σ1 I).toNat < EVM.addressModulus := by
    rcases hΘ1 with h | ⟨A_in, callGas, g', A', hΘ⟩
    · rw [h]; exact hwf.1
    · exact hwf.2.2 fork _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
  rw [ofUInt256_ofNat_eq_address] at hcall1
  have rd5 := RD.normalizePC (pc' := UInt256.ofNat 398) rd4 (by native_decide)
  set L1 : Store := (wStore I).insert "__a0" (.address a) with hL1
  have hrecv1 : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") = .ok (.address a) :=
    evalVar imms _ _ "__a0" _ (by rw [hL1]; exact store_get_self _ _ _)
  have heth1 : evalExpr? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) = .ok (.int 0) := by
    rw [evalExpr?]; rfl
  have hargs1 : evalExprs? config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      [.env .caller, .env .this, .var "amount"] = .ok [.address I.source, .address I.codeOwner, uint256Value (argWord I)] := by
    rw [evalExprs?, evalExpr_caller, evalExprs?, evalThis, evalExprs?,
      evalVar imms _ _ "amount" _ (by rw [hL1, store_get_ne _ _ (by decide)]; exact store_get_self _ _ _), evalExprs?]
    rfl
  cases z1 with
  | false =>
    have rd6 := wrapperBlocks.wrapper_block_398_fallthrough (by simp) (by decide) rd5
    have rd7 := wrapperBlocks.wrapper_block_402 (by simp [wrapperBlocks.wrapper_block_398_fallthrough_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode' rd7 hd hdec ?_
    rw [wrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hrecv1 heth1 hargs1 hcall1)))))
  | true =>
  have rd6 := wrapperBlocks.wrapper_block_398_taken (by simp) (by decide)
    (by apply D_J_contains_append_left; jump_dest) rd5
  simp only [wrapperBlocks.wrapper_block_398_taken_stack] at rd6
  have hout1 : out1.size < UInt256.size := lt_size_of_lt_sign (by omega)
  have h128 : 96 + 32 < UInt256.size := lt_size_of_lt_sign (by norm_num)
  by_cases hshort1 : out1.size < 32
  · have rd7 := wrapperBlocks.wrapper_block_409_taken (by simp) (rdsCheck_short 96 128 out1.size rfl h128 hshort1)
      (by apply D_J_contains_append_left; jump_dest) rd6
    have rd8 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_409_taken_stack]) rd7
    refine RDrev.reEquivExecutionRevert hcode' rd8 hd hdec ?_
    rw [wrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv1 heth1 hargs1 hcall1
            (by rw [decode_transferFrom, decodeReturn_bool_short out1 hshort1]; rfl))))))
  have h32 : 32 ≤ out1.size := by omega
  have rd7 := wrapperBlocks.wrapper_block_409_fallthrough (by simp) (rdsCheck_ok 96 128 out1.size rfl h128 h32 hout1) rd6
  simp only [wrapperBlocks.wrapper_block_409_fallthrough_stack] at rd7
  obtain ⟨bw, hbw⟩ : ∃ bw, retWord out1 = bw := ⟨_, rfl⟩
  rw [ulit_toNat' 96 (by decide), min32_toNat out1.size h32 hout1,
    write_out_eq_word out1 _ 96 h32 (by rw [hf4] <;> omega), hbw] at rd7
  have hW2 : (bw.toByteArray.write 0 (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32).size = 224 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hf4] <;> omega)]; exact hf4
  have hload96 : memLoad (UInt256.ofNat 96) (bw.toByteArray.write 0 (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32) = bw :=
    memLoad_write_back _ _ 96 (by decide) (by rw [hf4]; exact lt_usize _ (by decide))
  -- pc 432: the bool validation
  by_cases hbool : bw.toNat < 2
  swap
  · have rd8 := wrapperBlocks.wrapper_block_432_taken (by simp)
      (by rw [hload96]; intro h; exact hbool (u256_lt_two_of_shiftRight1_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd7
    have rd9 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_432_taken_stack]) rd8
    refine RDrev.reEquivExecutionRevert hcode' rd9 hd hdec ?_
    rw [wrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv1 heth1 hargs1 hcall1
            (by
              rw [decode_transferFrom, decodeReturn_bool_noncanon out1 h32 (by omega)
                (by rw [hbw]; intro h; apply hbool; rw [h]; decide) (by rw [hbw]; intro h; apply hbool; rw [h]; decide)]
              rfl))))))
  have rd8 := wrapperBlocks.wrapper_block_432_fallthrough (by simp)
    (by rw [hload96]; exact u256_shiftRight1_zero_of_lt _ hbool) rd7
  simp only [wrapperBlocks.wrapper_block_432_fallthrough_stack] at rd8
  rw [hload96] at rd8
  -- pc 443: `require(ok)`
  have hW3 : (bw.toByteArray.write 0 (bw.toByteArray.write 0 (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32) 224 32).size = 256 :=
    toByteArray_write32_size_of_ge _ _ 224 224 256 hW2 (by omega) (lt_usize _ (by decide)) rfl
  have hload224 : memLoad (UInt256.ofNat 224) (bw.toByteArray.write 0 (bw.toByteArray.write 0 (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32) 224 32) = bw :=
    memLoad_write_back _ _ 224 (by decide) (by rw [hW2]; exact lt_usize _ (by decide))
  have hload64 : memLoad (UInt256.ofNat 64) (bw.toByteArray.write 0 (bw.toByteArray.write 0 (bw.toByteArray.write 0
      (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32) 224 32) 64 32) = bw :=
    memLoad_write_back _ _ 64 (by decide) (by rw [hW3]; exact lt_usize _ (by decide))
  by_cases hok : bw = ⟨0⟩
  · have rd9 := wrapperBlocks.wrapper_block_443_fallthrough (by simp)
      (by simp only [ulit_toNat' 224 (by decide), ulit_toNat' 64 (by decide)]; rw [hload224, hload64, hok]; rfl) rd8
    have rd10 := wrapperBlocks.wrapper_block_462 (by simp [wrapperBlocks.wrapper_block_443_fallthrough_stack]) rd9
    have hdec1 : config.externalABI.decode? "transferFrom" out1 = some [.bool false] := by
      rw [decode_transferFrom, decodeReturn_bool_zero out1 h32 (by omega) (by rw [hbw]; exact hok)]; rfl
    have hcall1S : ExecStmt fork config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (.externalCall (.var "__a0") "transferFrom" (.intLit 0) [.env .caller, .env .this, .var "amount"] "ok" true)
        (.ok (frame imms (L1.insert "ok" (.bool false))) evm1) :=
      @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") a
        (.intLit 0) [.env .caller, .env .this, .var "amount"] [.address I.source, .address I.codeOwner, uint256Value (argWord I)]
        "transferFrom" evm1 out1 true [.bool false] "ok" hrecv1 heth1 hargs1 hcall1 hdec1
    refine RDrev.reEquivExecutionRevert hcode' rd10 hd hdec ?_
    rw [wrapBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcall1S
            (ExecBlock.consRevert (ExecStmt.requireFalse (evalVar imms _ _ "ok" _ (store_get_self _ _ _))))))))
  have hone : bw = ⟨1⟩ := by
    have h0 : bw.toNat ≠ 0 := fun h => hok (u256_inj (by rw [h]; rfl))
    exact u256_inj (by show bw.toNat = 1; omega)
  have rd9 := wrapperBlocks.wrapper_block_443_taken (by simp)
    (by simp only [ulit_toNat' 224 (by decide), ulit_toNat' 64 (by decide)]; rw [hload224, hload64, hone]; decide)
    (by apply D_J_contains_append_left; jump_dest) rd8
  simp only [wrapperBlocks.wrapper_block_443_taken_stack, wrapperBlocks.wrapper_block_443_taken_memory,
    ulit_toNat' 224 (by decide), ulit_toNat' 64 (by decide)] at rd9
  rw [hload224] at rd9
  set W4 := bw.toByteArray.write 0 (bw.toByteArray.write 0 (bw.toByteArray.write 0
    (tfMem (addrWord a) I (argWord I) (wrapperDispatchMem 0)) 96 32) 224 32) 64 32 with hW4def
  have hW4 : W4.size = 256 := by
    rw [hW4def, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hW3] <;> omega)]; exact hW3
  -- Stele up to the second call
  have hdec1 : config.externalABI.decode? "transferFrom" out1 = some [.bool true] := by
    rw [decode_transferFrom, decodeReturn_bool_one out1 h32 (by omega) (by rw [hbw]; exact hone)]; rfl
  set L2 : Store := L1.insert "ok" (.bool true) with hL2
  have hcall1S : ExecStmt fork config (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.externalCall (.var "__a0") "transferFrom" (.intLit 0) [.env .caller, .env .this, .var "amount"] "ok" true)
      (.ok (frame imms L2) evm1) :=
    @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "__a0") a
      (.intLit 0) [.env .caller, .env .this, .var "amount"] [.address I.source, .address I.codeOwner, uint256Value (argWord I)]
      "transferFrom" evm1 out1 true [.bool true] "ok" hrecv1 heth1 hargs1 hcall1 hdec1
  have hokT : evalExpr? config (frame imms L2) evm1 (.var "ok") = .ok (.bool true) :=
    evalVar imms _ _ "ok" _ (by rw [hL2]; exact store_get_self _ _ _)
  have hamtM : evalExpr? config (frame imms L2) evm1 (.var "amount") = .ok (uint256Value (argWord I)) :=
    evalVar imms _ _ "amount" _ (by rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide)]; exact store_get_self _ _ _)
  set L3 : Store := L2.insert "minted" (uint256Value (argWord I)) with hL3
  set L4 : Store := L3.insert "__a2" (.address a) with hL4
  -- pc 574: the `balanceOf` call at 612
  have rd10 := wrapperBlocks.wrapper_block_574 (immWords := wordsOf imms) (by simp) rd9
  simp only [wrapperBlocks.wrapper_block_574_stack, wrapperBlocks.wrapper_block_574_memory, wordsOf_TOKEN' hget,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 96 (by decide), ulit_toNat' 160 (by decide),
    ulit_toNat' 192 (by decide)] at rd10
  obtain ⟨hb0, hb1, hb2, hb3⟩ := bal2Mem_sizes (addrWord a) I (argWord I) W4 hW4
  obtain ⟨evm2, σ2, z2, out2, _, _, hcall2, hs2, rd11, hsize2⟩ :=
    typedStaticCallBridge (cfg := config) (name := "balanceOf") (args := [.address I.codeOwner]) rd10 hs1
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨612⟩ : UInt256), .STATICCALL, none))
      (by rw [encode_balanceOf, ulit_toNat' 188 (by decide), ulit_toNat' 36 (by decide), bal2Mem_input _ _ _ _ hW4])
      (by rw [ulit_toNat' 36 (by decide)]; norm_num) (by simp)
  have hcanon2 : (solcSlotWordAt ⟨0⟩ σ2 I).toNat < EVM.addressModulus := by
    have h := typedCallViaEVM_static_storage_getD_of_accounts_eq ⟨0⟩ ⟨0⟩ hs1.accounts hcall2
    rw [← hs2.accounts, hs2.env, hs1.env] at h
    show ((σ2.get? I.codeOwner).option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ⟨0⟩ ⟨0⟩)).toNat < _
    rw [h]
    exact hcanon1
  rw [ofUInt256_ofNat_eq_address] at hcall2
  have rd12 := RD.normalizePC (pc' := UInt256.ofNat 613) rd11 (by native_decide)
  have hrecv2 : evalExpr? config (frame imms L4) evm1 (.var "__a2") = .ok (.address a) :=
    evalVar imms _ _ "__a2" _ (by rw [hL4]; exact store_get_self _ _ _)
  have heth2 : evalExpr? config (frame imms L4) evm1 (.intLit 0) = .ok (.int 0) := by rw [evalExpr?]; rfl
  have hargs2 : evalExprs? config (frame imms L4) evm1 [.env .this] = .ok [.address I.codeOwner] := by
    rw [evalExprs?, evalThis, hs1.env, evalExprs?]; rfl
  -- the body up to the second call, for the revert cases
  have hpre : ∀ result, ExecBlock fork config (frame imms L4) evm1
      ([.externalCall (.var "__a2") "balanceOf" (.intLit 0) [.env .this] "held" false,
        .ite (.binary .and (.binary .gt (.storage tsRef) (.intLit 0)) (.binary .gt (.var "held") (.var "amount")))
          [.assign .localVar { base := "minted", steps := [] }
            (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "amount") (.storage tsRef)))
              (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "held") (.var "amount"))))] []] ++ wrapTailStmts) result →
      ExecBlock fork config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) wrapTransition.body result := by
    intro result h
    rw [wrapBody_eq]
    exact ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _))
          (ExecBlock.consNormal hcall1S
            (ExecBlock.consNormal (ExecStmt.requireTrue hokT)
              (ExecBlock.consNormal (ExecStmt.letDecl hamtM)
                (ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_TOKEN hget _ _)) h))))))
  cases z2 with
  | false =>
    have rd13 := wrapperBlocks.wrapper_block_613_fallthrough (by simp) (by decide) rd12
    have rd14 := wrapperBlocks.wrapper_block_617 (by simp [wrapperBlocks.wrapper_block_613_fallthrough_stack]) rd13
    exact RDrev.reEquivExecutionRevert hcode' rd14 hd hdec (ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consRevert (ExecStmt.externalCallFailure (hperm := Or.inl rfl) hrecv2 heth2 hargs2 hcall2))))
  | true =>
  have rd13 := wrapperBlocks.wrapper_block_613_taken (by simp) (by decide)
    (by apply D_J_contains_append_left; jump_dest) rd12
  simp only [wrapperBlocks.wrapper_block_613_taken_stack] at rd13
  have hout2 : out2.size < UInt256.size := lt_size_of_lt_sign (by omega)
  by_cases hshort2 : out2.size < 32
  · have rd14 := wrapperBlocks.wrapper_block_624_taken (by simp)
      (by rw [ult_one (by rw [ulit_toNat' _ hout2, ulit_toNat' 32 (by decide)]; exact hshort2)]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd13
    have rd15 := wrapperBlocks.wrapper_block_1760 (by simp) rd14
    exact RDrev.reEquivExecutionRevert hcode' rd15 hd hdec (ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hrecv2 heth2 hargs2 hcall2
        (by rw [decode_balanceOf, decodeReturn_uint256_short out2 hshort2]; rfl)))))
  have h32' : 32 ≤ out2.size := by omega
  have rd14 := wrapperBlocks.wrapper_block_624_fallthrough (by simp)
    (by exact ult_zero (by rw [ulit_toNat' _ hout2, ulit_toNat' 32 (by decide)]; omega)) rd13
  obtain ⟨hw, hhw⟩ : ∃ hw, retWord out2 = hw := ⟨_, rfl⟩
  rw [ulit_toNat' 160 (by decide), min32_toNat out2.size h32' hout2,
    write_out_eq_word out2 _ 160 h32' (by rw [hb3] <;> omega), hhw] at rd14
  set W6 := hw.toByteArray.write 0 (bal2Mem (addrWord a) I (argWord I) W4) 160 32 with hW6def
  have hW6 : W6.size = 256 := by
    rw [hW6def, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hb3] <;> omega)]; exact hb3
  have hload160 : memLoad (UInt256.ofNat 160) W6 = hw :=
    memLoad_write_back _ _ 160 (by decide) (by rw [hb3]; exact lt_usize _ (by decide))
  set W7 := hw.toByteArray.write 0 W6 128 32 with hW7def
  have hW7 : W7.size = 256 := by
    rw [hW7def, byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hW6] <;> omega)]; exact hW6
  have hload128 : memLoad (UInt256.ofNat 128) W7 = hw :=
    memLoad_write_back _ _ 128 (by decide) (by rw [hW6]; exact lt_usize _ (by decide))
  have hW7r : W7.readWithPadding 96 32 = (argWord I).toByteArray := by
    rw [hW7def, write32_read_below _ _ 128 96 (by rw [toByteArray_size]) (by rw [hW6] <;> omega) (by decide), hW6def,
      write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [hb3] <;> omega) (by decide),
      bal2Mem_read96 _ _ _ _ hW4]
  -- Stele after the second call
  have hdec2 : config.externalABI.decode? "balanceOf" out2 = some [uint256Value hw] := by
    rw [decode_balanceOf, decodeReturn_uint256_ok out2 h32' (by omega), hhw]; rfl
  set L5 : Store := L4.insert "held" (uint256Value hw) with hL5
  have hcall2S : ExecStmt fork config (frame imms L4) evm1
      (.externalCall (.var "__a2") "balanceOf" (.intLit 0) [.env .this] "held" false) (.ok (frame imms L5) evm2) :=
    @ExecStmt.externalCallSuccess (hperm := Or.inl rfl) fork config 0 (frame imms L4) evm1 (.var "__a2") a (.intLit 0) [.env .this]
      [.address I.codeOwner] "balanceOf" evm2 out2 false [uint256Value hw] "held" hrecv2 heth2 hargs2 hcall2 hdec2
  have hamt5 : ∀ evm, evalExpr? config (frame imms L5) evm (.var "amount") = .ok (uint256Value (argWord I)) := fun evm =>
    evalVar imms _ _ "amount" _ (by
      rw [hL5, store_get_ne _ _ (by decide), hL4, store_get_ne _ _ (by decide), hL3, store_get_ne _ _ (by decide),
        hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _)
  have hheld5 : ∀ evm, evalExpr? config (frame imms L5) evm (.var "held") = .ok (uint256Value hw) := fun evm =>
    evalVar imms _ _ "held" _ (by rw [hL5]; exact store_get_self _ _ _)
  have hL5m : L5.get? "minted" = some (uint256Value (argWord I)) := by
    rw [hL5, store_get_ne _ _ (by decide), hL4, store_get_ne _ _ (by decide), hL3]; exact store_get_self _ _ _
  have hL5sh : L5.get? "shares" = none := by simp [hL5, hL4, hL3, hL2, hL1]
  have hL5ts : L5.get? "totalShares" = none := by simp [hL5, hL4, hL3, hL2, hL1]
  have hL5hook : L5.get? "hook" = none := by simp [hL5, hL4, hL3, hL2, hL1]
  have hts2 : evalExpr? config (frame imms L5) evm2 (.storage tsRef) = .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ2 I)) := by
    rw [evalTsRead imms _ _ hL5ts, hs2.storageRead]; rfl
  obtain ⟨ts2, hts2eq⟩ : ∃ x, solcSlotWordAt (UInt256.ofNat 2) σ2 I = x := ⟨_, rfl⟩
  rw [hts2eq] at hts2
  have hgtts := evalExpr_gt_zero hts2
  -- the tail from pc 730, given the locals after the `if`
  have htail : ∀ (minted : UInt256) (M : ByteArray), M.size = 256 → M.readWithPadding 96 32 = minted.toByteArray →
      ∀ {aw : UInt256} {rdata : ByteArray} {k C : ℕ},
      RD fork (wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms)) I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 730) [solcSelectorWord I] M aw rdata σ2 k C →
      ∀ (L : Store), L.get? "minted" = some (uint256Value minted) → L.get? "shares" = none → L.get? "totalShares" = none →
        L.get? "hook" = none →
      ExecStmt fork config (frame imms L5) evm2
        (.ite (.binary .and (.binary .gt (.storage tsRef) (.intLit 0)) (.binary .gt (.var "held") (.var "amount")))
          [.assign .localVar { base := "minted", steps := [] }
            (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "amount") (.storage tsRef)))
              (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "held") (.var "amount"))))] [])
        (.ok (frame imms L) evm2) →
      runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
    intro minted M hM hMr aw rdata k C rdM L hLm hLsh hLts hLhook hite
    exact wrapTail imms hwf hcode' hd hdec σ2 evm2 hs2 hcanon2 minted M hM hMr rdM L hLm hLsh hLts hLhook
      (fun result h => hpre _ (ExecBlock.consNormal hcall2S (ExecBlock.consNormal hite h)))
  -- pc 633: `totalShares > 0`
  by_cases hts0 : ts2 = ⟨0⟩
  · obtain ⟨_, _, rd15⟩ := wrapperBlocks.wrapper_block_633_taken (by simp) (by rw [slotWord_eq, hts2eq, hts0]; decide)
      (by apply D_J_contains_append_left; jump_dest) rd14
    simp only [wrapperBlocks.wrapper_block_633_taken_stack, wrapperBlocks.wrapper_block_633_taken_memory,
      ulit_toNat' 160 (by decide), ulit_toNat' 128 (by decide)] at rd15
    rw [hload160] at rd15
    have rd16 := wrapperBlocks.wrapper_block_660 (by simp) rd15
    simp only [wrapperBlocks.wrapper_block_660_stack] at rd16
    have rd17 := wrapperBlocks.wrapper_block_662_taken (by simp) (by decide)
      (by apply D_J_contains_append_left; jump_dest) rd16
    simp only [wrapperBlocks.wrapper_block_662_taken_stack] at rd17
    exact htail (argWord I) W7 hW7 hW7r rd17 L5 hL5m hL5sh hL5ts hL5hook
      (ExecStmt.iteFalse (evalExpr_and_false (by rw [hgtts, hts0]; rfl)) ExecBlock.nil)
  have hts2pos : 0 < ts2.toNat := by
    rcases Nat.eq_zero_or_pos ts2.toNat with h | h
    · exact absurd (u256_inj (b := (⟨0⟩ : UInt256)) h) hts0
    · exact h
  obtain ⟨_, _, rd15⟩ := wrapperBlocks.wrapper_block_633_fallthrough (by simp)
    (by rw [slotWord_eq, hts2eq]; exact isZero_eq_zero_of_ne hts0) rd14
  simp only [wrapperBlocks.wrapper_block_633_fallthrough_stack, wrapperBlocks.wrapper_block_633_fallthrough_memory,
    ulit_toNat' 160 (by decide), ulit_toNat' 128 (by decide)] at rd15
  rw [hload160] at rd15
  have rd16 := wrapperBlocks.wrapper_block_649 (by simp) (by apply D_J_contains_append_left; jump_dest) rd15
  simp only [wrapperBlocks.wrapper_block_649_stack, ulit_toNat' 128 (by decide)] at rd16
  rw [hload128] at rd16
  have hgtheld := evalExpr_gt_words (hheld5 evm2) (hamt5 evm2)
  by_cases hle : hw.toNat ≤ (argWord I).toNat
  · -- `held > amount` is false: the `if` is skipped
    rw [ugt_zero hle] at rd16
    have rd17 := wrapperBlocks.wrapper_block_662_taken (by simp) (by decide)
      (by apply D_J_contains_append_left; jump_dest) rd16
    simp only [wrapperBlocks.wrapper_block_662_taken_stack] at rd17
    exact htail (argWord I) W7 hW7 hW7r rd17 L5 hL5m hL5sh hL5ts hL5hook
      (ExecStmt.iteFalse (evalExpr_and_true (by rw [hgtts, decide_eq_true hts2pos]) (by rw [hgtheld, decide_eq_false (by omega)]))
        ExecBlock.nil)
  have hlt : (argWord I).toNat < hw.toNat := by omega
  rw [ugt_one hlt] at rd16
  have rd17 := wrapperBlocks.wrapper_block_662_fallthrough (by simp) (by decide) rd16
  simp only [wrapperBlocks.wrapper_block_662_fallthrough_stack] at rd17
  have handT : evalExpr? config (frame imms L5) evm2
      (.binary .and (.binary .gt (.storage tsRef) (.intLit 0)) (.binary .gt (.var "held") (.var "amount"))) = .ok (.bool true) :=
    evalExpr_and_true (by rw [hgtts, decide_eq_true hts2pos]) (by rw [hgtheld, decide_eq_true hlt])
  -- pc 668: `amount * totalShares`
  by_cases hfit : (argWord I).toNat * ts2.toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd18⟩ := wrapperBlocks.wrapper_block_668_taken (by simp)
      (by rw [slotWord_eq, hts2eq]; exact mulCheck_overflow _ _ (by show UInt256.size ≤ (argWord I).toNat * ts2.toNat; omega))
      (by apply D_J_contains_append_left; jump_dest) rd17
    have rd19 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_668_taken_stack]) rd18
    exact RDrev.reEquivExecutionRevert hcode' rd19 hd hdec (ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consNormal hcall2S (ExecBlock.consRevert (ExecStmt.iteTrue handT (ExecBlock.consRevert
        (ExecStmt.assignExprRevert (evalExpr_binary_revert_left (by decide) (by decide)
          (evalExpr_uint256_mul_overflow (hamt5 _) hts2 (by omega))))))))))
  obtain ⟨_, _, rd18⟩ := wrapperBlocks.wrapper_block_668_fallthrough (by simp)
    (by rw [slotWord_eq, hts2eq]; exact mulCheck_ok _ _ hfit) rd17
  simp only [wrapperBlocks.wrapper_block_668_fallthrough_stack] at rd18
  rw [slotWord_eq, hts2eq] at rd18
  -- pc 690: `held - amount`; pc 710: the divisor; pc 720: `minted`
  have hsubne : UInt256.sub hw (argWord I) ≠ ⟨0⟩ := by
    intro h
    have h' := congrArg UInt256.toNat h
    rw [usub_toNat (by omega)] at h'
    change hw.toNat - (argWord I).toNat = 0 at h'
    omega
  have rd19 := wrapperBlocks.wrapper_block_690_fallthrough (by simp)
    (by
      rw [hload128]
      exact ugt_zero (by
        show (UInt256.sub hw (argWord I)).toNat ≤ hw.toNat
        rw [usub_toNat (by omega)]; omega)) rd18
  simp only [wrapperBlocks.wrapper_block_690_fallthrough_stack] at rd19
  rw [hload128] at rd19
  have rd20 := wrapperBlocks.wrapper_block_710_fallthrough (by simp) (isZero_eq_zero_of_ne hsubne) rd19
  simp only [wrapperBlocks.wrapper_block_710_fallthrough_stack] at rd20
  have rd21 := wrapperBlocks.wrapper_block_720 (by simp) rd20
  simp only [wrapperBlocks.wrapper_block_720_stack, wrapperBlocks.wrapper_block_720_memory, ulit_toNat' 96 (by decide)] at rd21
  obtain ⟨minted, hminted⟩ : ∃ m, UInt256.div (UInt256.mul (argWord I) ts2) (UInt256.sub hw (argWord I)) = m := ⟨_, rfl⟩
  rw [hminted] at rd21
  have hW8 : (minted.toByteArray.write 0 W7 96 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hW7] <;> omega)]; exact hW7
  have hW8r : (minted.toByteArray.write 0 W7 96 32).readWithPadding 96 32 = minted.toByteArray :=
    toByteArray_write_read_back_of_gap _ _ 96 (by rw [hW7]; exact lt_usize _ (by decide))
  have hdiv : evalExpr? config (frame imms L5) evm2
      (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "amount") (.storage tsRef)))
        (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "held") (.var "amount")))) = .ok (uint256Value minted) := by
    rw [evalExpr_uint256_div (evalExpr_uint256_mul (hamt5 _) hts2 hfit) (evalExpr_uint256_sub (hheld5 _) (hamt5 _) (by omega)) hsubne,
      hminted]
  have hassignL : assignStorageRef? config (frame imms L5) evm2 .localVar { base := "minted", steps := [] } (uint256Value minted) =
      .ok (frame imms (L5.insert "minted" (uint256Value minted)), evm2) :=
    assignLocalVar_frame (old := uint256Value (argWord I)) hL5m
  have hite : ExecStmt fork config (frame imms L5) evm2
      (.ite (.binary .and (.binary .gt (.storage tsRef) (.intLit 0)) (.binary .gt (.var "held") (.var "amount")))
        [.assign .localVar { base := "minted", steps := [] }
          (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "amount") (.storage tsRef)))
            (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "held") (.var "amount"))))] [])
      (.ok (frame imms (L5.insert "minted" (uint256Value minted))) evm2) :=
    ExecStmt.iteTrue handT (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inl rfl) hdiv hassignL) ExecBlock.nil)
  exact htail minted (minted.toByteArray.write 0 W7 96 32) hW8 hW8r rd21 (L5.insert "minted" (uint256Value minted))
    (store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide)]; exact hL5sh)
    (by rw [store_get_ne _ _ (by decide)]; exact hL5ts)
    (by rw [store_get_ne _ _ (by decide)]; exact hL5hook)
    hite

end Tests.Pipeline.VyperWrapper
