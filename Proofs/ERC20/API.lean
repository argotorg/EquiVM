import Proofs.ERC20.Invariant

/-!
# ERC20 — the supply invariant over the whole ABI

`Inv` is preserved by every call and established by the constructor:

* `erc20_steleExec_preserves_inv`: whatever the Stele dispatcher (`steleExec`) returns for any
  calldata, environment and state, the returned state satisfies `Inv` if the initial one did and
  the slots the call writes are unshared (`CallClean`);
* `erc20_steleCtorExec_establishes_inv` / `erc20_deployment_establishes_inv`: whatever the
  constructor returns from a fresh (all-balances-zero) state satisfies `Inv`, assuming
  `SupplyClean` and `BalClean` for the deployer.

Each public function's body is taken apart statement by statement with the `execBlock_*_cons`
inversion lemmas of `Reasoning.SteleBody`, so the theorems cover *every* derivation of the
relational semantics.  On the success path the intermediate values are pinned by the evaluation
lemmas of `Examples/ERC20`, so the returned state is the post-state whose invariant is proved in
`Proofs.ERC20.Invariant`; every other path reverts and returns no state.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace ERC20

/-! ## The bodies: whatever they return satisfies `Inv` -/

section Bodies

variable {evm evm' : EVM.State} {I : ExecutionEnv} {r : ExecResult}

/-- `transfer`: every run that reaches a state preserves `Inv`. -/
theorem transfer_block_inv (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat))
    (h : ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
      transferTransition.body r)
    (hInv : Inv evm) (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  -- require(msg.value == 0)
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  -- uint256 fromBalance = balanceOf[msg.sender]
  rcases execBlock_letDecl_cons h with rfl | ⟨v₁, hv₁, h⟩
  · simp at hr
  cases (evalExpr_transfer_sender_balance evm I).symm.trans hv₁
  -- require(fromBalance >= value)
  rcases execBlock_require_cons h with rfl | ⟨hc, h⟩
  · simp at hr
  by_cases henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat
  swap
  · cases (evalExpr_transfer_require_from_false evm I (by omega)).symm.trans hc
  -- balanceOf[msg.sender] = fromBalance - value
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₂, fr₂, evm₂, hv₂, ha₂, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_transfer_debit evm I henough).symm.trans hv₂
  cases (transferAssignSender evm I).symm.trans ha₂
  -- uint256 toBalance = balanceOf[to]
  rcases execBlock_letDecl_cons h with rfl | ⟨v₃, hv₃, h⟩
  · simp at hr
  cases (evalExpr_transfer_to_balance evm I).symm.trans hv₃
  -- uint256 newToBalance = toBalance + value   (checked)
  rcases execBlock_letDecl_cons h with rfl | ⟨v₄, hv₄, h⟩
  · simp at hr
  by_cases hfit : transferNewToNat evm I < UInt256.size
  swap
  · cases (evalExpr_transfer_newToBalance_revert evm I (by omega)).symm.trans hv₄
  cases (evalExpr_transfer_newToBalance evm I hfit).symm.trans hv₄
  -- balanceOf[to] = newToBalance
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₅, fr₅, evm₅, hv₅, ha₅, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_transfer_newToBalance_var evm I).symm.trans hv₅
  cases (transferAssignTo evm I hfit).symm.trans ha₅
  -- emit Transfer(msg.sender, to, value)
  rcases execBlock_emit_cons h with rfl | rfl | h
  · simp at hr
  · simp at hr
  -- return true
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  exact ⟨transferPostState_executionEnv evm I,
    transfer_preserves_inv evm I hcs hct henough hfit hInv⟩

/-- `transferFrom`: every run that reaches a state preserves `Inv`. -/
theorem transferFrom_block_inv
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat))
    (h : ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      transferFromTransition.body r)
    (hInv : Inv evm) (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  -- require(msg.value == 0)
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  -- uint256 currentAllowance = allowance[from][msg.sender]
  rcases execBlock_letDecl_cons h with rfl | ⟨v₁, hv₁, h⟩
  · simp at hr
  cases (evalExpr_transferFrom_currentAllowance evm I).symm.trans hv₁
  -- require(currentAllowance >= value)
  rcases execBlock_require_cons h with rfl | ⟨hc₁, h⟩
  · simp at hr
  by_cases hallow : (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evm I).toNat
  swap
  · cases (evalExpr_transferFrom_require_allowance_false evm I (by omega)).symm.trans hc₁
  -- uint256 fromBalance = balanceOf[from]
  rcases execBlock_letDecl_cons h with rfl | ⟨v₂, hv₂, h⟩
  · simp at hr
  cases (evalExpr_transferFrom_from_balance evm I).symm.trans hv₂
  -- require(fromBalance >= value)
  rcases execBlock_require_cons h with rfl | ⟨hc₂, h⟩
  · simp at hr
  by_cases hbal : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evm I).toNat
  swap
  · cases (evalExpr_transferFrom_require_from_false evm I (by omega)).symm.trans hc₂
  -- allowance[from][msg.sender] = currentAllowance - value
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₃, fr₃, evm₃, hv₃, ha₃, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_transferFrom_allowance_debit evm I hallow).symm.trans hv₃
  cases (transferFromAssignAllowance evm I).symm.trans ha₃
  -- balanceOf[from] = balanceOf[from] - value   (checked)
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₄, fr₄, evm₄, hv₄, ha₄, h⟩
  · simp at hr
  · simp at hr
  by_cases hdebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromAfterAllowanceState evm I) I).toNat
  swap
  · cases (evalExpr_transferFrom_balance_debit_revert evm (transferFromAfterAllowanceState evm I) I
      (by omega)).symm.trans hv₄
  cases (evalExpr_transferFrom_balance_debit evm (transferFromAfterAllowanceState evm I) I
    hdebit).symm.trans hv₄
  cases (transferFromAssignFrom evm I).symm.trans ha₄
  -- uint256 toBalance = balanceOf[to]
  rcases execBlock_letDecl_cons h with rfl | ⟨v₅, hv₅, h⟩
  · simp at hr
  cases (evalExpr_transferFrom_to_balance evm I).symm.trans hv₅
  -- uint256 newToBalance = toBalance + value   (checked)
  rcases execBlock_letDecl_cons h with rfl | ⟨v₆, hv₆, h⟩
  · simp at hr
  by_cases hfit : transferFromNewToNat evm I < UInt256.size
  swap
  · cases (evalExpr_transferFrom_newToBalance_revert evm I (by omega)).symm.trans hv₆
  cases (evalExpr_transferFrom_newToBalance evm I hfit).symm.trans hv₆
  -- balanceOf[to] = newToBalance
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₇, fr₇, evm₇, hv₇, ha₇, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_transferFrom_newToBalance_var evm I).symm.trans hv₇
  cases (transferFromAssignTo evm I hfit).symm.trans ha₇
  -- emit Transfer(from, to, value)
  rcases execBlock_emit_cons h with rfl | rfl | h
  · simp at hr
  · simp at hr
  -- return true
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  exact ⟨transferFromPostState_executionEnv evm I,
    transferFrom_preserves_inv evm I hca hcf hct hbal hfit hInv⟩

/-- `approve`: every run that reaches a state preserves `Inv`. -/
theorem approve_block_inv
    (hca : AllowClean evm.executionEnv.source (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (h : ExecBlock erc20Config { contract := erc20Contract, locals := approveStore I } evm
      approveTransition.body r)
    (hInv : Inv evm) (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  -- require(msg.value == 0)
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  -- allowance[msg.sender][spender] = value
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₁, fr₁, evm₁, hv₁, ha₁, h⟩
  · simp at hr
  · simp at hr
  cases (evalExpr_approve_value evm I).symm.trans hv₁
  cases (approveAssign evm I).symm.trans ha₁
  -- emit Approval(msg.sender, spender, value)
  rcases execBlock_emit_cons h with rfl | rfl | h
  · simp at hr
  · simp at hr
  -- return true
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  exact ⟨approvePostState_executionEnv evm I, approve_preserves_inv evm I hca hInv⟩

/-- A view body (`require(msg.value == 0); return …`) returns its initial state. -/
theorem view_block_inv {stele : Frame} {c : Expr} {es : List Expr}
    (h : ExecBlock erc20Config stele evm [.require c, .return es] r)
    (hInv : Inv evm) (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  rcases execBlock_return_cons h with rfl | ⟨vs, -, rfl⟩
  · simp at hr
  simp only [resultState?_returned, Option.some.injEq] at hr
  subst hr
  exact ⟨rfl, hInv⟩

/-- The constructor body, run on well-typed `initialSupply`: every run that reaches a state from
    an all-balances-zero state establishes `Inv`. -/
theorem ctor_block_inv (hsup : SupplyClean) (hcd : BalClean evm.executionEnv.source) {i : Int}
    (h0 : 0 ≤ i) (hlt : i < Int.ofNat (EVM.twoPow 256))
    (h : ExecBlock erc20Config { contract := erc20Contract, locals := erc20CtorLocals i } evm
      erc20Contract.ctor.body r)
    (hzero : ∀ a, balOf evm a = 0) (hr : resultState? r = some evm') :
    evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  have hvar : ∀ s : EVM.State, evalExpr? erc20Config
      { contract := erc20Contract, locals := erc20CtorLocals i } s (.var "initialSupply") =
        .ok (.int i) := fun s => by
    simp only [evalExpr?, erc20CtorLocals_get_initialSupply, EvalResult.ofOption]
  -- require(msg.value == 0)
  rcases execBlock_require_cons h with rfl | ⟨-, h⟩
  · simp at hr
  -- balanceOf[msg.sender] = initialSupply
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₁, fr₁, evm₁, hv₁, ha₁, h⟩
  · simp at hr
  · simp at hr
  cases (hvar evm).symm.trans hv₁
  cases (erc20CtorAssignBalance evm i h0 hlt).symm.trans ha₁
  -- totalSupply = initialSupply
  rcases execBlock_assign_cons h with rfl | rfl | ⟨v₂, fr₂, evm₂, hv₂, ha₂, h⟩
  · simp at hr
  · simp at hr
  cases (hvar _).symm.trans hv₂
  cases (erc20CtorAssignTotalSupply _ i h0 hlt).symm.trans ha₂
  cases h
  simp only [resultState?_ok, Option.some.injEq] at hr
  subst hr
  exact ⟨erc20CtorPostState_executionEnv evm (EVM.word i.toNat),
    constructor_establishes_inv evm (EVM.word i.toNat) hsup hcd hzero⟩

end Bodies

/-! ## Transition bodies: whatever they return satisfies `Inv` -/

section Transitions

variable {evm evm' : EVM.State} {I : ExecutionEnv} {fr : Frame} {ret : Option (List Value)}

theorem transfer_returned_inv (hcs : BalClean evm.executionEnv.source)
    (hct : BalClean (AccountAddress.ofNat (transferToWord I).toNat))
    (h : ExecTransitionBody erc20Config erc20Contract evm (transferStore I)
      transferTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact transfer_block_inv hcs hct hb hInv (hr.trans (resultState?_returned fr evm' ret))

theorem transferFrom_returned_inv
    (hca : AllowClean (AccountAddress.ofNat (transferFromFromWord I).toNat)
      evm.executionEnv.source)
    (hcf : BalClean (AccountAddress.ofNat (transferFromFromWord I).toNat))
    (hct : BalClean (AccountAddress.ofNat (transferFromToWord I).toNat))
    (h : ExecTransitionBody erc20Config erc20Contract evm (transferFromStore I)
      transferFromTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact transferFrom_block_inv hca hcf hct hb hInv (hr.trans (resultState?_returned fr evm' ret))

theorem approve_returned_inv
    (hca : AllowClean evm.executionEnv.source (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (h : ExecTransitionBody erc20Config erc20Contract evm (approveStore I)
      approveTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact approve_block_inv hca hb hInv (hr.trans (resultState?_returned fr evm' ret))

theorem totalSupply_returned_inv
    (h : ExecTransitionBody erc20Config erc20Contract evm ∅
      totalSupplyTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact view_block_inv hb hInv (hr.trans (resultState?_returned fr evm' ret))

theorem balanceOf_returned_inv
    (h : ExecTransitionBody erc20Config erc20Contract evm (balanceOfStore I)
      balanceOfTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact view_block_inv hb hInv (hr.trans (resultState?_returned fr evm' ret))

theorem allowance_returned_inv
    (h : ExecTransitionBody erc20Config erc20Contract evm (allowanceStore I)
      allowanceTransition.body (.returned fr evm' ret))
    (hInv : Inv evm) : evm'.executionEnv = evm.executionEnv ∧ Inv evm' := by
  obtain ⟨r, hb, hr⟩ := execFuncBody_block h
  exact view_block_inv hb hInv (hr.trans (resultState?_returned fr evm' ret))

end Transitions

/-! ## Dispatch: the decoded arguments are the stores the bodies were analysed with -/

section Decode

variable {I : ExecutionEnv} {callargs : Store}

theorem decode_approve_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata? (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some callargs) :
    callargs = approveStore I := by
  change decodeCalldata (approveTransition.params.map Param.name)
    (transitionSignature approveTransition).paramTypes I.calldata = some callargs at h
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (approveSpenderWord I).toNat < EVM.addressModulus
      · rw [erc20Decode_approve_ok hsz68 hbig hcanon] at h; exact (Option.some.inj h).symm
      · rw [erc20Decode_approve_none_noncanon hsz68 hbig hcanon] at h; cases h
    · rw [erc20Decode_approve_none_huge (by omega)] at h; cases h
  · rw [erc20Decode_approve_none_short hsz4 (by omega)] at h; cases h

theorem decode_totalSupply_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata?
      (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some callargs) :
    callargs = ∅ := by
  change decodeCalldata (totalSupplyTransition.params.map Param.name)
    (transitionSignature totalSupplyTransition).paramTypes I.calldata = some callargs at h
  rw [erc20Decode_totalSupply hsz4] at h
  exact (Option.some.inj h).symm

theorem decode_transferFrom_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata?
      (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some callargs) :
    callargs = transferFromStore I := by
  change decodeCalldata (transferFromTransition.params.map Param.name)
    (transitionSignature transferFromTransition).paramTypes I.calldata = some callargs at h
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcf : (transferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hct : (transferFromToWord I).toNat < EVM.addressModulus
        · rw [erc20Decode_transferFrom_ok hsz100 hbig hcf hct] at h
          exact (Option.some.inj h).symm
        · rw [erc20Decode_transferFrom_none_noncanon_to hsz100 hbig hcf hct] at h; cases h
      · rw [erc20Decode_transferFrom_none_noncanon_from hsz100 hbig hcf] at h; cases h
    · rw [erc20Decode_transferFrom_none_huge (by omega)] at h; cases h
  · rw [erc20Decode_transferFrom_none_short hsz4 (by omega)] at h; cases h

theorem decode_balanceOf_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata?
      (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some callargs) :
    callargs = balanceOfStore I := by
  change decodeCalldata (balanceOfTransition.params.map Param.name)
    (transitionSignature balanceOfTransition).paramTypes I.calldata = some callargs at h
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
      · rw [erc20Decode_balanceOf_ok hsz36 hbig hcanon] at h; exact (Option.some.inj h).symm
      · rw [erc20Decode_balanceOf_none_noncanon hsz36 hbig hcanon] at h; cases h
    · rw [erc20Decode_balanceOf_none_huge (by omega)] at h; cases h
  · rw [erc20Decode_balanceOf_none_short hsz4 (by omega)] at h; cases h

theorem decode_transfer_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata? (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some callargs) :
    callargs = transferStore I := by
  change decodeCalldata (transferTransition.params.map Param.name)
    (transitionSignature transferTransition).paramTypes I.calldata = some callargs at h
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (transferToWord I).toNat < EVM.addressModulus
      · rw [erc20Decode_transfer_ok hsz68 hbig hcanon] at h; exact (Option.some.inj h).symm
      · rw [erc20Decode_transfer_none_noncanon hsz68 hbig hcanon] at h; cases h
    · rw [erc20Decode_transfer_none_huge (by omega)] at h; cases h
  · rw [erc20Decode_transfer_none_short hsz4 (by omega)] at h; cases h

theorem decode_allowance_eq (hsz4 : 4 ≤ I.calldata.size)
    (h : erc20Config.externalABI.decodeCalldata?
      (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some callargs) :
    callargs = allowanceStore I := by
  change decodeCalldata (allowanceTransition.params.map Param.name)
    (transitionSignature allowanceTransition).paramTypes I.calldata = some callargs at h
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hco : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcs : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · rw [erc20Decode_allowance_ok hsz68 hbig hco hcs] at h; exact (Option.some.inj h).symm
        · rw [erc20Decode_allowance_none_noncanon_spender hsz68 hbig hco hcs] at h; cases h
      · rw [erc20Decode_allowance_none_noncanon_owner hsz68 hbig hco] at h; cases h
    · rw [erc20Decode_allowance_none_huge (by omega)] at h; cases h
  · rw [erc20Decode_allowance_none_short hsz4 (by omega)] at h; cases h

/-- A selector match means the calldata holds at least the selector. -/
theorem calldata_size_of_selectorDispatch {t : TransitionDecl}
    (hsel : selectorDispatchMsg erc20Contract I.calldata = some t) : 4 ≤ I.calldata.size := by
  rw [selectorDispatchMsg_eq_dispatchList] at hsel
  have hmem := dispatchList_some_mem hsel
  have hmatch := dispatchList_some_selIs hsel
  simp [erc20Contract] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc20ApproveSelectorBytes] at hmatch; exact erc20ApproveSelector_size hmatch
  · rw [selectorOf, erc20TotalSupplySelectorBytes] at hmatch
    exact erc20TotalSupplySelector_size hmatch
  · rw [selectorOf, erc20TransferFromSelectorBytes] at hmatch
    exact erc20TransferFromSelector_size hmatch
  · rw [selectorOf, erc20BalanceOfSelectorBytes] at hmatch; exact erc20BalanceOfSelector_size hmatch
  · rw [selectorOf, erc20TransferSelectorBytes] at hmatch; exact erc20TransferSelector_size hmatch
  · rw [selectorOf, erc20AllowanceSelectorBytes] at hmatch; exact erc20AllowanceSelector_size hmatch

end Decode

/-! ## The whole ABI -/

/-- The calldata argument at byte `4 + off`, read as an address. -/
abbrev callArg (I : ExecutionEnv) (off : UInt256) : AccountAddress :=
  AccountAddress.ofNat
    (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + off).toNat 32)).toNat

/-- The slots a call can write are unshared.  The first argument (`callArg I ⟨0⟩`) is `transfer`'s
    `to`, `approve`'s `spender` and `transferFrom`'s `from`; the second (`callArg I ⟨32⟩`) is
    `transferFrom`'s `to`.  Each function uses only the fields for the slots it writes. -/
structure CallClean (I : ExecutionEnv) : Prop where
  /-- `balanceOf[caller]` (`transfer`). -/
  caller : BalClean I.source
  /-- `balanceOf[arg₁]` (`transfer`'s `to`, `transferFrom`'s `from`). -/
  arg₁ : BalClean (callArg I ⟨0⟩)
  /-- `balanceOf[arg₂]` (`transferFrom`'s `to`). -/
  arg₂ : BalClean (callArg I ⟨32⟩)
  /-- `allowance[caller][arg₁]` (`approve`). -/
  callerArg₁ : AllowClean I.source (callArg I ⟨0⟩)
  /-- `allowance[arg₁][caller]` (`transferFrom`). -/
  arg₁Caller : AllowClean (callArg I ⟨0⟩) I.source

/-- **Every call preserves the supply invariant.**  Whatever the ERC20 spec returns for a call —
    any calldata, caller, value, and pre-state satisfying `Inv`, whose written slots are unshared
    (`CallClean`) — the returned state satisfies `Inv` (and belongs to the same contract: its
    environment is the call's). -/
theorem erc20_steleExec_preserves_inv
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {rc : ReturnConvention}
    {fr : Frame} {evm' : EVM.State} {ret : Option (List Value)}
    (hclean : CallClean I)
    (hInv : Inv (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hexec : steleExec erc20Config erc20Contract ∅ σ σ₀ g A I (.returned fr evm' ret) rc) :
    evm'.executionEnv = I ∧ Inv evm' := by
  cases hexec with
  | intro hsel hsig hdec hst hbody =>
    subst hsig hst
    have hsz4 := calldata_size_of_selectorDispatch hsel
    rw [selectorDispatchMsg_eq_dispatchList] at hsel
    have hmem := dispatchList_some_mem hsel
    simp [erc20Contract] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain rfl := decode_approve_eq hsz4 hdec
      exact approve_returned_inv hclean.callerArg₁ hbody hInv
    · obtain rfl := decode_totalSupply_eq hsz4 hdec
      exact totalSupply_returned_inv hbody hInv
    · obtain rfl := decode_transferFrom_eq hsz4 hdec
      exact transferFrom_returned_inv hclean.arg₁Caller hclean.arg₁ hclean.arg₂ hbody hInv
    · obtain rfl := decode_balanceOf_eq hsz4 hdec
      exact balanceOf_returned_inv hbody hInv
    · obtain rfl := decode_transfer_eq hsz4 hdec
      exact transfer_returned_inv hclean.caller hclean.arg₁ hbody hInv
    · obtain rfl := decode_allowance_eq hsz4 hdec
      exact allowance_returned_inv hbody hInv
  | fallback _ _ hfb _ _ _ _ =>
    rw [show erc20Contract.fallback = none from rfl] at hfb
    cases hfb
  | receive hrecv _ _ _ _ =>
    have hnone : receiveDispatchMsg erc20Contract I.calldata = none := by
      unfold receiveDispatchMsg; split <;> rfl
    rw [hnone] at hrecv
    cases hrecv

/-- **The constructor establishes the supply invariant.**  Whatever the ERC20 constructor returns
    for a well-typed `initialSupply` from a state without balances, the returned state satisfies
    `Inv`, assuming no balance slot is the `totalSupply` slot and the deployer's is unshared. -/
theorem erc20_steleCtorExec_establishes_inv (hsup : SupplyClean)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv} {i : Int}
    {fr : Frame} {evm' : EVM.State} {ret : Option (List Value)}
    (hcd : BalClean I.source)
    (h0 : 0 ≤ i) (hlt : i < Int.ofNat (EVM.twoPow 256))
    (hzero : ∀ a, balOf (initState σ σ₀ (Sat256.ofUInt256 g) A I) a = 0)
    (hexec : steleCtorExec erc20Config erc20Contract [.int i] σ σ₀ g A I (.returned fr evm' ret)) :
    evm'.executionEnv = I ∧ Inv evm' := by
  cases hexec with
  | intro hst _ hargs hbody =>
    subst hst hargs
    obtain ⟨r, hb, hr⟩ := execFuncBody_block hbody
    have hb' : ExecBlock erc20Config { contract := erc20Contract, locals := erc20CtorLocals i }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) erc20Contract.ctor.body r := hb
    exact ctor_block_inv hsup hcd h0 hlt hb' hzero (hr.trans (resultState?_returned fr evm' ret))

/-- The constructor, for any arguments the deployment relation admits
    (`erc20Config.selfDeployment`), establishes `Inv`. -/
theorem erc20_deployment_establishes_inv (hsup : SupplyClean)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {args : List Value} {code : ByteArray}
    {fr : Frame} {evm' : EVM.State} {ret : Option (List Value)}
    (hcd : BalClean I.source)
    (hdeploy : erc20Config.selfDeployment erc20Initcode args = some code)
    (hzero : ∀ a, balOf (initState σ σ₀ (Sat256.ofUInt256 g) A I) a = 0)
    (hexec : steleCtorExec erc20Config erc20Contract args σ σ₀ g A I (.returned fr evm' ret)) :
    evm'.executionEnv = I ∧ Inv evm' := by
  obtain ⟨i, rfl, h0, hlt, -⟩ := erc20Deployment_shape hdeploy
  exact erc20_steleCtorExec_establishes_inv hsup hcd h0 hlt hzero hexec

end ERC20
