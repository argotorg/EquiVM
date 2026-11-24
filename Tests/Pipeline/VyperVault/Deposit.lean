import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `deposit()`

Dispatcher bucket 9, arm entry pc 36: the `paused` check, the `callvalue > 0` check, the fee
(`value * 25 // 10000`, with Vyper's multiplication-overflow and subtraction-underflow checks),
`balances[msg.sender] += credited` (pc 330/362), `totalDeposits += credited` (pc 385),
`feesCollected += fee` and the `Deposited` log (pc 408).  Every checked addition can overflow and
revert; in static mode the first `SSTORE` (pc 367) halts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

abbrev u256T : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
abbrev pausedRef : StorageRef := { base := "paused", steps := [] }
abbrev balRef : StorageRef := { base := "balances", steps := [.mindex (.env .caller)] }
abbrev tdRef : StorageRef := { base := "totalDeposits", steps := [] }
abbrev fcRef : StorageRef := { base := "feesCollected", steps := [] }
abbrev feeExpr : Expr :=
  .binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.env .callvalue) (.intLit 25))) (.intLit 10000)
abbrev creditedExpr : Expr := .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.env .callvalue) (.var "fee"))
abbrev addExpr (r : StorageRef) (v : Ident) : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage r) (.var v))

theorem depositBody_eq : depositTransition.body =
    [.require (.unary .not (.storage pausedRef)),
     .require (.binary .gt (.env .callvalue) (.intLit 0)),
     .letDecl "fee" (some u256T) feeExpr,
     .letDecl "credited" (some u256T) creditedExpr,
     .assign .storage balRef (addExpr balRef "credited"),
     .assign .storage tdRef (addExpr tdRef "credited"),
     .assign .storage fcRef (addExpr fcRef "fee"),
     .emit "Deposited" [.env .caller, .var "credited"]] := by rfl

/-- The fee and the credited amount, as the bytecode computes them. -/
abbrev depositFee (wv : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul wv (UInt256.ofNat 25)) (UInt256.ofNat 10000)
abbrev depositCredited (wv : UInt256) : UInt256 := UInt256.sub wv (depositFee wv)

/-- The storage slot of `balances[msg.sender]`. -/
abbrev balSlot (I : ExecutionEnv) : UInt256 := vyperMappingSlot (UInt256.ofNat 1) (.address I.source)

/-- The account maps after each of the three stores. -/
abbrev σ1 (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (balSlot I) (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue)
abbrev σ2 (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (σ1 σ I) (UInt256.ofNat 2)
    (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue)
abbrev σ3 (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (σ2 σ I) (UInt256.ofNat 3)
    (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue)

/-- The locals after the two `let`s. -/
abbrev depositLocals (wv : UInt256) : Store :=
  ((∅ : Store).insert "fee" (uint256Value (depositFee wv))).insert "credited" (uint256Value (depositCredited wv))

theorem depositFee_le (wv : UInt256) (hfit : wv.toNat * 25 < UInt256.size) :
    (depositFee wv).toNat ≤ wv.toNat := by
  show (UInt256.div (UInt256.mul wv (UInt256.ofNat 25)) (UInt256.ofNat 10000)).toNat ≤ wv.toNat
  rw [udiv_toNat, u256_mul_toNat, ulit_toNat' 25 (by decide), ulit_toNat' 10000 (by decide),
    Nat.mod_eq_of_lt hfit]
  omega

/-! ### The scratch memory at pc 330 -/

/-- `mem[64] = fee`, `mem[96] = credited`, `mem[32] = caller`, `mem[0] = 1`. -/
abbrev mem307 (I : ExecutionEnv) : ByteArray :=
  (depositFee I.weiValue).toByteArray.write 0 (vyperVaultDispatchMem 9) 64 32
abbrev mem330a (I : ExecutionEnv) : ByteArray :=
  (depositCredited I.weiValue).toByteArray.write 0 (mem307 I) 96 32
abbrev mem330 (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat I.source.val).toByteArray.write 0 (mem330a I) 32 32) 0 32

theorem mem307_size (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    (mem307 I).size = 96 :=
  toByteArray_write32_size_of_ge _ _ 64 32 96 hmemsize (by omega) (lt_usize _ (by decide)) rfl

theorem mem330a_size (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    (mem330a I).size = 128 :=
  toByteArray_write32_size_of_ge _ _ 96 96 128 (mem307_size I hmemsize) (by omega) (lt_usize _ (by decide)) rfl

theorem memLoad64_mem307 (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    memLoad (UInt256.ofNat 64) (mem307 I) = depositFee I.weiValue :=
  memLoad_write_back _ _ 64 (by decide) (by rw [hmemsize]; exact lt_usize _ (by decide))

theorem memLoad96_mem330 (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    memLoad (UInt256.ofNat 96) (mem330 I) = depositCredited I.weiValue := by
  have hA := mem330a_size I hmemsize
  have hB : ((UInt256.ofNat I.source.val).toByteArray.write 0 (mem330a I) 32 32).size = 128 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hA]; omega)]
    exact hA
  rw [memLoad_above_write _ _ 0 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_above_write _ _ 32 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]
  exact memLoad_write_back _ _ 96 (by decide) (by rw [mem307_size I hmemsize]; exact lt_usize _ (by decide))

theorem memLoad64_mem330 (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    memLoad (UInt256.ofNat 64) (mem330 I) = depositFee I.weiValue := by
  have hA := mem330a_size I hmemsize
  have hB : ((UInt256.ofNat I.source.val).toByteArray.write 0 (mem330a I) 32 32).size = 128 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hA]; omega)]
    exact hA
  rw [memLoad_above_write _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_above_write _ _ 32 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_below_write _ _ 96 64 (by rw [mem307_size I hmemsize]) (by omega)
      (by rw [mem307_size I hmemsize]; exact lt_usize _ (by decide)) (by decide)]
  exact memLoad64_mem307 I hmemsize

theorem keccak_mem330 (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (mem330 I) = balSlot I := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1) (.address I.source)
    (mem := mem330a I) (by rw [mem330a_size I hmemsize]; omega)
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

/-! ### The Stele side -/

theorem evalPausedRead {σ σ₀ A I} {g : UInt256} (imms : Store) :
    evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage pausedRef) =
      .ok (wordToElem .bool (solcSlotWordAt (UInt256.ofNat 4) σ I)) := by
  have her : evalStorageRef config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) pausedRef =
      .ok { base := "paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .bool)
      (loc := vyperWordLoc (UInt256.ofNat 4) .bool) (hbase := by simp)
      (her := her) (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
    storageLocLoad_vyperWord, storageLoad_initState_ofUInt256_solcSlotWordAt]

/-- `deposit()`: the theorem `Correct.lean` routes selector 8 to. -/
theorem vyperVaultDepositBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 8) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachDepositBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some depositTransition :=
    vyperVaultDispatch_deposit (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (depositTransition.params.map Param.name)
      (transitionSignature depositTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, depositTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  have hmemsize : (vyperVaultDispatchMem 9).size = 32 := by native_decide
  rcases hwf with h0 | h1
  swap
  · -- paused: `assert not self.paused` fails
    obtain ⟨_, _, rd1⟩ := vyperVaultBlocks.vyperVault_block_36_fallthrough (by simp)
      (by rw [slotWord_eq, h1]; decide) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_44 (by simp) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_159 (by simp) rd2
    have hp : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage pausedRef) =
        .ok (.bool true) := by
      rw [evalPausedRead (σ := σ) (σ₀ := σ₀) (A := A) (g := g) imms, h1]; rfl
    refine RDrev.reEquivExecutionRevert hcode' rd3 hd hdec ?_
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_not_bool hp)))
  obtain ⟨_, _, rd1⟩ := vyperVaultBlocks.vyperVault_block_36_taken (by simp)
    (by rw [slotWord_eq, h0]; decide) (by apply D_J_contains_append_left; jump_dest) rd
  have hp : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage pausedRef) =
      .ok (.bool false) := by
    rw [evalPausedRead (σ := σ) (σ₀ := σ₀) (A := A) (g := g) imms, h0]; rfl
  have hnot : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.unary .not (.storage pausedRef)) = .ok (.bool true) := evalExpr_not_bool hp
  by_cases hwv : I.weiValue = ⟨0⟩
  · -- no value: `assert msg.value > 0` fails
    have rd2 := vyperVaultBlocks.vyperVault_block_165_fallthrough (by simp) (by rw [hwv]; rfl) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_171 (by simp) rd2
    have rd4 := vyperVaultBlocks.vyperVault_block_286 (by simp [vyperVaultBlocks.vyperVault_block_171_stack]) rd3
    refine RDrev.reEquivExecutionRevert hcode' rd4 hd hdec ?_
    rw [depositBody_eq]
    refine ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consRevert (ExecStmt.requireFalse ?_)))
    rw [evalExpr_gt_zero (evalExpr_callvalue _)]
    show EvalResult.ok (Value.bool (decide (0 < I.weiValue.toNat))) = _
    rw [hwv]; rfl
  have rd2 := vyperVaultBlocks.vyperVault_block_165_taken (by simp) (fun h => hwv h)
    (by apply D_J_contains_append_left; jump_dest) rd1
  have hpos : 0 < I.weiValue.toNat := by
    by_contra h
    exact hwv (uint256_toNat_eq_zero (by omega))
  have hgt : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
    rw [evalExpr_gt_zero (evalExpr_callvalue _)]
    show EvalResult.ok (Value.bool (decide (0 < I.weiValue.toNat))) = _
    rw [decide_eq_true hpos]
  -- the fee
  by_cases hfit1 : I.weiValue.toNat * 25 < UInt256.size
  swap
  · -- `msg.value * 25` overflows
    have rd3 := vyperVaultBlocks.vyperVault_block_292_taken (by simp)
      (u256_xor_ne_zero_of_ne (u256_mul_div_right_overflow_ne _ _ (by rw [ulit_toNat' 25 (by decide)]; omega)))
      (by apply D_J_contains_append_left; jump_dest) rd2
    have rd4 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_292_taken_stack]) rd3
    refine RDrev.reEquivExecutionRevert hcode' rd4 hd hdec ?_
    rw [depositBody_eq]
    refine ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt) (ExecBlock.consRevert (ExecStmt.letDeclRevert ?_))))
    exact evalExpr_binary_revert_left (by decide) (by decide)
      (evalExpr_uint256_mul_overflow (evalExpr_callvalue _) (evalExpr_intLit_word _ 25 (by decide))
        (by show UInt256.size ≤ I.weiValue.toNat * (UInt256.ofNat 25).toNat; rw [ulit_toNat' 25 (by decide)]; omega))
  have rd3 := vyperVaultBlocks.vyperVault_block_292_fallthrough (by simp)
    (by
      rw [u256_mul_div_right_eq_of_noOverflow _ _ (by decide) (by rw [ulit_toNat' 25 (by decide)]; exact hfit1),
        u256_xor_self]
      rfl) rd2
  simp only [vyperVaultBlocks.vyperVault_block_292_fallthrough_stack] at rd3
  have hfee_le := depositFee_le I.weiValue hfit1
  -- pc 307: fee to memory, credited = value - fee (never underflows)
  have rd4 := vyperVaultBlocks.vyperVault_block_307_fallthrough (by simp)
    (by
      rw [ulit_toNat' 64 (by decide), memLoad64_mem307 I hmemsize]
      exact ugt_zero (by rw [usub_toNat hfee_le]; omega)) rd3
  simp only [vyperVaultBlocks.vyperVault_block_307_fallthrough_stack,
    vyperVaultBlocks.vyperVault_block_307_fallthrough_memory, ulit_toNat' 64 (by decide),
    memLoad64_mem307 I hmemsize] at rd4
  -- Stele: the two `let`s
  have hfeeEval : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) feeExpr =
      .ok (uint256Value (depositFee I.weiValue)) :=
    evalExpr_uint256_div
      (evalExpr_uint256_mul (evalExpr_callvalue _) (evalExpr_intLit_word _ 25 (by decide))
        (by show I.weiValue.toNat * (UInt256.ofNat 25).toNat < UInt256.size; rw [ulit_toNat' 25 (by decide)]; exact hfit1))
      (evalExpr_intLit_word _ 10000 (by decide)) (by decide)
  have hcredEval : evalExpr? config (frame imms ((∅ : Store).insert "fee" (uint256Value (depositFee I.weiValue))))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) creditedExpr = .ok (uint256Value (depositCredited I.weiValue)) :=
    evalExpr_uint256_sub (evalExpr_callvalue _) (evalVar imms _ _ "fee" _ (store_get_self _ _ _)) hfee_le
  -- Stele: the first assignment's operands
  have her1 : evalStorageRef config (frame imms (depositLocals I.weiValue)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      balRef = .ok { base := "balances", steps := [.mindex (.address I.source)] } := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
      EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue, initState]
  have hbalRead : evalExpr? config (frame imms (depositLocals I.weiValue)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage balRef) = .ok (uint256Value (solcSlotWordAt (balSlot I) σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (physicalSlot := balSlot I) (hbase := by simp) (her := her1)
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
        (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hcredVar : ∀ evm, evalExpr? config (frame imms (depositLocals I.weiValue)) evm
      (.var "credited") = .ok (uint256Value (depositCredited I.weiValue)) := fun evm =>
    evalVar imms _ _ "credited" _ (store_get_self _ _ _)
  have hfeeVar : ∀ evm, evalExpr? config (frame imms (depositLocals I.weiValue)) evm
      (.var "fee") = .ok (uint256Value (depositFee I.weiValue)) := fun evm =>
    evalVar imms _ _ "fee" _ (by rw [store_get_ne _ _ (by decide), store_get_self])
  -- pc 330: the mapping slot, the current balance, the overflow check
  have hkec := keccak_mem330 I hmemsize
  have hm96 := memLoad96_mem330 I hmemsize
  have hm64 := memLoad64_mem330 I hmemsize
  by_cases hfit2 : (solcSlotWordAt (balSlot I) σ I).toNat + (depositCredited I.weiValue).toNat < UInt256.size
  swap
  · -- `balances[msg.sender] + credited` overflows
    obtain ⟨_, _, rd5⟩ := vyperVaultBlocks.vyperVault_block_330_taken (by simp)
      (by
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide)]
        rw [hkec, hm96, slotWord_eq,
          u256_add_overflow_lt (solcSlotWordAt (balSlot I) σ I) (depositCredited I.weiValue) (by omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd4
    have rd6 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_330_taken_stack]) rd5
    refine RDrev.reEquivExecutionRevert hcode' rd6 hd hdec ?_
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt)
        (ExecBlock.consNormal (ExecStmt.letDecl hfeeEval)
          (ExecBlock.consNormal (ExecStmt.letDecl hcredEval)
            (ExecBlock.consRevert (ExecStmt.assignExprRevert
              (evalExpr_uint256_add_overflow hbalRead (hcredVar _) (by omega))))))))
  obtain ⟨_, _, rd5⟩ := vyperVaultBlocks.vyperVault_block_330_fallthrough (by simp)
    (by
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide)]
      rw [hkec, hm96, slotWord_eq]
      exact ult_zero (by rw [uadd_toNat, Nat.mod_eq_of_lt hfit2]; omega)) rd4
  simp only [vyperVaultBlocks.vyperVault_block_330_fallthrough_stack,
    vyperVaultBlocks.vyperVault_block_330_fallthrough_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide)] at rd5
  rw [hkec, hm96, slotWord_eq] at rd5
  -- Stele: the first assignment
  have hadd1 := evalExpr_uint256_add hbalRead (hcredVar _) hfit2
  have hassign1 : assignStorageRef? config (frame imms (depositLocals I.weiValue))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage balRef
      (uint256Value (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue)) =
      .ok (frame imms (depositLocals I.weiValue),
        Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
          (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue)) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "balances", steps := [.mindex (.address I.source)] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (balSlot I))
      (hbase := by simp) (her := her1)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax]) (hloc := rfl)
    erw [storageLocStore_uint256]
  -- the state after the first store, and the `totalDeposits` read from it
  have htd : evalExpr? config (frame imms (depositLocals I.weiValue))
      (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
        (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
      (.storage tdRef) = .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "totalDeposits", steps := [] })
        (physicalSlot := UInt256.ofNat 2) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_accountMap]
    rfl
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the first `SSTORE` (pc 367) halts
    have hpf : I.perm = false := by simpa using hperm
    have r1 := rd5.swap1
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨362⟩ : UInt256), .SWAP1, none))
      (by evm_ov)
    have r2 := r1.pop
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨363⟩ : UInt256), .POP, none))
      (by evm_ov)
    have r3 := r2.swap1
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨364⟩ : UInt256), .SWAP1, none))
      (by evm_ov)
    have r4 := r3.pop
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨365⟩ : UInt256), .POP, none))
      (by evm_ov)
    have r5 := r4.dup2
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨366⟩ : UInt256), .DUP2, none))
      (by evm_ov)
    have rs := r5.sstoreStatic hpf
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨367⟩ : UInt256), .SSTORE, none))
      (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt)
        (ExecBlock.consNormal (ExecStmt.letDecl hfeeEval)
          (ExecBlock.consNormal (ExecStmt.letDecl hcredEval)
            (ExecBlock.consStatic (ExecStmt.assignStatic hadd1 hassign1 (by show I.perm = false; exact hpf)))))))
  -- pc 362: store the balance, read `totalDeposits`, check the addition
  by_cases hfit3 : (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I).toNat + (depositCredited I.weiValue).toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd6⟩ := vyperVaultBlocks.vyperVault_block_362_taken (by simp) hperm
      (by
        rw [hm96, slotWord_eq,
          u256_add_overflow_lt (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I) (depositCredited I.weiValue) (by omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd5
    have rd7 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_362_taken_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode' rd7 hd hdec ?_
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt)
        (ExecBlock.consNormal (ExecStmt.letDecl hfeeEval)
          (ExecBlock.consNormal (ExecStmt.letDecl hcredEval)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd1 hassign1)
              (ExecBlock.consRevert (ExecStmt.assignExprRevert
                (evalExpr_uint256_add_overflow htd (hcredVar _) (by omega)))))))))
  obtain ⟨_, _, rd6⟩ := vyperVaultBlocks.vyperVault_block_362_fallthrough (by simp) hperm
    (by
      rw [hm96, slotWord_eq]
      exact ult_zero (by
        show (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I).toNat ≤
          (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue).toNat
        rw [uadd_toNat, Nat.mod_eq_of_lt hfit3]; omega)) rd5
  simp only [vyperVaultBlocks.vyperVault_block_362_fallthrough_stack] at rd6
  rw [hm96, slotWord_eq] at rd6
  -- Stele: the second assignment
  have hadd2 := evalExpr_uint256_add htd (hcredVar _) hfit3
  have hassign2 : assignStorageRef? config (frame imms (depositLocals I.weiValue))
      (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
        (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
      .storage tdRef (uint256Value (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue)) =
      .ok (frame imms (depositLocals I.weiValue),
        Stele.EVM.storageStore
          (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
            (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
          I.codeOwner (UInt256.ofNat 2)
          (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue)) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalDeposits", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 2))
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv]
    rfl
  -- the `feesCollected` read after two stores
  have hfc : evalExpr? config (frame imms (depositLocals I.weiValue))
      (Stele.EVM.storageStore
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
          (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
        I.codeOwner (UInt256.ofNat 2)
        (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue))
      (.storage fcRef) = .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "feesCollected", steps := [] })
        (physicalSlot := UInt256.ofNat 3) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_executionEnv,
      storageStore_accountMap, storageStore_accountMap]
    rfl
  -- pc 385: store `totalDeposits`, read `feesCollected`, check the addition
  by_cases hfit4 : (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I).toNat + (depositFee I.weiValue).toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd7⟩ := vyperVaultBlocks.vyperVault_block_385_taken (by simp) hperm
      (by
        rw [hm64, slotWord_eq,
          u256_add_overflow_lt (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I) (depositFee I.weiValue) (by omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd6
    have rd8 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_385_taken_stack]) rd7
    refine RDrev.reEquivExecutionRevert hcode' rd8 hd hdec ?_
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt)
        (ExecBlock.consNormal (ExecStmt.letDecl hfeeEval)
          (ExecBlock.consNormal (ExecStmt.letDecl hcredEval)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd1 hassign1)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd2 hassign2)
                (ExecBlock.consRevert (ExecStmt.assignExprRevert
                  (evalExpr_uint256_add_overflow hfc (hfeeVar _) (by omega))))))))))
  obtain ⟨_, _, rd7⟩ := vyperVaultBlocks.vyperVault_block_385_fallthrough (by simp) hperm
    (by
      rw [hm64, slotWord_eq]
      exact ult_zero (by
        show (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I).toNat ≤
          (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue).toNat
        rw [uadd_toNat, Nat.mod_eq_of_lt hfit4]; omega)) rd6
  simp only [vyperVaultBlocks.vyperVault_block_385_fallthrough_stack] at rd7
  rw [hm64, slotWord_eq] at rd7
  -- pc 408: store `feesCollected`, log, stop
  have rd8 := vyperVaultBlocks.vyperVault_block_408 (by simp) hperm rd7
  -- Stele: the third assignment and the log
  have hadd3 := evalExpr_uint256_add hfc (hfeeVar _) hfit4
  have hassign3 : assignStorageRef? config (frame imms (depositLocals I.weiValue))
      (Stele.EVM.storageStore
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
          (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
        I.codeOwner (UInt256.ofNat 2)
        (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue))
      .storage fcRef (uint256Value (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue)) =
      .ok (frame imms (depositLocals I.weiValue),
        Stele.EVM.storageStore
          (Stele.EVM.storageStore
            (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
              (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
            I.codeOwner (UInt256.ofNat 2)
            (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue))
          I.codeOwner (UInt256.ofNat 3)
          (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue)) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "feesCollected", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 3))
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv, storageStore_executionEnv]
    rfl
  have hemit : evalExprs? config (frame imms (depositLocals I.weiValue))
      (Stele.EVM.storageStore
        (Stele.EVM.storageStore
          (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
            (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
          I.codeOwner (UInt256.ofNat 2)
          (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue))
        I.codeOwner (UInt256.ofNat 3)
        (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue))
      [.env .caller, .var "credited"] = .ok [.address I.source, uint256Value (depositCredited I.weiValue)] := by
    rw [evalExprs?, evalExpr_caller, evalExprs?, evalVar imms _ _ "credited" _ (store_get_self _ _ _), evalExprs?]
    simp only [storageStore_executionEnv, EvalResult.bind, bind, pure]
    rfl
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      depositTransition.body
      (.returned (frame imms (depositLocals I.weiValue))
        (Stele.EVM.storageStore
          (Stele.EVM.storageStore
            (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (balSlot I)
              (solcSlotWordAt (balSlot I) σ I + depositCredited I.weiValue))
            I.codeOwner (UInt256.ofNat 2)
            (solcSlotWordAt (UInt256.ofNat 2) (σ1 σ I) I + depositCredited I.weiValue))
          I.codeOwner (UInt256.ofNat 3)
          (solcSlotWordAt (UInt256.ofNat 3) (σ2 σ I) I + depositFee I.weiValue)) none)
      (restrictImmutables contract imms) := by
    rw [depositBody_eq]
    exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hnot)
      (ExecBlock.consNormal (ExecStmt.requireTrue hgt)
        (ExecBlock.consNormal (ExecStmt.letDecl hfeeEval)
          (ExecBlock.consNormal (ExecStmt.letDecl hcredEval)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd1 hassign1)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd2 hassign2)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hadd3 hassign3)
                  (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [storageStore_executionEnv, initState] using hperm) hemit) ExecBlock.nil))))))))
  exact rd8.reEquivExecutionGen hcode' hd hdec hbody
    (by rw [storageStore_accountMap, storageStore_accountMap, storageStore_accountMap]; rfl)
    (returnEquiv.fallthrough rfl rfl (by native_decide))

end Tests.Pipeline.VyperVault
