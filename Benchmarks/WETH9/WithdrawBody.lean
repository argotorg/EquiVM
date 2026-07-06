import Benchmarks.WETH9.Deposit
import Reasoning.ExternalCall

/-!
# WETH9 `withdraw(uint256)` — body helper lemmas

`withdraw` is the hardest WETH9 function: it decrements `balanceOf[msg.sender]` by `wad` and makes an
external value-transfer `CALL` (`msg.sender.transfer(wad)` in the source, modeled as a `.lowLevelCall`
with `require(success)`).  This file carries the EVM trace and the Solm body-execution facts; the
top-level refinement `weth9WithdrawBodyCore` lives in `Withdraw.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## The wrapping subtraction store word -/

/-- `wordOfInt (a - b) = a ⊖ b` when `b ≤ a` (the unchecked `-=` on store; `require(bal≥wad)` rules
    out underflow). -/
theorem wordOfInt_sub_words (a b : UInt256) (hle : b.toNat ≤ a.toNat) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  rw [show (Int.ofNat a.toNat - Int.ofNat b.toNat) = Int.ofNat (a.toNat - b.toNat) from
      (Nat.cast_sub hle).symm, wordOfInt_ofNat_toNat_gen]
  apply u256_inj
  rw [usub_toNat hle]
  exact ulit_toNat' _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt)

/-! ## Argument / store definitions -/

/-- The decoded `wad` argument word. -/
abbrev withdrawWadWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

/-- The `wad` callargs store. -/
abbrev withdrawStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "wad" (.int (Int.ofNat (withdrawWadWord I).toNat))

/-! ## Dispatch and decode -/

theorem weth9SelectorDispatchWithdraw {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 4)) :
    selectorDispatchMsg contract I.calldata = some withdrawTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes]
  native_decide

/-- Legacy (solc 0.5) single-`uint256` calldata decode succeeds for any `size ≥ 36` — including huge
    calldata (`≥ 2^255`), matching the runtime's **unsigned** `LT` length guard. -/
theorem decodeCalldata_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05) (start := 0)
    (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem weth9Decode_withdraw_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some (withdrawStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["wad"] [uint256] I.calldata = _
  simpa [withdrawStore, withdrawWadWord] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "wad") hsz36

theorem weth9Decode_withdraw_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["wad"] [uint256] I.calldata = none
  simpa using decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "wad") hsz4 hshort

/-! ## Solm body execution

The Solm `withdraw` body is
`require(msg.value==0); require(balanceOf[caller] ≥ wad); balanceOf[caller] -= wad;
 (success,_data)=caller.call{value:wad}(""); require(success)`.
The store state after the `-=` and the post-call locals. -/

/-- The `evm` state after `balanceOf[caller] -= wad` (unchecked wrapping store). -/
def withdrawStoreState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (callerBalSlot I)
    (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I))
      (withdrawWadWord I))

/-- Post-call locals: `wad`, `success`, `_data`. -/
def withdrawCallStore (I : ExecutionEnv) (z : Bool) (out : ByteArray) : Store :=
  ((withdrawStore I).insert "success" (.bool z)).insert "_data" (.bytes out)

theorem withdrawStore_wad_get (I : ExecutionEnv) :
    (withdrawStore I).get? "wad" = some (.int (Int.ofNat (withdrawWadWord I).toNat)) :=
  store_get_self _ _ _

theorem withdrawStore_balanceOf_get (I : ExecutionEnv) :
    (withdrawStore I).get? "balanceOf" = none := by
  rw [store_get_ne (a := "balanceOf") _ _ (by decide)]; simp

theorem withdrawCallStore_success_get (I : ExecutionEnv) (z : Bool) (out : ByteArray) :
    (withdrawCallStore I z out)["success"]? = some (.bool z) := by
  change (withdrawCallStore I z out).get? "success" = some (.bool z)
  unfold withdrawCallStore
  rw [store_get_ne (a := "success") _ _ (by decide)]
  exact store_get_self _ _ _

/-- `sender` evaluates to `msg.sender` (unchanged by the store). -/
theorem evalWithdrawSender (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

/-- `emptyBytes` (`new bytes(0)`) evaluates to the empty byte array. -/
theorem evalWithdrawEmptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm emptyBytes =
      .ok (.bytes ByteArray.empty) := by
  simp [emptyBytes, evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem evalWithdrawWadVar (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := withdrawStore I } evm (.var "wad") =
      .ok (.int (Int.ofNat (withdrawWadWord I).toNat)) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawStore]

theorem evalWithdrawSuccess (evm : EVM.State) (I : ExecutionEnv) (z : Bool) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := withdrawCallStore I z out } evm
      (.var "success") = .ok (.bool z) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, withdrawCallStore_success_get]

/-- `require(balanceOf[caller] ≥ wad)` evaluates to `true` when `wad ≤ bal`. -/
theorem evalWithdrawGe_true (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hle : (withdrawWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat) :
    evalExpr? config { contract := contract, locals := withdrawStore I } evm
      (.binary .ge (.storage (balanceOfRef sender)) (.var "wad")) = .ok (.bool true) := by
  simp only [evalExpr?, evalCallerBal evm I (withdrawStore I) hsrc (withdrawStore_balanceOf_get I),
    withdrawStore_wad_get, EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?,
    EvalResult.ok.injEq, Value.bool.injEq, decide_eq_true_eq]
  exact Int.ofNat_le.mpr hle

/-- `require(balanceOf[caller] ≥ wad)` evaluates to `false` when `bal < wad`. -/
theorem evalWithdrawGe_false (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hlt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat <
      (withdrawWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := withdrawStore I } evm
      (.binary .ge (.storage (balanceOfRef sender)) (.var "wad")) = .ok (.bool false) := by
  simp only [evalExpr?, evalCallerBal evm I (withdrawStore I) hsrc (withdrawStore_balanceOf_get I),
    withdrawStore_wad_get, EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?,
    EvalResult.ok.injEq, Value.bool.injEq, decide_eq_false_iff_not]
  exact fun h => absurd (Int.ofNat_le.mp h) (by omega)

/-- `balanceOf[caller] - wad` (as an unbounded `Int`). -/
theorem evalWithdrawSub (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := withdrawStore I } evm
      (.binary .sub (.storage (balanceOfRef sender)) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat - Int.ofNat (withdrawWadWord I).toNat)) := by
  simp only [evalExpr?, evalCallerBal evm I (withdrawStore I) hsrc (withdrawStore_balanceOf_get I),
    withdrawStore_wad_get, EvalResult.bind, EvalResult.ofOption, bind, pure, evalBinaryOp?]

/-- The `balanceOf[caller] -= wad` assignment, given no underflow (`wad ≤ bal`). -/
theorem withdrawAssign (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hle : (withdrawWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat) :
    assignStorageRef? config { contract := contract, locals := withdrawStore I } evm
      .storage (balanceOfRef sender)
      (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat - Int.ofNat (withdrawWadWord I).toNat)) =
      .ok ({ contract := contract, locals := withdrawStore I }, withdrawStoreState evm I) := by
  refine assignStorageRef_storage_scalar_value
    (er := callerBalRef I) (ty := uint256St) (loc := wordLoc (callerBalSlot I))
    (hbase := by simp [balanceOfRef, withdrawStore_balanceOf_get I]) ?_ ?_ (by rfl) (by trivial) ?_
  · simp only [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · unfold withdrawStoreState
    rw [show wordLoc (callerBalSlot I) = uint256Loc (callerBalSlot I) from rfl,
      storageLocStore_uint256_int, wordOfInt_sub_words _ _ hle]

/-- Body execution, `bal < wad` branch: `require(balanceOf[caller] ≥ wad)` reverts. -/
theorem weth9WithdrawBodyReverts_geFalse (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv = I) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat <
      (withdrawWadWord I).toNat) :
    ExecTransitionBody config contract evm (withdrawStore I) withdrawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalWithdrawGe_false evm I hsrc hlt))

/-- Body execution, `bal ≥ wad`, call succeeds: `require(success)` passes, body returns (void). -/
theorem weth9WithdrawBodyReturns_success (evm evm' : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsrc : evm.executionEnv = I) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hle : (withdrawWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat)
    (hcall : callViaEVM (withdrawStoreState evm I)
      (EVM.address (withdrawStoreState evm I).executionEnv.source)
      (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (true, evm', out)) :
    ExecTransitionBody config contract evm (withdrawStore I) withdrawTransition.body
      (.returned { contract := contract, locals := withdrawCallStore I true out } evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalWithdrawGe_true evm I hsrc hle)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalWithdrawSub evm I hsrc) (withdrawAssign evm I hsrc hle)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalWithdrawSender (withdrawStoreState evm I) (withdrawStore I))
      (evalWithdrawWadVar (withdrawStoreState evm I) I)
      (evalWithdrawEmptyBytes (withdrawStoreState evm I) (withdrawStore I)) hcall) ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalWithdrawSuccess evm' I true out))
    ExecBlock.nil

/-- Body execution, `bal ≥ wad`, call fails: `require(success)` reverts. -/
theorem weth9WithdrawBodyReverts_callFailure (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsrc : evm.executionEnv = I) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hle : (withdrawWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat)
    (hcall : callViaEVM (withdrawStoreState evm I)
      (EVM.address (withdrawStoreState evm I).executionEnv.source)
      (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (false, evm', out)) :
    ExecTransitionBody config contract evm (withdrawStore I) withdrawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold withdrawTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalWithdrawGe_true evm I hsrc hle)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalWithdrawSub evm I hsrc) (withdrawAssign evm I hsrc hle)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalWithdrawSender (withdrawStoreState evm I) (withdrawStore I))
      (evalWithdrawWadVar (withdrawStoreState evm I) I)
      (evalWithdrawEmptyBytes (withdrawStoreState evm I) (withdrawStore I)) hcall) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalWithdrawSuccess evm' I false out))

/-! ## EVM trace: dispatch → guard → decode → body entry (pc 1395) -/

/-- `callvalue ≠ 0`: the withdraw callvalue guard reverts. -/
theorem weth9WithdrawGuardRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 4)) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h487⟩ := weth9ReachWithdraw (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  exact weth9GuardPeelRev (gt := ⟨499⟩) h487 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- `callvalue = 0`, `size < 36`: the ABI length guard reverts. -/
theorem weth9WithdrawDecodeRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 4)) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h487⟩ := weth9ReachWithdraw (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h501⟩ := weth9GuardPeelOk (gt := ⟨499⟩) h487 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hltShort : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
      hsize]
    simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      show (⟨4⟩ : UInt256).toNat = 4 from rfl]; omega
  exact h501.push2 ⟨164⟩ (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨32⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.push2 ⟨522⟩ (by native_decide) (by simp)
    |>.jumpiNT (by native_decide) (by rw [hltShort]; decide) (by simp)
    |>.uniswapPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)

/-- `callvalue = 0`, `size ≥ 36`: reach the body entry (pc 1395) with `[wad, 164, sel]`. -/
theorem weth9WithdrawReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 4)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h487⟩ := weth9ReachWithdraw (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode (by omega) hsize hsel
  obtain ⟨_, _, h501⟩ := weth9GuardPeelOk (gt := ⟨499⟩) h487 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize
  have h1395 := h501.push2 ⟨164⟩ (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨32⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.push2 ⟨522⟩ (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
    |>.jumpdest (by native_decide) (by simp)
    |>.pop (by native_decide) (by simp)
    |>.calldataload (by native_decide) (by simp)
    |>.push2 ⟨1395⟩ (by native_decide) (by simp)
    |>.jump (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [withdrawWadWord, calldataWord] using h1395⟩

/-! ## EVM trace: `require(balanceOf ≥ wad)` check + `balanceOf -= wad` store -/

/-- The caller-keyed keccak of `caller ‖ 3` on the first-segment memory. -/
theorem withdrawKeccak1 (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem).readWithPadding 0 64)))
      = callerBalSlot I := by
  rw [twoWordHashMem_solcMappingSlot ⟨3⟩ (solcSourceWord I) solcFreePtrMem_size]
  exact (callerBalSlot_eq I).symm

/-- The caller-keyed keccak of `caller ‖ 3` on the second-segment (re-hashed) memory. -/
theorem withdrawKeccak2 (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (solcSourceWord I) ⟨3⟩
          (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem)).readWithPadding 0 64)))
      = callerBalSlot I := by
  rw [twoWordHashMem_solcMappingSlot ⟨3⟩ (solcSourceWord I)
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)]
  exact (callerBalSlot_eq I).symm

/-- Require-check segment (pc 1395→1415): keccak `balanceOf[caller]` slot, `SLOAD`, `wad > bal`,
    `ISZERO`.  The top of stack is `¬(wad > bal)` = `bal ≥ wad`. -/
theorem weth9WithdrawRequireCheck {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1415⟩
      [UInt256.isZero (UInt256.gt (withdrawWadWord I) (solcSlotWord σ I (callerBalSlot I))),
        withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hA := evm_run h with [
    jumpdest, caller, push1 ⟨0⟩, swap1, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨3⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (callerBalSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (withdrawKeccak1 I) (by native_decide) (by evm_ov)]
  obtain ⟨_, _, hSload⟩ := hA.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run hSload with [dup2, gt, iszero]⟩

/-- `bal < wad`: `require(balanceOf ≥ wad)` reverts at pc 1419. -/
theorem weth9WithdrawRequireRev {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hlt : (solcSlotWord σ I (callerBalSlot I)).toNat < (withdrawWadWord I).toNat)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h1415⟩ := weth9WithdrawRequireCheck h
  have hgt : UInt256.gt (withdrawWadWord I) (solcSlotWord σ I (callerBalSlot I)) = ⟨1⟩ :=
    ugt_one (by omega)
  exact h1415.push2 ⟨1423⟩ (by native_decide) (by simp)
    |>.jumpiNT (by native_decide) (by rw [hgt]; decide) (by simp)
    |>.uniswapPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)

/-- `bal ≥ wad`: pass the require, re-keccak, `balanceOf[caller] -= wad` (`SSTORE`), reaching the
    `CALL` setup (pc 1447) with the mapping-hash memory and the decremented balance. -/
theorem weth9WithdrawReachStore {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1447⟩
      [⟨64⟩, ⟨0⟩, solcSourceWord I, withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      (twoWordHashMem (solcSourceWord I) ⟨3⟩ (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (callerBalSlot I)
        (UInt256.sub (solcSlotWord σ I (callerBalSlot I)) (withdrawWadWord I))) k' C' := by
  obtain ⟨_, _, h1415⟩ := weth9WithdrawRequireCheck h
  have h1423 := h1415.push2 ⟨1423⟩ (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (by rw [ugt_zero hle]; decide) (by jump_dest) (by simp)
    |>.jumpdest (by native_decide) (by simp)
  have hC := evm_run h1423 with [
    caller, push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem (solcSourceWord I)
        (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨3⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (solcSourceWord I) ⟨3⟩
        (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup3,
    raw keccak256 0 (callerBalSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (withdrawKeccak2 I) (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, hSload2⟩ := hC.sload (by native_decide) (by evm_ov)
  have hD := evm_run hSload2 with [dup6, swap1, sub, swap1]
  obtain ⟨_, _, hSstore⟩ := hD.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, hSstore⟩

/-! ## EVM trace: `CALL` setup (pc 1447 → 1464) -/

/-- The mapping-hash store memory (mem after the two keccak stores). -/
noncomputable def withdrawStoreMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨3⟩ (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem)

theorem withdrawStoreMem_size (I : ExecutionEnv) : (withdrawStoreMem I).size = 96 :=
  twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)

theorem withdrawStoreMem_read64 (I : ExecutionEnv) :
    (withdrawStoreMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)

theorem withdrawStoreMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawStoreMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((withdrawStoreMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [withdrawStoreMem_size]; decide) (by decide) (withdrawStoreMem_read64 I)

/-- The `transfer` gas stipend word `2300 · iszero(wad)` the solc `call{value}` pattern forwards. -/
abbrev withdrawGasArg (I : ExecutionEnv) : UInt256 :=
  UInt256.mul ⟨2300⟩ (UInt256.isZero (withdrawWadWord I))

/-- The post-store accountMap: `balanceOf[caller]` decremented by `wad`. -/
abbrev withdrawStoreMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (callerBalSlot I)
    (UInt256.sub (solcSlotWord σ I (callerBalSlot I)) (withdrawWadWord I))

/-- `bal ≥ wad`: reach the value-transfer `CALL` (pc 1464) with its seven arguments assembled. -/
theorem weth9WithdrawToCall {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1464⟩
      [withdrawGasArg I, solcSourceWord I, withdrawWadWord I, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        withdrawWadWord I, withdrawGasArg I, solcSourceWord I, withdrawWadWord I, ⟨164⟩,
        weth9SelWord I]
      (withdrawStoreMem I) (UInt256.ofNat 3) ByteArray.empty (cA, withdrawStoreMap σ I) k' C' := by
  obtain ⟨_, _, h1447⟩ := weth9WithdrawReachStore hperm hle h
  exact ⟨_, _, evm_run h1447 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost (withdrawStoreMem_mload64 I)
      (by native_decide) (by evm_ov),
    dup4, iszero, push2 ⟨2300⟩, mul, swap2, dup5, swap2, swap1, dup2, dup2, dup2, dup6, dup9, dup9]⟩

/-! ## EVM trace: post-`CALL` cleanup + success/failure tails -/

/-- Post-`CALL` stack cleanup (pc 1465→1470): drop the four scratch words, leaving `[status]`. -/
theorem weth9WithdrawAfterCall {cA gh bl σ σ₀ A I} {g : Sat256} {zw : UInt256}
    {mem o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1465⟩
      [zw, ⟨128⟩, withdrawWadWord I, withdrawGasArg I, solcSourceWord I, withdrawWadWord I, ⟨164⟩,
        weth9SelWord I]
      mem (UInt256.ofNat 3) o acc k C) :
    ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1470⟩
      [zw, withdrawWadWord I, ⟨164⟩, weth9SelWord I] mem (UInt256.ofNat 3) o acc k' C' := by
  exact ⟨_, _, evm_run h with [swap4, pop, pop, pop, pop]⟩

/-- Call failed (`status = 0`): bubble up the callee's revert (`RETURNDATACOPY` + `REVERT`). -/
theorem weth9WithdrawFailureTail {cA gh bl σ σ₀ A I} {g : Sat256} {mem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hoSize : o.size < UInt256.size)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1470⟩
      [⟨0⟩, withdrawWadWord I, ⟨164⟩, weth9SelWord I] mem (UInt256.ofNat 3) o acc k C) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hrdstoNat : (UInt256.ofNat o.size).toNat = o.size := UInt256.toNat_ofNat_of_lt hoSize
  have h1481 := evm_run h with [
    iszero, dup1, iszero, push2 ⟨1486⟩, jumpiNT (by decide),
    returndatasize, push1 ⟨0⟩, dup1]
  have h1482 := RD.returndatacopy
    (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 0 (UInt256.ofNat o.size).toNat))
      - Cₘ (UInt256.ofNat 3))
    (o.write 0 mem 0 (UInt256.ofNat o.size).toNat)
    (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 0 (UInt256.ofNat o.size).toNat))
    h1481 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdstoNat]; omega)
    (by intro s haw hstk; simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by rfl) (by rfl) (by evm_ov)
  have h1483 := evm_run h1482 with [returndatasize, push1 ⟨0⟩]
  exact RD.rev _ h1483 (by native_decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws]) (by evm_ov)

/-- The `Withdrawal(caller, wad)` log-data memory (`wad` stored at the free pointer 0x80). -/
noncomputable def withdrawLogMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (withdrawWadWord I)).write 0 (withdrawStoreMem I) 128 32

theorem withdrawLogMem_read64 (I : ExecutionEnv) :
    (withdrawLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hthmsize : (withdrawStoreMem I).size = 96 := withdrawStoreMem_size I
  have hgap32 : (128 : ℕ) - (withdrawStoreMem I).size = 32 := by rw [hthmsize]
  have hgapeq : withdrawLogMem I = withdrawStoreMem I ++ ffi.ByteArray.zeroes (USize.ofNat 32)
      ++ UInt256.toByteArray (withdrawWadWord I) := by
    rw [withdrawLogMem, toByteArray_write_eq _ _ _ (by rw [hthmsize]; omega)
      (by rw [hgap32]; exact lt_usize 32 (by norm_num)), hgap32]
  have hzsize : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' (lt_usize 32 (by norm_num))]
  have hcvsize : (UInt256.toByteArray (withdrawWadWord I)).size = 32 :=
    (UInt256.toByteArrayWithSizeProof (withdrawWadWord I)).2
  have h1 : (withdrawLogMem I).readWithPadding 64 32 = (withdrawLogMem I).extract 64 (64 + 32) :=
    readWithPadding_eq_extract _ 64 (by
      rw [hgapeq, ByteArray.size_append, ByteArray.size_append, hthmsize, hzsize, hcvsize]; omega)
  have h2 : (64 : ℕ) + 32 ≤ (withdrawStoreMem I ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size := by
    rw [ByteArray.size_append, hthmsize, hzsize]; omega
  have h3 : (64 : ℕ) + 32 ≤ (withdrawStoreMem I).size := by rw [hthmsize]
  rw [h1, hgapeq, extract_append_left _ _ 64 (64 + 32) h2, extract_append_left _ _ 64 (64 + 32) h3,
    ← readWithPadding_eq_extract (withdrawStoreMem I) 64 h3, withdrawStoreMem_read64]

theorem withdrawLogMem_size (I : ExecutionEnv) : (withdrawLogMem I).size = 160 := by
  have hthmsize : (withdrawStoreMem I).size = 96 := withdrawStoreMem_size I
  have hgap32 : (128 : ℕ) - (withdrawStoreMem I).size = 32 := by rw [hthmsize]
  have hgapeq : withdrawLogMem I = withdrawStoreMem I ++ ffi.ByteArray.zeroes (USize.ofNat 32)
      ++ UInt256.toByteArray (withdrawWadWord I) := by
    rw [withdrawLogMem, toByteArray_write_eq _ _ _ (by rw [hthmsize]; omega)
      (by rw [hgap32]; exact lt_usize 32 (by norm_num)), hgap32]
  have hzsize : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' (lt_usize 32 (by norm_num))]
  have hcvsize : (UInt256.toByteArray (withdrawWadWord I)).size = 32 :=
    (UInt256.toByteArrayWithSizeProof (withdrawWadWord I)).2
  rw [hgapeq, ByteArray.size_append, ByteArray.size_append, hthmsize, hzsize, hcvsize]

theorem withdrawLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((withdrawLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  rw [if_neg (by rw [withdrawLogMem_size]; decide),
    show (⟨64⟩ : UInt256).toNat = 64 from rfl, withdrawLogMem_read64]
  native_decide

/-- Call succeeded (`status = 1`): store `wad`, emit the `Withdrawal` `LOG2`, and `STOP`. -/
theorem weth9WithdrawSuccessTail {cA gh bl σ σ₀ A I} {g : Sat256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1470⟩
      [⟨1⟩, withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      (withdrawStoreMem I) (UInt256.ofNat 3) o acc k C) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have hpermI : (initState cA gh bl σ σ₀ g A I).executionEnv.perm = true := by
    simp [initState]; exact hperm
  have hA := evm_run h with [
    iszero, dup1, iszero, push2 ⟨1486⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost (withdrawStoreMem_mload64 I)
      (by native_decide) (by evm_ov),
    dup3, dup2,
    raw mstore 6 (withdrawLogMem I) (UInt256.ofNat 5) (by native_decide) mem_cost
      (by unfold withdrawLogMem; rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
      (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (withdrawLogMem_mload64 I)
      (by native_decide) (by evm_ov),
    caller, swap2]
  have hB := hA.pushConst
    (⟨57810043145978950376228313794938171962422655018555593468903716172405399886693⟩ : UInt256)
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have h1541 := evm_run hB with [swap2, swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1]
  have h1542 := RD.log2 0 (UInt256.ofNat 5) h1541 (by native_decide) hpermI mem_cost
    (by native_decide) (by evm_ov)
  exact (h1542.pop (by native_decide) (by evm_ov)).jump (by native_decide) (by jump_dest)
      (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.stop (by native_decide) (by evm_ov)

/-! ## EVM trace: the three `CALL` outcomes -/

/-- `bal ≥ wad`, depth limit reached (`depth = 1024`): the `CALL` returns `0`, the body reverts. -/
theorem weth9WithdrawCallDepthRev {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat)
    (hdepth : I.depth = 1024)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h1464⟩ := weth9WithdrawToCall hperm hle h
  obtain ⟨_, _, rd1465⟩ :=
    h1464.callValueDepthLimitEmptyInOut hperm (by native_decide) hdepth (by evm_ov)
  obtain ⟨_, _, rd1470⟩ := weth9WithdrawAfterCall rd1465
  exact weth9WithdrawFailureTail (by decide) rd1470

/-- `bal ≥ wad`, insufficient contract balance: the `CALL` returns `0`, the body reverts. -/
theorem weth9WithdrawCallInsufficientRev {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat)
    (hbalance : ¬ withdrawWadWord I ≤
      ((withdrawStoreMap σ I).find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h1464⟩ := weth9WithdrawToCall hperm hle h
  obtain ⟨_, _, rd1465⟩ :=
    h1464.callValueInsufficientBalanceEmptyInOut hperm (by native_decide) hbalance hdepth (by evm_ov)
  obtain ⟨_, _, rd1470⟩ := weth9WithdrawAfterCall rd1465
  exact weth9WithdrawFailureTail (by decide) rd1470

/-- `bal ≥ wad`, sufficient balance, depth OK: the value `CALL` is dispatched; expose its `Θ` witness
    (for the Solm-side coupling) and the post-call `RD` at the branch (pc 1470). -/
theorem weth9WithdrawCallMade {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true)
    (hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat)
    (hbalance : withdrawWadWord I ≤
      ((withdrawStoreMap σ I).find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1395⟩
      [withdrawWadWord I, ⟨164⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o : ByteArray)
      (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks (withdrawStoreMap σ I)
          (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (solcSourceWord I))
          (toExecute (withdrawStoreMap σ I) (AccountAddress.ofUInt256 (solcSourceWord I)))
          callGas (UInt256.ofNat I.gasPrice) (withdrawWadWord I) (withdrawWadWord I)
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1470⟩
          [(if z then ⟨1⟩ else ⟨0⟩), withdrawWadWord I, ⟨164⟩, weth9SelWord I]
          (withdrawStoreMem I) (UInt256.ofNat 3) o (cA', σ') k' C' := by
  obtain ⟨_, _, h1464⟩ := weth9WithdrawToCall hperm hle h
  obtain ⟨cA', σ', z, o, A_in, callGas, _, _, hΘ, rd1465, hosz⟩ :=
    h1464.callValueMadeEmptyInOut (by native_decide) hperm hbalance hdepth (by evm_ov)
  refine ⟨cA', σ', z, o, A_in, callGas, ?_, hosz, weth9WithdrawAfterCall rd1465⟩
  simpa [initState] using hΘ

/-! ## Solm store-state accountMap (for the external-call coupling) -/

/-- The Solm store state's `accountMap` is the caller-keyed decremented map. -/
theorem withdrawStoreState_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (withdrawStoreState (initState cA gh bl σ σ₀ g A I) I).accountMap =
      sstoreAccountMap I.codeOwner σ (callerBalSlot I)
        (UInt256.sub (solcSlotWord σ I (callerBalSlot I)) (withdrawWadWord I)) := by
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have h : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner (callerBalSlot I)
      = solcSlotWord σ I (callerBalSlot I) := by
    simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState,
      Ethereum.Account.lookupStorage]
  unfold withdrawStoreState
  rw [hco, storageStore_accountMap, show (initState cA gh bl σ σ₀ g A I).accountMap = σ from rfl, h]

/-- The store state keeps the execution environment. -/
theorem withdrawStoreState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).executionEnv = evm.executionEnv := by
  unfold withdrawStoreState; rw [storageStore_executionEnv]

theorem withdrawStoreState_originalMap (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).σ₀ = evm.σ₀ := by
  unfold withdrawStoreState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawStoreState_createdAccounts (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).createdAccounts = evm.createdAccounts := by
  unfold withdrawStoreState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawStoreState_genesisBlockHeader (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold withdrawStoreState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawStoreState_blocks (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).blocks = evm.blocks := by
  unfold withdrawStoreState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem withdrawStoreState_substate (evm : EVM.State) (I : ExecutionEnv) :
    (withdrawStoreState evm I).substate = evm.substate := by
  unfold withdrawStoreState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

end Benchmarks.WETH9
