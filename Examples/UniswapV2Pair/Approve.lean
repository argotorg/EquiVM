import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `approve(address,uint256)` canonical-success slice -/

/-- The raw ABI word for `approve`'s `spender` argument. -/
abbrev approveSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `approve`'s `value` argument. -/
abbrev approveValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev approveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

abbrev approveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveValueWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (approveSpenderValue I)).insert "value" (approveValueValue I)

abbrev approveSpenderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

def approveStorageSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address evm.executionEnv.source) (approveSpenderKey I)

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveStorageSlot evm I)
    (approveValueWord I)

abbrev approveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source), .mindex (approveSpenderKey I)] }

theorem approveStorageSlot_eq_mapSlot (evm : EVM.State) (I : ExecutionEnv)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus) :
    approveStorageSlot evm I =
      mapSlot (approveSpenderWord I) (mapSlot (UInt256.ofNat evm.executionEnv.source.val) ⟨2⟩) := by
  unfold approveStorageSlot allowanceSlot allowanceOwnerSlot approveSpenderKey
  rw [keyValueToWord_address_of_canonical _ hcanonSpender, keyValueToWord_address]

theorem approveStore_spender (I : ExecutionEnv) :
    (approveStore I).get? "spender" = some (approveSpenderValue I) := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_self]

theorem approveStore_value (I : ExecutionEnv) :
    (approveStore I).get? "value" = some (approveValueValue I) := by
  rw [approveStore, store_get_self]

theorem approveStore_allowance (I : ExecutionEnv) :
    (approveStore I).get? "allowance" = none := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_approve_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "spender") = .ok (approveSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_spender]

theorem evalExpr_approve_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "value") = .ok (approveValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_value]

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := approveStore I } evm
      (allowanceRef sender (.var "spender")) = .ok (approveEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef, sender,
    envValue, evalExpr_approve_spender, approveEvaledRef, approveSpenderValue, approveSpenderKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "spender")) (approveValueValue I) =
        .ok ({ contract := contract, locals := approveStore I }, approvePostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := approveStore_allowance I)
      (her := evalStorageRef_approve_allowance evm I)
      (hty := by
        simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [approvePostState, approveStorageSlot]

theorem uniswapDecode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some (approveStore I) := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, approveStore, approveSpenderValue, approveValueValue,
    approveSpenderWord, approveValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hcanon

theorem uniswapDecode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem uniswapDecode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, approveSpenderWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hnc

theorem uniswapDecode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "spender") (y := "value") hbig

/-- The Solm `approve(address,uint256)` body writes `allowance[msg.sender][spender]` and returns
    `true`. -/
theorem uniswapApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (approveStore I) approveTransition.body
      (.returned { contract := contract, locals := approveStore I } (approvePostState evm I)
        (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalExpr_approve_value evm I)
    (approveAssign evm I)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

/-! ## EVM trace prefix -/

/-- The optimized external wrapper for `approve(address,uint256)` accepts canonical calldata and
    jumps to the external approve routine at pc 2894. -/
theorem uniswapApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2894⟩
        [approveValueWord I, approveSpenderWord I, ⟨797⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd775⟩ := RD.uniswapAddressUint256ExternalLenOk
    (entry := ⟨753⟩) (ret := ⟨797⟩) (routine := ⟨2894⟩) hreach
    uniswap_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd2894⟩ := RD.uniswapAddressUint256ExternalMaskAndJump
    (entry := ⟨753⟩) (ret := ⟨797⟩) (routine := ⟨2894⟩) (R := [sel]) rd775
    uniswap_address_uint256_external_entry_wf
    (by simpa [approveSpenderWord] using hcanonSpender)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [approveSpenderWord, approveValueWord] using rd2894⟩

/-- Short-calldata path for `approve(address,uint256)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than two ABI words. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapAddressUint256ExternalShort
    (entry := ⟨753⟩) (ret := ⟨797⟩) (routine := ⟨2894⟩)
    hreach uniswap_address_uint256_external_entry_wf hsz4 hsize hshort

/-- The external `approve(address,uint256)` routine prepares the shared internal `_approve`
    routine call at pc 7412. -/
theorem RD.uniswapApproveExternalToInternal {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨2894⟩ (value :: spender :: ret :: R)
        mem aw rdata (cA, σ) k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: uniswapSourceWord ee :: ⟨2907⟩ :: ⟨0⟩ :: value :: spender :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd7412₀ := evm_run h with [
    jumpdest, push1 ⟨0⟩, push2 ⟨2907⟩, caller, dup5, dup5, push2 ⟨7412⟩]
  exact ⟨_, _, by
    simpa [uniswapSourceWord] using rd7412₀.jump (by decide) (by jump_dest) (by evm_ov)⟩

/-- The external `approve(address,uint256)` continuation receives `_approve`'s unit return and
    jumps to the bool-return wrapper with `true`. -/
theorem RD.uniswapApproveExternalFinish {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨2907⟩
        (⟨0⟩ :: value :: spender :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  have rd2916 := evm_run h with [
    jumpdest, pop, push1 ⟨1⟩, jumpdest, swap3, swap2, pop, pop]
  exact ⟨_, _, rd2916.jump (by decide) hret (by evm_ov)⟩

/-- Chained canonical-success prefix for `approve(address,uint256)`, from the dispatcher body pc
    to the shared internal `_approve` routine at pc 7412. -/
theorem uniswapApproveX_toInternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7412⟩
      (approveValueWord I :: approveSpenderWord I :: uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ ::
        approveValueWord I :: approveSpenderWord I :: ⟨797⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2894⟩ := uniswapApproveX_decoded (g := g)
    hsz68 hsize hcanonSpender hreach
  obtain ⟨_, _, rd7412⟩ := RD.uniswapApproveExternalToInternal
    (value := approveValueWord I) (spender := approveSpenderWord I) (ret := ⟨797⟩)
    (R := [sel]) rd2894 (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, rd7412⟩

/-- Chained canonical-success prefix for `approve(address,uint256)`, through the first
    nested-mapping hash inside the shared internal `_approve` routine. -/
theorem uniswapApproveX_innerHash {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7441⟩
      (mapSlot (uniswapSourceWord I) ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ ::
        uniswapSourceWord I :: solcAddrMask :: approveValueWord I :: approveSpenderWord I ::
        uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ :: approveValueWord I ::
        approveSpenderWord I :: ⟨797⟩ :: [sel])
      (twoWordHashMem (uniswapSourceWord I) ⟨2⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd7412⟩ := uniswapApproveX_toInternal (g := g)
    hsz68 hsize hcanonSpender hreach
  obtain ⟨_, _, rd7441⟩ := RD.uniswapApproveInternalInnerHash
    (value := approveValueWord I) (spender := approveSpenderWord I)
    (owner := uniswapSourceWord I) (ret := ⟨2907⟩)
    (R := [⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨797⟩, sel])
    rd7412 (uniswapSourceWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd7441⟩

/-- Chained canonical-success prefix for `approve(address,uint256)`, through the exact
    `SSTORE` of `allowance[msg.sender][spender]`. -/
theorem uniswapApproveX_store {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: uniswapSourceWord I :: approveSpenderWord I ::
        approveValueWord I :: approveSpenderWord I :: uniswapSourceWord I :: ⟨2907⟩ ::
        ⟨0⟩ :: approveValueWord I :: approveSpenderWord I :: ⟨797⟩ :: [sel])
      (twoWordHashMem (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩)
        (twoWordHashMem (uniswapSourceWord I) ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
        (approveValueWord I))
      k C := by
  obtain ⟨_, _, rd7441⟩ := uniswapApproveX_innerHash (g := g)
    hsz68 hsize hcanonSpender hreach
  obtain ⟨_, _, rd7457⟩ := RD.uniswapApproveInternalStore
    (value := approveValueWord I) (spender := approveSpenderWord I)
    (owner := uniswapSourceWord I) (ret := ⟨2907⟩)
    (R := [⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨797⟩, sel])
    rd7441 hperm hcanonSpender
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd7457⟩

/-- Chained canonical-success prefix for `approve(address,uint256)`, through the `Approval`
    event and back to the external approve continuation. -/
theorem uniswapApproveX_emit {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2907⟩
      (⟨0⟩ :: approveValueWord I :: approveSpenderWord I :: ⟨797⟩ :: [sel])
      (uniswapApproveLogMem (uniswapSourceWord I) (approveSpenderWord I) (approveValueWord I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
        (approveValueWord I))
      k C := by
  obtain ⟨_, _, rd7457⟩ := uniswapApproveX_store (g := g)
    hperm hsz68 hsize hcanonSpender hreach
  obtain ⟨_, _, rd2907⟩ := RD.uniswapApproveInternalEmitAndJump
    (value := approveValueWord I) (spender := approveSpenderWord I)
    (owner := uniswapSourceWord I) (ret := ⟨2907⟩)
    (R := [⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨797⟩, sel])
    rd7457 hperm (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [uniswapApproveHashMem] using rd2907⟩

/-- Complete canonical-success EVM path for `approve(address,uint256)`, returning ABI `true`. -/
theorem uniswapApproveX_success {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ
        (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
        (approveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd2907⟩ := uniswapApproveX_emit (g := g)
    hperm hsz68 hsize hcanonSpender hreach
  obtain ⟨_, _, rd797⟩ := RD.uniswapApproveExternalFinish
    (value := approveValueWord I) (spender := approveSpenderWord I) (ret := ⟨797⟩)
    (R := [sel]) rd2907 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hbool : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hmemout :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapApproveLogMem (uniswapSourceWord I) (approveSpenderWord I)
            (approveValueWord I)) 128 32 =
        uniswapApproveReturnMem (uniswapSourceWord I) (approveSpenderWord I)
          (approveValueWord I) ⟨1⟩ := by
    rw [hbool]
    rfl
  have hread128 :
      (uniswapApproveReturnMem (uniswapSourceWord I) (approveSpenderWord I)
        (approveValueWord I) ⟨1⟩).readWithPadding 128 32 =
          UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [hbool]
    exact uniswapApproveReturnMem_read128 (uniswapSourceWord I) (approveSpenderWord I)
      (approveValueWord I) ⟨1⟩
  have hret := RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapApproveLogMem (uniswapSourceWord I) (approveSpenderWord I)
      (approveValueWord I))
    (memout := uniswapApproveReturnMem (uniswapSourceWord I) (approveSpenderWord I)
      (approveValueWord I) ⟨1⟩)
    rd797
    (uniswapApproveLogMem_mload64 (uniswapSourceWord I) (approveSpenderWord I)
      (approveValueWord I))
    hmemout
    (uniswapApproveReturnMem_mload64 (uniswapSourceWord I) (approveSpenderWord I)
      (approveValueWord I) ⟨1⟩)
    hread128
      (by simp only [List.length_singleton]; omega)
  simpa [hbool] using hret

/- Canonical-success refinement slice for `approve(address,uint256)`.

The non-canonical address case is intentionally not claimed here: the optimized bytecode masks the
address word, while the current ABI decoder rejects non-canonical address encodings.
-/
set_option maxHeartbeats 2000000 in
theorem uniswapApproveBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (_hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hdecode :
      decodeCalldata (approveTransition.params.map Param.name)
        (transitionSignature approveTransition).paramTypes I.calldata = some (approveStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (approveStore I) approveTransition.body
        (.returned { contract := contract, locals := approveStore I }
          (approvePostState evmS I) (some (.bool true))) := by
    exact uniswapApproveBodyReturns evmS I (by simp only [evmS, initState]; exact hwv)
  have hslotS :
      approveStorageSlot evmS I =
        mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩) := by
    simpa [evmS, initState, uniswapSourceWord] using
      approveStorageSlot_eq_mapSlot evmS I hcanonSpender
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner σ_evm
          (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
          (approveValueWord I)).1 =
        (approvePostState evmS I).createdAccounts := by
    simp [approvePostState, evmS, initState, storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm
          (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
          (approveValueWord I))
        (approvePostState evmS I).accountMap := by
    unfold approvePostState
    rw [storageStore_accountMap]
    rw [hslotS]
    change accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm
        (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
        (approveValueWord I))
      (sstoreAccountMap I.codeOwner σ_solm
        (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
        (approveValueWord I))
    exact accountMapEquiv_sstoreAccountMap I.codeOwner
      (mapSlot (approveSpenderWord I) (mapSlot (uniswapSourceWord I) ⟨2⟩))
      (approveValueWord I) hAccounts
  exact (uniswapApproveX_success (g := Sat256.ofUInt256 g)
      hperm hsz68 hsize hcanonSpender hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody hcreated
      hAccountsPost (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Short-calldata decode-failure refinement slice for `approve(address,uint256)`.

The non-canonical and huge-calldata branches are intentionally not claimed here: the optimized
bytecode masks address words and uses an unsigned length check, while the current Solm ABI decoder
rejects those cases before execution.
-/
theorem uniswapApproveBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨753⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_approve_none_short (I := I) hsz4 hshort
  exact (uniswapApproveX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Canonical-success `approve(address,uint256)` refinement slice, packaged from selector dispatch
through the body core. -/
theorem uniswapApproveBodyOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ rfl hsel
  exact uniswapApproveBodyCoreOk hcode hsize hperm hwv hsz68 hbig hcanonSpender
    hdispatch
    (uniswapDecode_approve_ok hsz68 hbig hcanonSpender)
    (uniswapReachApproveBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `approve(address,uint256)` refinement slice, packaged from
selector dispatch through the body core. -/
theorem uniswapApproveBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ rfl hsel
  exact uniswapApproveBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachApproveBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapApproveBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus
      · exact uniswapApproveBodyOk hcode hsize hperm hwv hsel hsz68 hbig
          hcanonSpender hdispatch hAccounts
      · sorry
    · sorry
  · exact uniswapApproveBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
