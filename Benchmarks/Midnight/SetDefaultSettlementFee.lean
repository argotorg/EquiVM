import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.SettlementSetterSource
import Benchmarks.Midnight.ArrayStorage
import Benchmarks.Midnight.TripleDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PackedArray
import Benchmarks.Midnight.MappingMemory

/-!
# Midnight `setDefaultSettlementFee(address,uint256,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15196; reach lemma `midnightReachSetDefaultSettlementFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def settlementDefaultArguments (token : UInt256) (index : Nat) (value : UInt256) : Store :=
  (((∅ : Store).insert "loanToken" (.address (AccountAddress.ofNat token.toNat))).insert
    "index" (.int (Int.ofNat index))).insert "newSettlementFee" (.int value.toNat)

def settlementDefaultFrame (evm : EVM.State) (token value : UInt256) (i : Fin 7) : Frame :=
  resumeAfterInternalCall (calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm)
    "__c0" (some [.int (maxSettlementFeeValue i)])

def settlementDefaultState (evm : EVM.State) (token value : UInt256) (i : Fin 7) : EVM.State :=
  let slot := solcMappingSlot ⟨4⟩ token
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint16Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (settlementFeeQuotient value) ⟨i.val, by omega⟩)

theorem settlementDefaultInputValue (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256) :
    (calldataFrame contract (settlementDefaultArguments token index value) ∅ evm).locals.get?
      "newSettlementFee" = some (.int value.toNat) := by
  change (((settlementDefaultArguments token index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "newSettlementFee") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultArguments, store_get_self]

theorem settlementDefaultInputIndex (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256) :
    (calldataFrame contract (settlementDefaultArguments token index value) ∅ evm).locals.get?
      "index" = some (.int (Int.ofNat index)) := by
  change (((settlementDefaultArguments token index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "index") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultArguments, store_get_ne _ _ (by decide),
    store_get_self]

theorem settlementDefaultInputToken (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256) :
    (calldataFrame contract (settlementDefaultArguments token index value) ∅ evm).locals.get?
      "loanToken" = some (.address (AccountAddress.ofNat token.toNat)) := by
  change (((settlementDefaultArguments token index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "loanToken") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultArguments, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem settlementDefaultValueGet (evm : EVM.State) (token value : UInt256) (i : Fin 7) :
    (settlementDefaultFrame evm token value i).locals.get? "newSettlementFee" =
      some (.int value.toNat) := by
  change (((calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "newSettlementFee") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultInputValue]

theorem settlementDefaultIndexGet (evm : EVM.State) (token value : UInt256) (i : Fin 7) :
    (settlementDefaultFrame evm token value i).locals.get? "index" =
      some (.int (Int.ofNat i.val)) := by
  change (((calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "index") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultInputIndex]

theorem settlementDefaultTokenGet (evm : EVM.State) (token value : UInt256) (i : Fin 7) :
    (settlementDefaultFrame evm token value i).locals.get? "loanToken" =
      some (.address (AccountAddress.ofNat token.toNat)) := by
  change (((calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "loanToken") = _
  rw [store_get_ne _ _ (by decide), settlementDefaultInputToken]

theorem settlementDefaultCapGet (evm : EVM.State) (token value : UInt256) (i : Fin 7) :
    (settlementDefaultFrame evm token value i).locals.get? "__c0" =
      some (.int (maxSettlementFeeValue i)) := store_get_self _ _ _

theorem settlementDefaultAuthEval (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256) :
    evalExpr? config (calldataFrame contract (settlementDefaultArguments token index value) ∅ evm) evm
      (roleGuard "feeSetter") = .ok (.bool (decide (roleAllowed evm ⟨10⟩))) :=
  evalRoleGuard evm "feeSetter" ⟨10⟩ rfl
    (by simp [calldataFrame, settlementDefaultArguments]) rfl rfl

theorem settlementDefaultPrefix (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hauth : roleAllowed evm ⟨10⟩) :
    ABlock config evm (calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm)
      (setDefaultSettlementFeeTransition.body.drop 3) (settlementDefaultFrame evm token value i)
      (setDefaultSettlementFeeTransition.body.drop 6) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      (ExecBlock.consNormal (maxFeeCall i rfl (settlementDefaultInputIndex evm token i.val value)) h))⟩
  · simpa only [decide_eq_true hauth] using settlementDefaultAuthEval evm token i.val value
  · simpa only [decide_eq_true (show i.val ≤ 6 by omega)] using
      evalSettlementIndexBound (cfg := config) (evm := evm) (settlementDefaultInputIndex evm token i.val value)

theorem settlementDefaultGuards (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0) :
    ABlock config evm (calldataFrame contract (settlementDefaultArguments token i.val value) ∅ evm)
      (setDefaultSettlementFeeTransition.body.drop 3) (settlementDefaultFrame evm token value i)
      (setDefaultSettlementFeeTransition.body.drop 8) := by
  refine ⟨fun h ↦ (settlementDefaultPrefix evm token value i hauth).run
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) (ExecBlock.consNormal (ExecStmt.requireTrue ?_) h))⟩
  · simpa only [decide_eq_true hbound] using evalSettlementBound (cfg := config) (evm := evm)
      (settlementDefaultValueGet evm token value i) (settlementDefaultCapGet evm token value i)
  · simpa only [decide_eq_true hmultiple] using evalSettlementMultiple (cfg := config) (evm := evm)
      (settlementDefaultValueGet evm token value i)

theorem settlementDefaultAssign (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hcanon : token.toNat < EVM.addressModulus) :
    assignStorageRef? config (settlementDefaultFrame evm token value i) evm .storage
      { base := "defaultSettlementFeeCbp", steps := [.mindex (.var "loanToken"), .aindex (.var "index")] }
      (.int (Int.ofNat (settlementFeeQuotient value).toNat)) =
      .ok (settlementDefaultFrame evm token value i, settlementDefaultState evm token value i) := by
  apply assignStorageRef_storage_scalar_value (layout := midnightStorageLayout)
    (er := { base := "defaultSettlementFeeCbp", steps := [.mindex
      (.address (AccountAddress.ofNat token.toNat)), .aindex (.int (Int.ofNat i.val))] })
    (ty := .elem (.int packedUInt16Int)) (loc := uint16Loc (solcMappingSlot ⟨4⟩ token) ⟨i.val, by omega⟩)
  · simp [settlementDefaultFrame, resumeAfterInternalCall, collapseReturns,
      calldataFrame, settlementDefaultArguments]
  · rw [evalMappingArrayRef (settlementDefaultTokenGet evm token value i)
      (settlementDefaultIndexGet evm token value i) rfl
      (show storageTypeAt? _ _ = some (.array (.elem (.int packedUInt16Int)) 7) from rfl), if_pos i.isLt]
  · rfl
  · rfl
  · have hi16 : i.val < 16 := by omega
    have hiword : i.val < UInt256.size := Nat.lt_trans i.isLt (by decide)
    change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨4⟩ (keyValueToWord (.address (AccountAddress.ofNat token.toNat))) +
        UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i.val))).toNat / 16)
      offset := Fin.ofNat 32 (((keyValueToWord (.int (Int.ofNat i.val))).toNat % 16) * 2)
      size := 2, hbound := _, type := .int packedUInt16Int }) = _
    simp only [keyValueToWord_address_of_canonical token hcanon,
      keyValueToWord_int_ofNat_of_lt hiword, UInt256.toNat_ofNat_of_lt hiword,
      Nat.div_eq_of_lt hi16, Nat.mod_eq_of_lt hi16]
    change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨4⟩ token + ⟨0⟩, offset := Fin.ofNat 32 (i.val * 2), size := 2,
      hbound := _, type := .int packedUInt16Int }) = _
    rw [u256_add_zero]
    congr 3
    apply Fin.ext
    change (i.val * 2) % 32 = 2 * i.val
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint16_word evm _ _ _

theorem settlementDefaultAuthReverts (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ¬ roleAllowed evm ⟨10⟩) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token index value)
      setDefaultSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using settlementDefaultAuthEval evm token index value

theorem settlementDefaultIndexReverts (evm : EVM.State) (token : UInt256) (index : Nat) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hindex : ¬ index ≤ 6) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token index value)
      setDefaultSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using settlementDefaultAuthEval evm token index value
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hindex] using
    evalSettlementIndexBound (cfg := config) (evm := evm) (settlementDefaultInputIndex evm token index value)

theorem settlementDefaultBoundReverts (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : ¬ value.toNat ≤ maxSettlementFeeValue i) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token i.val value)
      setDefaultSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementDefaultPrefix evm token value i hauth).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hbound] using evalSettlementBound (cfg := config) (evm := evm)
    (settlementDefaultValueGet evm token value i) (settlementDefaultCapGet evm token value i)

theorem settlementDefaultMultipleReverts (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 ≠ 0) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token i.val value)
      setDefaultSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementDefaultPrefix evm token value i hauth).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using evalSettlementBound (cfg := config) (evm := evm)
      (settlementDefaultValueGet evm token value i) (settlementDefaultCapGet evm token value i)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hmultiple] using evalSettlementMultiple (cfg := config) (evm := evm)
    (settlementDefaultValueGet evm token value i)

theorem settlementDefaultReturns (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hcanon : token.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token i.val value)
      setDefaultSettlementFeeTransition.body
      (.returned (settlementDefaultFrame evm token value i) (settlementDefaultState evm token value i) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  apply (settlementDefaultGuards evm token value i hauth hbound hmultiple).run
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalSettlementCast i (settlementDefaultValueGet evm token value i) hbound)
    (settlementDefaultAssign evm token value i hcanon))
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address (AccountAddress.ofNat token.toNat), .int (Int.ofNat i.val), .int value.toNat]) ?_ ?_)
    ExecBlock.nil
  · simpa only [settlementDefaultState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, settlementDefaultTokenGet, settlementDefaultIndexGet,
      settlementDefaultValueGet, EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem settlementDefaultStatic (evm : EVM.State) (token value : UInt256) (i : Fin 7)
    (hcanon : token.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (settlementDefaultArguments token i.val value)
      setDefaultSettlementFeeTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply (settlementDefaultGuards evm token value i hauth hbound hmultiple).run
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (evalSettlementCast i (settlementDefaultValueGet evm token value i) hbound)
    (settlementDefaultAssign evm token value i hcanon) hperm

theorem settlementDefaultStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨15348⟩ (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)
      mem aw rdata σ k C) : RDstatic midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r9 := r8.dup1 (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.dup7 (by native_decide) (by evm_ov)
  have r12 := r11.div (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.or (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  exact r21.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem settlementDefaultTracePrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token value index : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : 64 ≤ mem.size)
    (hcanon : token.toNat < EVM.addressModulus) (hi : index.toNat < 7)
    (rd : RD midnightBytecode I g s0 ⟨15283⟩ (token :: value :: index :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨15348⟩
      (UInt256.ofNat (2 * index.toNat) :: solcMappingSlot ⟨4⟩ token :: value :: UInt256.ofNat 32 ::
        UInt256.ofNat 33574630258737581165192553333308920302038662582617165778577286065939461421092 ::
        token :: index :: R) (twoWordHashMem token ⟨4⟩ mem) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_15283 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_15283_stack, midnightBlocks.midnight_block_15283_memory,
    addressMask_computed, solcAddrMask_clean hcanon, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at rd1
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem token (UInt256.ofNat 4) mem) =
      solcMappingSlot ⟨4⟩ token := twoWordHashMem_mapSlot_of_ge64 token (UInt256.ofNat 4) hm
  rw [hh] at rd1
  obtain ⟨k2, C2, rd2⟩ := midnightUint16ArrayLocation (by simp; omega) hi (by jump_dest) rd1
  exact ⟨_, _, _, rd2⟩

theorem settlementDefaultTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token value index : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : 64 ≤ mem.size)
    (hcanon : token.toNat < EVM.addressModulus) (hi : index.toNat < 7) (hperm : I.perm = true)
    (rd : RD midnightBytecode I g s0 ⟨15283⟩ (token :: value :: index :: R) mem aw rdata σ k C) :
    RDret midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ token)
        (setUint16Word (solcSlotWordAt (solcMappingSlot ⟨4⟩ token) σ I)
          (settlementFeeQuotient value) ⟨index.toNat, by omega⟩)) ByteArray.empty := by
  obtain ⟨aw1, k1, C1, rd1⟩ := settlementDefaultTracePrepare hstack hm hcanon hi rd
  have hr := midnightBlocks.midnight_block_15348 hstack hperm rd1
  simp only [(uint16ArrayIndexFacts index hi).2.2] at hr
  simpa only [setUint16Word, settlementFeeQuotient, u256_land_comm] using hr

theorem settlementDefaultTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {token value index : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : 64 ≤ mem.size)
    (hcanon : token.toNat < EVM.addressModulus) (hi : index.toNat < 7) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨15283⟩ (token :: value :: index :: R) mem aw rdata σ k C) :
    RDstatic midnightBytecode g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := settlementDefaultTracePrepare hstack hm hcanon hi rd
  exact settlementDefaultStoreStatic hstack hperm rd1

/-- `setDefaultSettlementFee(address,uint256,uint256)`: the theorem `Correct.lean` routes selector 16 to. -/
theorem midnightSetDefaultSettlementFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setDefaultSettlementFeeTransition := by
    apply midnightDispatch_setDefaultSettlementFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetDefaultSettlementFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15196_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_15202_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_15214 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_15214_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          change RD _ _ _ _ _ [calldataWord I.calldata 4, solcSelectorWord I]
            midnightEntryMemory _ _ _ _ _ at rd4
          have hdec := midnightDecodeTriple_ok "loanToken" "index" "newSettlementFee"
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h100 hhi hsize
            (decodeAddressWord (off := 4) (by omega) hcanon)
            (decodeUint256Word (off := 36) (by omega)) (decodeUint256Word (off := 68) h100)
          by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_15221_fallthrough (by simp)
              (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
            simp only [midnightBlocks.midnight_block_15221_fallthrough_stack] at rd5
            change RD _ _ _ _ _ [calldataWord I.calldata 4, calldataWord I.calldata 68,
              calldataWord I.calldata 36, solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd5
            by_cases hi : (calldataWord I.calldata 36).toNat ≤ 6
            · have rd6 := midnightBlocks.midnight_block_15248_fallthrough (by simp) (ugt_zero hi) rd5
              have rd7 := midnightBlocks.midnight_block_15256 (by simp) (by jump_dest) rd6
              simp only [midnightBlocks.midnight_block_15256_stack] at rd7
              let i : Fin 7 := ⟨(calldataWord I.calldata 36).toNat, by omega⟩
              obtain ⟨aw8, k8, C8, rd8⟩ := midnightMaxSettlementFeeWord (by simp) (by omega)
                midnightEntryMemory_freePtr (by jump_dest) rd7
              have hcap : (UInt256.ofNat (maxSettlementFeeValue i)).toNat = maxSettlementFeeValue i :=
                UInt256.toNat_ofNat_of_lt (maxFeeValue_lt i)
              by_cases hbound : (calldataWord I.calldata 68).toNat ≤ maxSettlementFeeValue i
              · have rd9 := midnightBlocks.midnight_block_15264_fallthrough (by simp)
                  (ugt_zero (by rw [hcap]; exact hbound)) rd8
                simp only [midnightBlocks.midnight_block_15264_fallthrough_stack] at rd9
                by_cases hmultiple : (calldataWord I.calldata 68).toNat % 1000000000000 = 0
                · have rd10 := midnightBlocks.midnight_block_15271_fallthrough (by simp)
                    ((mod_eq_zero_iff _ _ (by decide)).mpr hmultiple) rd9
                  have hm : 64 ≤ (maxFeeMemory midnightEntryMemory).size := by
                    rw [maxFeeMemory_size]; omega
                  by_cases hperm : I.perm = true
                  · have hr := settlementDefaultTraceReturn (by simp) hm hcanon (by omega) hperm rd10
                    have hac := storageWordWrite_accounts (σ := σ)
                      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                      (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4))
                      (fun old ↦ setUint16Word old (settlementFeeQuotient (calldataWord I.calldata 68))
                        ⟨i.val, by omega⟩)
                    exact hr.reEquivExecutionGen hcode hd hdec
                      (settlementDefaultReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                        hcanon hwv hhi hauth hbound hmultiple hperm) hac voidReturnEquiv
                  · have hp : I.perm = false := by
                      cases h : I.perm
                      · rfl
                      · exact False.elim (hperm h)
                    have hr := settlementDefaultTraceStatic (by simp) hm hcanon (by omega) hp rd10
                    exact hr.reEquivStaticHalt hcode hd hdec
                      (settlementDefaultStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                        hcanon hwv hhi hauth hbound hmultiple hp)
                · have rd10 := midnightBlocks.midnight_block_15271_taken (by simp)
                    (fun h ↦ hmultiple ((mod_eq_zero_iff _ _ (by decide)).mp h)) (by jump_dest) rd9
                  have hr := midnightBlocks.midnight_block_15386 (by simp) rd10
                  exact hr.reEquivExecutionRevert hcode hd hdec
                    (settlementDefaultMultipleReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                      hwv hhi hauth hbound hmultiple)
              · have rd9 := midnightBlocks.midnight_block_15264_taken (by simp)
                  (by rw [ugt_one (by rw [hcap]; exact Nat.lt_of_not_ge hbound)]; decide)
                  (by jump_dest) rd8
                have hr := midnightBlocks.midnight_block_15401
                  (by simp [midnightBlocks.midnight_block_15264_taken_stack]) rd9
                exact hr.reEquivExecutionRevert hcode hd hdec
                  (settlementDefaultBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 68) i hwv hhi hauth hbound)
            · have rd6 := midnightBlocks.midnight_block_15248_taken (by simp)
                (by rw [ugt_one (a := calldataWord I.calldata 36) (b := UInt256.ofNat 6)
                  (Nat.lt_of_not_ge hi)]; decide) (by jump_dest) rd5
              have hr := midnightBlocks.midnight_block_15416 (by simp) rd6
              exact hr.reEquivExecutionRevert hcode hd hdec
                (settlementDefaultIndexReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat
                  (calldataWord I.calldata 68) hwv hhi hauth hi)
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_15221_taken (by simp)
              (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
              (by jump_dest) rd4
            have hr := midnightBlocks.midnight_block_15431
              (by simp [midnightBlocks.midnight_block_15221_taken_stack]) rd5
            exact hr.reEquivExecutionRevert hcode hd hdec
              (settlementDefaultAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat
                (calldataWord I.calldata 68) hwv hhi hauth)
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeTriple_none_left "loanToken" "index" "newSettlementFee"
              .address (.int (.uint ⟨256, by decide⟩)) (.int (.uint ⟨256, by decide⟩))
              h100 hhi hsize (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_15202_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "loanToken" "index" "newSettlementFee"
            .address (.int (.uint ⟨256, by decide⟩)) (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_15202_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "loanToken" "index" "newSettlementFee"
          .address (.int (.uint ⟨256, by decide⟩)) (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_15196_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setDefaultSettlementFeeTransition.params.map Param.name)
        (transitionSignature setDefaultSettlementFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
