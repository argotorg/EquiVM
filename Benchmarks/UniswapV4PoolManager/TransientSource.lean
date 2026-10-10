import Benchmarks.UniswapV4PoolManager.Storage

/-! Transient lock, currency delta slots, and their source helpers. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

abbrev lockSlot : UInt256 := ⟨0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23⟩
abbrev deltaCountSlot : UInt256 := ⟨0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b⟩
abbrev lockFunction : FunctionDecl := contract.functions[3]!
abbrev accountDeltaFunction : FunctionDecl := contract.functions[26]!
abbrev uintToInt128Function : FunctionDecl := contract.functions[27]!
abbrev getDeltaFunction : FunctionDecl := contract.functions[43]!
abbrev applyDeltaFunction : FunctionDecl := contract.functions[79]!
abbrev decrementDeltaCountFunction : FunctionDecl := contract.functions[80]!
abbrev incrementDeltaCountFunction : FunctionDecl := contract.functions[81]!
abbrev deltaSlotFunction : FunctionDecl := contract.functions[84]!

theorem lockFunction_lookup : lookupCallable? contract "Lock_isUnlocked" = some lockFunction.toCallable := rfl
theorem deltaSlotFunction_lookup : lookupCallable? contract "CurrencyDelta__computeSlot" = some deltaSlotFunction.toCallable := rfl
theorem getDeltaFunction_lookup : lookupCallable? contract "CurrencyDelta_getDelta" = some getDeltaFunction.toCallable := rfl

def transientWord (evm : EVM.State) (slot : UInt256) : UInt256 :=
  Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot

theorem rawTransient_writeInt {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (value : Int) (hf : f.contract = contract)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    assignStorageRef? config f evm .transient {base := "rawTransient", steps := [.aindex index]}
      (.int value) =
      .ok (f, Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt value)) := by
  apply assignStorageRef_transient_scalar_value (rawTransient_ref hf he)
    (hbackend := rfl) (hloc := rawTransient_loc slot)
  · rw [hf]; exact rawTransient_type slot
  · exact Or.inl ⟨_, rfl⟩
  · exact transientLocStore_uint256_int _ _ _

theorem rawTransient_write {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (value : UInt256) (hf : f.contract = contract)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    assignStorageRef? config f evm .transient {base := "rawTransient", steps := [.aindex index]}
      (.int (Int.ofNat value.toNat)) =
      .ok (f, Solm.EVM.transientStore evm evm.executionEnv.codeOwner slot value) := by
  simpa only [wordOfInt_ofNat_toNat] using rawTransient_writeInt (Int.ofNat value.toNat) hf he

theorem evalLockSlot {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    evalExpr? config f evm (.const "LOCK_SLOT") = .ok (.int (Int.ofNat lockSlot.toNat)) := by
  rw [evalExpr?, hf]; rfl

theorem evalDeltaCountSlot {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    evalExpr? config f evm (.const "COUNT_SLOT") = .ok (.int (Int.ofNat deltaCountSlot.toNat)) := by
  rw [evalExpr?, hf]; rfl

theorem lockBodyExec {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecFuncBody config f evm lockFunction.body
      (.returned f evm (some [.bool (decide (transientWord evm lockSlot ≠ ⟨0⟩))])) := by
  have he := evalNeWords (rawTransient_read hf (evalLockSlot hf))
    (by simp only [evalExpr?]; rfl : evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)))
  exact ExecFuncBody.execBlockRet (ABlock.start.returns he)

theorem lockCall {f : Frame} {evm : EVM.State} (hf : f.contract = contract) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Lock_isUnlocked" [] retVar)
      (.ok {f with locals := f.locals.insert retVar (.bool (decide (transientWord evm lockSlot ≠ ⟨0⟩)))} evm) := by
  exact internalCallFunctionReturn rfl (by rw [hf]; exact lockFunction_lookup) rfl
    (lockBodyExec (f := {f with locals := ∅}) hf)

-- LIBRARY CANDIDATE: converting an address expression to its unsigned 160-bit value.
theorem evalAddressUint160 {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {a : AccountAddress}
    (he : evalExpr? cfg f evm e = .ok (.address a)) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.uint ⟨160, by decide⟩)))) =
      .ok (.int (Int.ofNat (accountWord a).toNat)) := by
  apply evalCastValue he
  simp only [castValue?, show a.toNat < EVM.twoPow 160 from a.isLt, if_true]
  rw [accountWord_toNat]
  rfl

-- LIBRARY CANDIDATE: packed encoding of two uint256 words.
theorem evalPackedWords2 {cfg : Config} {f : Frame} {evm : EVM.State} {e0 e1 : Expr} {w0 w1 : UInt256}
    (h0 : evalExpr? cfg f evm e0 = .ok (.int (Int.ofNat w0.toNat)))
    (h1 : evalExpr? cfg f evm e1 = .ok (.int (Int.ofNat w1.toNat))) :
    evalExpr? cfg f evm (.abiEncodePacked [(abiUInt256, e0), (abiUInt256, e1)]) =
      .ok (.bytes (w0.toByteArray ++ w1.toByteArray)) := by
  have he := evalPackedArgs_cons h0 (encodePacked_uint256 w0)
    (evalPackedArgs_single h1 (encodePacked_uint256 w1))
  rw [evalExpr?, he]
  simp only [bind, EvalResult.bind, pure]
  congr 2
  rw [mk_toArray_eq, List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]

-- LIBRARY CANDIDATE: evaluating keccak on bytes as a bytes32 word value.
theorem evalKeccakWord {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {bytes : ByteArray}
    (he : evalExpr? cfg f evm e = .ok (.bytes bytes)) :
    evalExpr? cfg f evm (.keccak256 e) = .ok (wordBytes32Value (uInt256OfByteArray (KEC bytes))) := by
  simp only [evalExpr?, he, bind, EvalResult.bind, pure, wordBytes32Value, toBytesBE_keccak_uInt256OfByteArray]
  rfl

def currencyDeltaSlot (target currency : AccountAddress) : UInt256 :=
  mappingSlotWord (accountWord target) (accountWord currency)

theorem deltaSlotBodyExec {f : Frame} {evm : EVM.State} {target currency : AccountAddress}
    (ht : f.locals.get? "target" = some (.address target))
    (hc : f.locals.get? "currency" = some (.address currency)) :
    ExecFuncBody config f evm deltaSlotFunction.body
      (.returned f evm (some [wordBytes32Value (currencyDeltaSlot target currency)])) := by
  have he := evalKeccakWord (cfg := config) (evm := evm)
    (evalPackedWords2 (evalAddressUint160 (evalLocalValue ht)) (evalAddressUint160 (evalLocalValue hc)))
  exact ExecFuncBody.execBlockRet (ABlock.start.returns he)

theorem deltaSlotCall {f : Frame} {evm : EVM.State} {target currency : AccountAddress}
    {et ec : Expr} (hf : f.contract = contract)
    (ht : evalExpr? config f evm et = .ok (.address target))
    (hc : evalExpr? config f evm ec = .ok (.address currency)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyDelta__computeSlot" [et, ec] retVar)
      (.ok {f with locals := f.locals.insert retVar (wordBytes32Value (currencyDeltaSlot target currency))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address target, .address currency])
    (value := some [wordBytes32Value (currencyDeltaSlot target currency)])
    (by simp only [evalExprs?, ht, hc, bind, EvalResult.bind, pure])
    (by rw [hf]; exact deltaSlotFunction_lookup) (by rfl)
  exact deltaSlotBodyExec (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("target" == "currency") = false)).trans (store_get_self _ _ _))

def currencyDeltaValue (evm : EVM.State) (target currency : AccountAddress) : Int :=
  normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat (transientWord evm (currencyDeltaSlot target currency)).toNat)

theorem getDeltaBodyExec {f : Frame} {evm : EVM.State} {target currency : AccountAddress}
    (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "target" = some (.address target)) :
    ExecFuncBody config f evm getDeltaFunction.body
      (.returned {f with locals := f.locals.insert "hashSlot" (wordBytes32Value (currencyDeltaSlot target currency))}
        evm (some [.int (currencyDeltaValue evm target currency)])) := by
  have hcall := deltaSlotCall (evm := evm) hf (evalLocalValue ht) (evalLocalValue hc) "hashSlot"
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal hcall (ABlock.start.returns ?_)
  apply evalExpr_cast_int
  exact rawTransient_read hf (evalCastValue (evalLocalValue (store_get_self _ _ _)) (castBytes32ToUint256 _))

theorem getDeltaCall {f : Frame} {evm : EVM.State} {target currency : AccountAddress}
    {ec et : Expr} (hf : f.contract = contract)
    (hc : evalExpr? config f evm ec = .ok (.address currency))
    (ht : evalExpr? config f evm et = .ok (.address target)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyDelta_getDelta" [ec, et] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (currencyDeltaValue evm target currency))} evm) := by
  apply internalCallFunctionReturn (argVals := [.address currency, .address target])
    (value := some [.int (currencyDeltaValue evm target currency)])
    (by simp only [evalExprs?, hc, ht, bind, EvalResult.bind, pure])
    (by rw [hf]; exact getDeltaFunction_lookup) (by rfl)
  exact getDeltaBodyExec hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "target") = false)).trans (store_get_self _ _ _))

-- LIBRARY CANDIDATE: tuple projection from an evaluated expression.
theorem evalTupleProjection {cfg : Config} {f : Frame} {evm : EVM.State}
    {e : Expr} {values : List Value} {i : Nat} {value : Value}
    (he : evalExpr? cfg f evm e = .ok (.tuple values)) (hi : values[i]? = some value) :
    evalExpr? cfg f evm (.tupleGet e i) = .ok value := by
  simp only [evalExpr?, he, bind, EvalResult.bind, tupleGetValue?, hi]

end Benchmarks.UniswapV4PoolManager
