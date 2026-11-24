import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}

/-! # EAS memory allocator: source execution and compiled routine -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.SteleArithmetic.assignLocalVarBase_ok: preserve arbitrary immutables.
theorem assignLocalBase_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} (hget : frame.locals.get? name = some old) :
    assignStorageRef? cfg frame evm .localVar {base := name} value =
      .ok ({frame with locals := frame.locals.insert name value}, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, EvalResult.bind, bind, pure]

abbrev allocateFunction : FunctionDecl := contract.functions[0]!

def allocateRounded (size : Nat) : Nat := ((size + 31) % UInt256.size) / 32 * 32

def allocateNext (heap size : Nat) : Nat := (heap + allocateRounded size) % UInt256.size

def allocatePrefix : Body := [
  .letDecl "rounded" (some (.elem (.int (.uint ⟨256, by decide⟩))))
    (.cast (.binary .add (.var "size") (.intLit 31)) (.elem (.int (.uint ⟨256, by decide⟩)))),
  .assign .localVar {base := "rounded"}
    (.binary .mul (.binary .div (.var "rounded") (.intLit 32)) (.intLit 32)),
  .letDecl "next" (some (.elem (.int (.uint ⟨256, by decide⟩))))
    (.cast (.binary .add (.var "$EAS.freeMemory") (.var "rounded"))
      (.elem (.int (.uint ⟨256, by decide⟩))))]

def allocateGuard : Expr :=
  .binary .and (.binary .le (.var "next") (.intLit (2^64-1)))
    (.binary .ge (.var "next") (.var "$EAS.freeMemory"))

def allocateSuffix : Body := [
  .require allocateGuard,
  .assign .localVar {base := "$EAS.freeMemory"} (.var "next"),
  .return [.tupleLit [], .var "$EAS.freeMemory"]]

theorem allocate_body : allocateFunction.body = allocatePrefix ++ allocateSuffix := by
  native_decide

def allocatePrefixLocals (locals : Store) (heap size : Nat) : Store :=
  locals
    |>.insert "rounded" (.int (Int.ofNat ((size + 31) % UInt256.size)))
    |>.insert "rounded" (.int (Int.ofNat (allocateRounded size)))
    |>.insert "next" (.int (Int.ofNat (allocateNext heap size)))

-- LIBRARY CANDIDATE: casting a sum of natural-valued expressions to a uint256.
theorem evalCastUint256Add {cfg : Config} {frame : Frame} {evm : EVM.State}
    {a b : Expr} {x y : Nat}
    (hx : evalExpr? cfg frame evm a = .ok (.int (Int.ofNat x)))
    (hy : evalExpr? cfg frame evm b = .ok (.int (Int.ofNat y))) :
    evalExpr? cfg frame evm (.cast (.binary .add a b) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat ((x + y) % UInt256.size))) := by
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, evalBinaryOp?, castValue?,
    normalizeInt, EvalResult.ofOption]
  simp only [Int.ofNat_eq_natCast]
  norm_cast

-- LIBRARY CANDIDATE: floor a natural-valued expression to a multiple of 32.
theorem evalFloor32 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {n : Nat} (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.binary .mul (.binary .div e (.intLit 32)) (.intLit 32)) =
      .ok (.int (Int.ofNat (n / 32 * 32))) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast]
  norm_num

theorem allocatePrefix_exec {cfg : Config} {frame : Frame} {evm : EVM.State}
    {heap size : Nat}
    (hs : frame.locals.get? "size" = some (.int (Int.ofNat size)))
    (hp : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork cfg frame evm allocatePrefix
      (.ok {frame with locals := allocatePrefixLocals frame.locals heap size} evm) := by
  have hsEval : evalExpr? cfg frame evm (.var "size") = .ok (.int (Int.ofNat size)) := by
    simp only [evalExpr?, hs, EvalResult.ofOption]
  have hround := evalCastUint256Add hsEval
    (show evalExpr? cfg frame evm (.intLit 31) = .ok (.int (Int.ofNat (31 : Nat))) by simp only [evalExpr?, pure]; rfl)
  refine ExecBlock.consNormal (ExecStmt.letDecl hround) ?_
  have hr : evalExpr? cfg {frame with locals := frame.locals.insert "rounded" (.int (Int.ofNat ((size + 31) % UInt256.size)))}
      evm (.var "rounded") = .ok (.int (Int.ofNat ((size + 31) % UInt256.size))) := by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalFloor32 hr) (assignLocalBase_ok (store_get_self _ _ _))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat (allocateNext heap size))) ?_) ExecBlock.nil
  apply evalCastUint256Add
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("rounded" == "$EAS.freeMemory") = false), hp, EvalResult.ofOption]
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption, allocateRounded]

theorem allocatePrefix_get_heap {locals : Store} {heap size : Nat}
    (hp : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    (allocatePrefixLocals locals heap size).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [allocatePrefixLocals,
    store_get_ne _ _ (by decide : ("next" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("rounded" == "$EAS.freeMemory") = false), hp]

theorem evalAllocateGuard {cfg : Config} {frame : Frame} {evm : EVM.State}
    {heap next : Nat}
    (hn : frame.locals.get? "next" = some (.int (Int.ofNat next)))
    (hp : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    evalExpr? cfg frame evm allocateGuard = .ok (.bool (decide (next ≤ 2^64-1 ∧ heap ≤ next))) := by
  simp only [allocateGuard, evalExpr?, hn, hp, EvalResult.ofOption, EvalResult.bind,
    bind, pure, evalBinaryOp?, Int.ofNat_eq_natCast]
  have hn' : ((next : ℤ) ≤ 2^64-1) = (next ≤ 2^64-1) := by apply propext; omega
  have hp' : ((heap : ℤ) ≤ next) = (heap ≤ next) := by apply propext; omega
  simp only [hn', hp']
  by_cases hn : next ≤ 18446744073709551615 <;> simp [hn]

def allocateFinalLocals (locals : Store) (heap size : Nat) : Store :=
  (allocatePrefixLocals locals heap size).insert "$EAS.freeMemory" (.int (Int.ofNat (allocateNext heap size)))

theorem allocateSource_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {heap size : Nat}
    (hs : frame.locals.get? "size" = some (.int (Int.ofNat size)))
    (hp : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hguard : allocateNext heap size ≤ 2^64-1 ∧ heap ≤ allocateNext heap size) :
    ExecFuncBody fork cfg frame evm allocateFunction.body
      (.returned {frame with locals := allocateFinalLocals frame.locals heap size}
        evm (some [.tuple [], .int (Int.ofNat (allocateNext heap size))])) := by
  rw [allocate_body]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (allocatePrefix_exec hs hp)
  have hp' := allocatePrefix_get_heap (size := size) hp
  have hn : (allocatePrefixLocals frame.locals heap size).get? "next" =
      some (.int (Int.ofNat (allocateNext heap size))) := store_get_self _ _ _
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hguard, decide_true] using evalAllocateGuard (evm := evm) (cfg := cfg)
      (frame := {frame with locals := allocatePrefixLocals frame.locals heap size}) hn hp'
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int (Int.ofNat (allocateNext heap size)))
    ?_ (assignLocalBase_ok hp')) ?_
  · simp only [evalExpr?, hn, EvalResult.ofOption]
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExprList?, evalExpr?, store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocateSource_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {heap size : Nat}
    (hs : frame.locals.get? "size" = some (.int (Int.ofNat size)))
    (hp : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hguard : ¬ (allocateNext heap size ≤ 2^64-1 ∧ heap ≤ allocateNext heap size)) :
    ExecFuncBody fork cfg frame evm allocateFunction.body .reverted := by
  rw [allocate_body]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (allocatePrefix_exec hs hp)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hguard, decide_false] using evalAllocateGuard (evm := evm) (cfg := cfg)
    (frame := {frame with locals := allocatePrefixLocals frame.locals heap size})
    (store_get_self _ _ _) (allocatePrefix_get_heap (size := size) hp)

theorem allocateNext_word (heap size : UInt256) :
    heap + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩) =
      UInt256.ofNat (allocateNext heap.toNat size.toNat) := by
  apply u256_inj
  rw [uadd_toNat, longDataCutoff_toNat, uadd_toNat]
  change allocateNext heap.toNat size.toNat = _
  exact (ulit_toNat' _ (Nat.mod_lt _ (by decide))).symm

theorem allocateCheck_ok (heap size : UInt256)
    (hguard : allocateNext heap.toNat size.toNat ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat size.toNat) :
    UInt256.lor
      (UInt256.gt (heap + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) ⟨18446744073709551615⟩)
      (UInt256.lt (heap + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) heap) = ⟨0⟩ := by
  rw [allocateNext_word]
  have hn : (UInt256.ofNat (allocateNext heap.toNat size.toNat)).toNat = allocateNext heap.toNat size.toNat :=
    ulit_toNat' _ (Nat.mod_lt _ (by decide))
  rw [ugt_zero (by rw [hn]; exact hguard.1), ult_zero (by rw [hn]; exact hguard.2)]
  decide

theorem allocateCheck_revert (heap size : UInt256)
    (hguard : ¬ (allocateNext heap.toNat size.toNat ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat size.toNat)) :
    UInt256.lor
      (UInt256.gt (heap + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) ⟨18446744073709551615⟩)
      (UInt256.lt (heap + UInt256.land (size + ⟨31⟩) (UInt256.lnot ⟨31⟩)) heap) ≠ ⟨0⟩ := by
  rw [allocateNext_word]
  have hn : (UInt256.ofNat (allocateNext heap.toNat size.toNat)).toNat = allocateNext heap.toNat size.toNat :=
    ulit_toNat' _ (Nat.mod_lt _ (by decide))
  by_cases hb : allocateNext heap.toNat size.toNat ≤ 2^64-1
  · have hh : allocateNext heap.toNat size.toNat < heap.toNat := by omega
    rw [ult_one (by rw [hn]; exact hh)]
    exact u256_lor_one_right_ne_zero _
  · rw [ugt_one (by rw [hn]; change 18446744073709551615 < allocateNext heap.toNat size.toNat; omega)]
    exact u256_lor_one_left_ne_zero _

theorem easAllocate_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap size ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024)
    (hguard : allocateNext heap.toNat size.toNat ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat size.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4883⟩ (heap :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat size.toNat))) aw' rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_4883_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (allocateCheck_ok heap size hguard) rd
  obtain ⟨aw', k', C', rd2⟩ := easBlocks.eas_block_4944_packed (immWords := wordsOf (immStore v))
    (by omega) hvalid rd1
  refine ⟨aw', k', C', ?_⟩
  simpa only [easBlocks.eas_block_4944_stack, easBlocks.eas_block_4944_memory,
    show UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 = UInt256.lnot ⟨31⟩ from rfl,
    show UInt256.ofNat 31 = (⟨31⟩ : UInt256) from rfl,
    allocateNext_word, Reasoning.Theory.writeWord] using rd2

theorem easAllocate_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap size : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hguard : ¬ (allocateNext heap.toNat size.toNat ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat size.toNat))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4883⟩ (heap :: size :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_4883_taken (immWords := wordsOf (immStore v))
    hstack (allocateCheck_revert heap size hguard)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_4723 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_4883_taken_stack, List.length_cons]; omega) rd1

theorem allocate_lookup : lookupCallable? contract "_allocate" = some allocateFunction.toCallable := by
  rfl

def allocateArgs (heap size : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "size" (.int (Int.ofNat size))

theorem allocate_bind (heap size : Nat) :
    bindParams? allocateFunction.params [.int (Int.ofNat size), .int (Int.ofNat heap)] =
      some (allocateArgs heap size) := by
  rfl

theorem allocateCall_ok {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {sizeExpr heapExpr : Expr} {heap size : Nat} {retVar : Ident}
    (hs : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm sizeExpr =
      .ok (.int (Int.ofNat size)))
    (hp : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm heapExpr =
      .ok (.int (Int.ofNat heap)))
    (hguard : allocateNext heap size ≤ 2^64-1 ∧ heap ≤ allocateNext heap size) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_allocate" [sizeExpr, heapExpr] retVar)
      (.ok {
        contract := contract
        locals := locals.insert retVar (.tuple [.tuple [], .int (Int.ofNat (allocateNext heap size))]),
        immutables := imms} evm) := by
  exact internalCallFunctionReturn
    (by simp only [evalExprs?, hs, hp, bind, EvalResult.bind, pure])
    allocate_lookup (allocate_bind heap size)
    (allocateSource_ok
      (store_get_self _ _ _)
      (by simp only [allocateArgs, store_get_ne _ _ (by decide : ("size" == "$EAS.freeMemory") = false), store_get_self]) hguard)

theorem allocateCall_revert {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {sizeExpr heapExpr : Expr} {heap size : Nat} {retVar : Ident}
    (hs : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm sizeExpr =
      .ok (.int (Int.ofNat size)))
    (hp : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm heapExpr =
      .ok (.int (Int.ofNat heap)))
    (hguard : ¬ (allocateNext heap size ≤ 2^64-1 ∧ heap ≤ allocateNext heap size)) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_allocate" [sizeExpr, heapExpr] retVar) .reverted := by
  exact internalCallFunctionRevert
    (by simp only [evalExprs?, hs, hp, bind, EvalResult.bind, pure])
    allocate_lookup (allocate_bind heap size)
    (allocateSource_revert
      (store_get_self _ _ _)
      (by simp only [allocateArgs, store_get_ne _ _ (by decide : ("size" == "$EAS.freeMemory") = false), store_get_self]) hguard)

-- LIBRARY CANDIDATE: unpack a function result with a threaded heap cursor.
def unpackHeapLocals (locals : Store) (result cursor : Ident) (value : Value) (heap : Nat) : Store :=
  locals.insert result value |>.insert cursor (.int (Int.ofNat heap))

theorem unpackHeapResult {cfg : Config} {frame : Frame} {evm : EVM.State}
    {tmp result cursor : Ident} {value old : Value} {heap : Nat}
    (hret : frame.locals.get? tmp = some (.tuple [value, .int (Int.ofNat heap)]))
    (hheap : frame.locals.get? cursor = some old)
    (hrt : (result == tmp) = false) (hrc : (result == cursor) = false) :
    ExecBlock fork cfg frame evm
      [.letDecl result none (.tupleGet (.var tmp) 0),
       .assign .localVar {base := cursor} (.tupleGet (.var tmp) 1)]
      (.ok {frame with locals := unpackHeapLocals frame.locals result cursor value heap} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := value) ?_) ?_
  · simp only [evalExpr?, hret, EvalResult.ofOption, EvalResult.bind, bind]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int (Int.ofNat heap)) ?_
    (assignLocalBase_ok (by simpa only [store_get_ne _ _ hrc] using hheap))) ExecBlock.nil
  simp only [evalExpr?, store_get_ne _ _ hrt, hret, EvalResult.ofOption, EvalResult.bind, bind]
  rfl


end Benchmarks.EAS.EAS
