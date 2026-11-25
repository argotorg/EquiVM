import Benchmarks.Midnight.InternalCall
import Benchmarks.Midnight.Allocation

variable {fork : Ethereum.Fork}

/-! The shared seven-entry settlement-fee cap table, in source and runtime memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

abbrev maxSettlementFeeFunction : FunctionDecl := contract.functions[0]!

def maxSettlementFees : List Nat :=
  [14000000000000, 14000000000000, 98000000000000, 417000000000000,
   1250000000000000, 2500000000000000, 5000000000000000]

def maxSettlementFeeValue (i : Fin 7) : Nat := maxSettlementFees[i]

def maxFeeValues : List Value := maxSettlementFees.map (fun n ↦ .int n)

def maxFeeWords : List UInt256 := maxSettlementFees.map UInt256.ofNat

def maxFeeArguments (i : Fin 7) : Store := (∅ : Store).insert "index" (.int i.val)

def maxFeeFrame (imms : Store) (i : Fin 7) : Frame :=
  { contract := contract, locals := (maxFeeArguments i).insert "fees" (.array maxFeeValues),
    immutables := imms }

theorem maxFeeIndexEval (i : Fin 7) :
    evalIndex? (.array maxFeeValues) (.int i.val) = .ok (.int (maxSettlementFeeValue i)) := by
  revert i
  decide

theorem maxFeeBodyReturns (evm : EVM.State) (imms : Store) (i : Fin 7) :
    ExecFuncBody fork config { contract := contract, locals := maxFeeArguments i, immutables := imms }
      evm maxSettlementFeeFunction.body
      (.returned (maxFeeFrame imms i) evm (some [.int (maxSettlementFeeValue i)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .array maxFeeValues) ?_) ?_
  · simp only [List.map_cons, List.map_nil, evalExpr?, evalExprList?, bind, pure, EvalResult.bind]
    rfl
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hi : ((maxFeeArguments i).insert "fees" (.array maxFeeValues)).get? "index" =
      some (.int i.val) := by
    rw [store_get_ne _ _ (by decide), maxFeeArguments, store_get_self]
  simp only [evalExprs?, evalExpr?, store_get_self, hi, EvalResult.ofOption,
    bind, pure, EvalResult.bind]
  rw [maxFeeIndexEval]

theorem maxFeeCall {frame : Frame} {evm : EVM.State} (i : Fin 7)
    (hc : frame.contract = contract)
    (hi : frame.locals.get? "index" = some (.int i.val)) :
    ExecStmt fork config frame evm (.internalCall "maxSettlementFee" [.var "index"] "__c0")
      (.ok (resumeAfterInternalCall frame "__c0" (some [.int (maxSettlementFeeValue i)])) evm) := by
  apply internalCallFunctionReturn (callee := maxSettlementFeeFunction)
    (locals := maxFeeArguments i) (argVals := [.int i.val])
  · simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, bind, pure, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · rw [hc]
    exact maxFeeBodyReturns evm frame.immutables i

theorem maxFeeValue_lt (i : Fin 7) : maxSettlementFeeValue i < UInt256.size := by
  revert i; decide

theorem maxFeeValue_bound (i : Fin 7) : maxSettlementFeeValue i ≤ 5000000000000000 := by
  revert i; decide

def maxFeeMemory (mem : ByteArray) : ByteArray :=
  writeWordArray (writeWord mem 64 ⟨1056⟩) 832 maxFeeWords

theorem maxFeeMemory_size (mem : ByteArray) : (maxFeeMemory mem).size = max mem.size 1056 := by
  simp only [maxFeeMemory, maxFeeWords, maxSettlementFees, List.map_cons, List.map_nil,
    writeWordArray, writeWord_sparse_size]
  omega

theorem maxFeeMemory_freePtr (mem : ByteArray) :
    memLoad (UInt256.ofNat 64) (maxFeeMemory mem) = ⟨1056⟩ := by
  rw [maxFeeMemory, memLoad_writeWordArray_below _ _ _ _
    (by rw [writeWord_sparse_size]; change 96 ≤ max mem.size 96; omega) (by decide)]
  exact memLoad_writeWord mem (UInt256.ofNat 64) ⟨1056⟩

theorem maxFeeMemory_zero {mem : ByteArray} (hsize : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩) :
    memLoad (UInt256.ofNat 800) (maxFeeMemory mem) = ⟨0⟩ := by
  rw [maxFeeMemory, memLoad_writeWordArray_below _ _ _ _
    (by rw [writeWord_sparse_size]; change 832 ≤ max mem.size 96; omega) (by decide)]
  rw [memLoad_writeWord_preserved mem 64 (UInt256.ofNat 800) ⟨1056⟩ hsize (Or.inr (by decide)), hzero]

theorem maxFeeMemory_writeZero {mem : ByteArray} (hsize : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩) (value : UInt256) :
    memLoad (UInt256.ofNat 800) (writeWord (maxFeeMemory mem) 1056 value) = ⟨0⟩ := by
  rw [memLoad_writeWord_preserved (maxFeeMemory mem) 1056 (UInt256.ofNat 800) value
    (by rw [maxFeeMemory_size]; change 832 ≤ max mem.size 1056; omega) (Or.inl (by decide)),
    maxFeeMemory_zero hsize hzero]

theorem maxFeeMemory_read (mem : ByteArray) (i : Fin 7) :
    memLoad (UInt256.ofNat (832 + 32 * i.val)) (maxFeeMemory mem) =
      UInt256.ofNat (maxSettlementFeeValue i) := by
  have ha : (UInt256.ofNat (832 + 32 * i.val)).toNat = 832 + 32 * i.val := by
    apply UInt256.toNat_ofNat_of_lt
    have := i.isLt
    have : 1056 < UInt256.size := by decide
    omega
  apply mloadWordValue_of_readWithPadding
  · rw [ha, maxFeeMemory_size]; have := i.isLt; omega
  · rw [ha]
    have hr := writeWordArray_read_index (writeWord mem 64 ⟨1056⟩) 832 maxFeeWords i
    have hw : maxFeeWords[i] = UInt256.ofNat (maxSettlementFeeValue i) := by
      clear * - i
      revert i
      decide
    exact hr.trans (congrArg UInt256.toByteArray hw)

theorem midnightMaxSettlementFee {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (i : Fin 7)
    (hstack : R.length + 9 ≤ 1024) (hmem : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨23967⟩ (UInt256.ofNat i.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret (UInt256.ofNat (maxSettlementFeeValue i) :: R)
      (maxFeeMemory mem) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_23967 (by simp; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23967_stack, hmem] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate224 (by simp; omega) (by native_decide)
    (by jump_dest) rd1
  have hi : (UInt256.ofNat i.val).toNat < 7 := by
    have hlarge : 7 < UInt256.size := by decide
    rw [UInt256.toNat_ofNat_of_lt (Nat.lt_trans i.isLt hlarge)]
    exact i.isLt
  obtain ⟨aw3, k3, C3, rd3⟩ := midnightBlocks.midnight_block_23980_fallthrough_packed
    (by simp; omega) (by rw [ult_one hi]; rfl) rd2
  change RD fork _ _ _ _ _ _ (maxFeeMemory mem) _ _ _ _ _ at rd3
  have rd4 := midnightBlocks.midnight_block_24075 (by simp; omega) hret rd3
  simp only [midnightBlocks.midnight_block_24075_stack] at rd4
  have ha : UInt256.shiftLeft (UInt256.ofNat i.val) (UInt256.ofNat 5) + ⟨832⟩ =
      UInt256.ofNat (832 + 32 * i.val) := by
    clear * - i
    revert i
    decide
  rw [ha, maxFeeMemory_read] at rd4
  exact ⟨_, _, _, rd4⟩

theorem midnightMaxSettlementFeeWord {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {index ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hi : index.toNat < 7)
    (hmem : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨23967⟩ (index :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret
      (UInt256.ofNat (maxSettlementFeeValue ⟨index.toNat, hi⟩) :: R)
      (maxFeeMemory mem) aw' rdata σ k' C' := by
  apply midnightMaxSettlementFee (aw := aw) (k := k) (C := C) ⟨index.toNat, hi⟩ hstack hmem hret
  simpa only [u256_ofNat_toNat] using rd

end Benchmarks.Midnight
