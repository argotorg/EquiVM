import Benchmarks.CompoundIII.Comet.Storage
import Benchmarks.CompoundIII.Comet.GetterCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def toBoolCallable : CallableDecl :=
  { params := [⟨"x", .elem (.int (.uint ⟨8, by decide⟩))⟩]
    returnType := [.elem .bool]
    body := [.return [.binary .ne (.var "x") (.intLit 0)]] }

theorem toBoolCallable_lookup : lookupCallable? contract "toBool" = some toBoolCallable := by
  rfl

theorem toBool_returns (frame : Frame) (evm : EVM.State) (w : UInt256) :
    ExecFuncBody config { frame with locals := (∅ : Store).insert "x" (.int w.toNat) }
      evm toBoolCallable.body
      (.returned { frame with locals := (∅ : Store).insert "x" (.int w.toNat) }
        evm (some [.bool (decide (w.toNat ≠ 0))])) := by
  exact .execBlockRet <| ABlock.start.returns (by
    simp [evalExpr?, evalBinaryOp?, pure, bind, EvalResult.bind, EvalResult.ofOption]
    apply Bool.eq_iff_iff.mpr
    simp)

theorem toBool_call (frame : Frame) (evm : EVM.State) (arg : Expr) (ret : Ident)
    (w : UInt256) (hc : frame.contract = contract)
    (harg : evalExpr? config frame evm arg = .ok (.int w.toNat)) :
    ExecStmt config frame evm (.internalCall "toBool" [arg] ret)
      (.ok { frame with locals := frame.locals.insert ret (.bool (decide (w.toNat ≠ 0))) }
        evm) := by
  exact ExecStmt.internalCallReturn (callee := toBoolCallable)
    (evalExprs?_singleton harg) (by rw [hc]; exact toBoolCallable_lookup) rfl
    (toBool_returns frame evm w)

-- LIBRARY CANDIDATE: a typed byte-sized AND agrees with word-level AND on canonical inputs.
theorem evalUint8And (x y : UInt256) (hx : x.toNat < 256) (hy : y.toNat < 256) :
    evalIntBitwise (.uint ⟨8, by decide⟩) Nat.land (.ofNat x.toNat) (.ofNat y.toNat) =
      .int (UInt256.land x y).toNat := by
  have hnorm (z : Nat) (hz : z < 256) :
      normalizeInt (.uint ⟨8, by decide⟩) (.ofNat z) = .ofNat z :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hz)
  unfold evalIntBitwise
  dsimp only [IntType.bitWidth]
  rw [hnorm x.toNat hx, hnorm y.toNat hy]
  change Value.int (normalizeInt (.uint ⟨8, by decide⟩) (.ofNat (Nat.land x.toNat y.toNat))) = _
  rw [hnorm _ (lt_of_le_of_lt (nat_land_le_right _ _) hy)]
  rw [uland_toNat]
  rfl

def pauseMaskExpr (bit : Fin 5) : Expr :=
  .binary (.shl (.uint ⟨8, by decide⟩))
    (.cast (.intLit 1) (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit bit.val)

theorem pauseMask_eval (frame : Frame) (evm : EVM.State) (bit : Fin 5) :
    evalExpr? config frame evm (pauseMaskExpr bit) =
      .ok (.int (UInt256.ofNat (2 ^ bit.val)).toNat) := by
  rcases bit with ⟨bit, hbit⟩
  interval_cases bit <;>
    simp [pauseMaskExpr, evalExpr?, evalBinaryOp?, castValue?, pure, bind, EvalResult.bind,
      EvalResult.ofOption, normalizeInt, EVM.twoPow, IntType.bitWidth, UInt256.toNat,
      UInt256.ofNat] <;> rfl

def pauseBitExpr (bit : Fin 5) : Expr :=
  .binary (.bitAnd (.uint ⟨8, by decide⟩)) (.storage ⟨"pauseFlags", []⟩) (pauseMaskExpr bit)

def pauseBitWord (evm : EVM.State) (bit : Fin 5) : UInt256 :=
  UInt256.land (pauseFlagsWord evm) (UInt256.ofNat (2 ^ bit.val))

theorem pauseBit_eval (evm : EVM.State) (locals imms : Store) (bit : Fin 5)
    (hlocal : locals.get? "pauseFlags" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (pauseBitExpr bit) = .ok (.int (pauseBitWord evm bit).toNat) := by
  have hmask : (UInt256.ofNat (2 ^ bit.val)).toNat < 256 := by
    rcases bit with ⟨bit, hbit⟩
    interval_cases bit <;> (dsimp only; decide)
  simp only [pauseBitExpr, evalExpr?, evalPauseFlags evm locals imms hlocal,
    pauseMask_eval, bind, EvalResult.bind, evalBinaryOp?, pauseBitWord]
  exact congrArg EvalResult.ok (evalUint8And _ _ (pauseFlagsWord_lt evm) hmask)

def pauseFunctionName (bit : Fin 5) : Ident :=
  match bit.val with
  | 0 => "isSupplyPaused_body"
  | 1 => "isTransferPaused_body"
  | 2 => "isWithdrawPaused_body"
  | 3 => "isAbsorbPaused_body"
  | _ => "isBuyPaused_body"

def pauseCallable (bit : Fin 5) : CallableDecl :=
  { params := [], returnType := [.elem .bool]
    body := [.internalCall "toBool" [pauseBitExpr bit] "__c0", .return [.var "__c0"]] }

theorem pauseCallable_lookup (bit : Fin 5) :
    lookupCallable? contract (pauseFunctionName bit) = some (pauseCallable bit) := by
  rcases bit with ⟨bit, hbit⟩
  interval_cases bit <;> rfl

theorem pauseCallable_returns (evm : EVM.State) (imms : Store) (bit : Fin 5) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms }
      evm (pauseCallable bit).body
      (.returned
        { contract := contract
          immutables := imms
          locals := (∅ : Store).insert "__c0" (.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))) }
        evm (some [.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (toBool_call _ evm (pauseBitExpr bit) "__c0" _ rfl
    (pauseBit_eval evm ∅ imms bit (by simp)))
  exact ABlock.start.returns (by simp [evalExpr?, EvalResult.ofOption])

def pauseGetterBody (bit : Fin 5) : List Stmt :=
  calldataPrologue [.internalCall (pauseFunctionName bit) [] "result", .return [.var "result"]]

theorem pauseGetter_returns (evm : EVM.State) (imms : Store) (bit : Fin 5)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract evm ∅ (pauseGetterBody bit)
      (.returned frame evm (some [.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))])) imms := by
  let caller : Frame := { contract := contract, locals := ∅, immutables := imms }
  refine ⟨resumeAfterInternalCall (calldataLocalFrame caller evm) "result"
    (some [.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))]), ExecFuncBody.execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hsize).run
  apply ExecBlock.consNormal
    (ExecStmt.internalCallReturn (callee := pauseCallable bit) (argVals := [])
      (by simp only [evalExprs?, pure]) (pauseCallable_lookup bit) rfl
      (pauseCallable_returns evm imms bit))
  exact ABlock.start.returns (by
    simp [evalExpr?, EvalResult.ofOption, resumeAfterInternalCall, collapseReturns])

def pauseBitRuntime (σ : AccountMap) (I : ExecutionEnv) (bit : Fin 5) : UInt256 :=
  UInt256.land (UInt256.shiftRight (solcSlotWordAt ⟨1⟩ σ I) ⟨248⟩)
    (UInt256.ofNat (2 ^ bit.val))

def pauseReturnWord (σ : AccountMap) (I : ExecutionEnv) (bit : Fin 5) : UInt256 :=
  UInt256.isZero (UInt256.isZero (pauseBitRuntime σ I bit))

theorem pauseBitWord_init {σ σ₀ A I} {g : Sat256} (bit : Fin 5) :
    pauseBitWord (initState σ σ₀ g A I) bit = pauseBitRuntime σ I bit := by
  rw [pauseBitWord, pauseFlagsWord_eq_shift, storageLoad_initState_solcSlotWord]
  rfl

theorem pauseGetter_refines {t : TransitionDecl} {imms : Store} {σ σ₀ A I} {g : UInt256}
    {code : ByteArray} (bit : Fin 5)
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg contract I.calldata = some t) (hp : t.params = [])
    (hb : t.body = pauseGetterBody bit) (ht : t.returnType = [.elem .bool])
    (hX : GetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ (pauseReturnWord σ I bit).toByteArray) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  apply guardedGetter_refines hcode hsz hd hp hb ht
    (nonzeroReturnEncoding (pauseBitRuntime σ I bit)) ?_ hX
  intro hvalue hsize
  simpa only [pauseBitWord_init] using
    pauseGetter_returns (initState σ σ₀ (Sat256.ofUInt256 g) A I) imms bit hvalue hsize

end Benchmarks.CompoundIII.Comet
