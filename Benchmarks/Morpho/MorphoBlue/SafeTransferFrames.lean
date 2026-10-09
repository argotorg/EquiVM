import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferArgs (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) : List Value :=
  [.address token] ++ (if isFrom then [.address sender] else []) ++
    [.address recipient, .int (Int.ofNat value.toNat), .int (Int.ofNat cursor)]

def safeTransferLocals (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) : Store :=
  let base := (((∅ : Store).insert "__memory" (.int (Int.ofNat cursor))).insert
    "value" (.int (Int.ofNat value.toNat))).insert "to" (.address recipient)
  let base := if isFrom then base.insert "from" (.address sender) else base
  base.insert "token" (.address token)

def safeTransferStart (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) (imms : Store) : Frame :=
  { contract := contract, locals := safeTransferLocals isFrom token sender recipient value cursor,
    immutables := imms }

theorem safeTransfer_bind (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) :
    bindParams? (safeTransferFunctionFor isFrom).params
      (safeTransferArgs isFrom token sender recipient value cursor) =
      some (safeTransferLocals isFrom token sender recipient value cursor) := by
  cases isFrom <;> rfl

theorem safeTransfer_lookup (isFrom : Bool) :
    lookupCallable? contract
      (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") =
      some (safeTransferFunctionFor isFrom).toCallable := by
  cases isFrom <;> rfl

structure SafeTransferInputs (frame : Frame) (isFrom : Bool)
    (token sender recipient : AccountAddress) (value : UInt256) (cursor : Nat) : Prop where
  token_eq : frame.locals.get? "token" = some (.address token)
  from_eq : isFrom = true → frame.locals.get? "from" = some (.address sender)
  to_eq : frame.locals.get? "to" = some (.address recipient)
  value_eq : frame.locals.get? "value" = some (.int (Int.ofNat value.toNat))
  memory_eq : frame.locals.get? "__memory" = some (.int (Int.ofNat cursor))

theorem safeTransferStart_inputs (isFrom : Bool) (token sender recipient : AccountAddress)
    (value : UInt256) (cursor : Nat) (imms : Store) :
    SafeTransferInputs (safeTransferStart isFrom token sender recipient value cursor imms)
      isFrom token sender recipient value cursor := by
  cases isFrom <;> constructor <;>
    simp [safeTransferStart, safeTransferLocals, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]

theorem SafeTransferInputs.prepared {frame isFrom token sender recipient value cursor}
    (h : SafeTransferInputs frame isFrom token sender recipient value cursor) :
    SafeTransferInputs (safeTransferPrepared frame isFrom cursor) isFrom token sender recipient
      value (cursor + safeTransferInputAllocation isFrom) := by
  constructor
  · exact (safeTransferPrepared_other _ _ _ _ (by decide)).trans h.token_eq
  · intro hm
    exact (safeTransferPrepared_other _ _ _ _ (by decide)).trans (h.from_eq hm)
  · exact (safeTransferPrepared_other _ _ _ _ (by decide)).trans h.to_eq
  · exact (safeTransferPrepared_other _ _ _ _ (by decide)).trans h.value_eq
  · exact safeTransferPrepared_memory _ _ _

def safeTransferCallArgs (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) : List Value :=
  (if isFrom then [.address sender] else []) ++
    [.address recipient, .int (Int.ofNat value.toNat)]

theorem SafeTransferInputs.encode {frame isFrom token sender recipient value cursor}
    (h : SafeTransferInputs frame isFrom token sender recipient value cursor)
    (evm : EVM.State) {cd : ByteArray}
    (hd : config.externalABI.encode? (if isFrom then "transferFrom" else "transfer")
      (safeTransferCallArgs isFrom sender recipient value) = some cd) :
    evalExpr? config frame evm (safeTransferCallDataExpr isFrom) = .ok (.bytes cd) := by
  cases isFrom
  · simp only [safeTransferCallDataExpr, safeTransferCallArgs, Bool.false_eq_true, ↓reduceIte,
      List.nil_append] at hd ⊢
    simp only [evalExpr?, evalExprList?.eq_def, h.to_eq, h.value_eq,
      EvalResult.ofOption, pure, bind, EvalResult.bind, hd]
  · simp only [safeTransferCallDataExpr, safeTransferCallArgs, ↓reduceIte,
      List.cons_append, List.nil_append] at hd ⊢
    simp only [evalExpr?, evalExprList?.eq_def, h.from_eq rfl, h.to_eq, h.value_eq,
      EvalResult.ofOption, pure, bind, EvalResult.bind, hd]

theorem safeTransferCalled_locals (frame : Frame) (isFrom : Bool) (cursor : Nat)
    (success : Bool) (out : ByteArray) :
    (safeTransferCalled frame isFrom cursor success out).locals.get? "__memory" =
      some (.int (Int.ofNat (cursor + safeTransferInputAllocation isFrom))) ∧
    (safeTransferCalled frame isFrom cursor success out).locals.get? "returndata" =
      some (.bytes out) ∧
    (safeTransferCalled frame isFrom cursor success out).locals.get? "success" =
      some (.bool success) := by
  simp only [safeTransferCalled, store_get_ne (k := "returndata") (a := "__memory") _ _ (by decide),
    store_get_ne (k := "success") (a := "__memory") _ _ (by decide), safeTransferPrepared_memory,
    store_get_ne (k := "returndata") (a := "success") _ _ (by decide), store_get_self,
    and_self]

end Benchmarks.Morpho.MorphoBlue
