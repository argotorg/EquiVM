import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Add

/-! Source market values and checked updates of their three mutable balance fields. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketUpdatedValue (out : ByteArray) (supplyAssets supplyShares borrowAssets : UInt256) :
    Value :=
  .struct "Market"
    [("totalSupplyAssets", uint256Value supplyAssets),
     ("totalSupplyShares", uint256Value supplyShares),
     ("totalBorrowAssets", uint256Value borrowAssets),
     ("totalBorrowShares", uint256Value (calldataWord out 96)),
     ("lastUpdate", uint256Value (calldataWord out 128)),
     ("fee", uint256Value (calldataWord out 160))]

theorem marketUpdatedValue_original (out : ByteArray) :
    marketUpdatedValue out (calldataWord out 0) (calldataWord out 32) (calldataWord out 64) =
      marketValue out := rfl

-- LIBRARY CANDIDATE: assignment to a local struct field preserves the rest of the frame.
theorem assignLocalField {cfg : Config} {frame : Frame} {evm : State}
    {root old value updated : Value} {base field : Ident}
    (hr : frame.locals.get? base = some root)
    (hf : lookupField? root field = some old)
    (hu : updateField? root field value = some updated) :
    assignStorageRef? cfg frame evm .localVar { base := base, steps := [.field field] } value =
      .ok ({ frame with locals := frame.locals.insert base updated }, evm) := by
  simp only [assignStorageRef?, hr, updateLocalPath?, hf, hu, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

def marketFieldAdd (field result : Ident) : Stmt :=
  .assign .localVar { base := "market", steps := [.field field] }
    (.inRange (.uint ⟨128, by decide⟩)
      (.binary .add (.field (.var "market") field) (.var result)))

def marketUpdateFrame (frame : Frame) (value : Value) : Frame :=
  { frame with locals := frame.locals.insert "market" value }

theorem marketFieldAddSource {frame : Frame} {evm : State}
    {fields : List (Ident × Value)} {updated : Value} {field result : Ident} {a b : UInt256}
    (hm : frame.locals.get? "market" = some (.struct "Market" fields))
    (hf : lookupField? (.struct "Market" fields) field = some (uint256Value a))
    (hu : updateField? (.struct "Market" fields) field (uint256Value (a + b)) = some updated)
    (hb : frame.locals.get? result = some (uint256Value b))
    (hsum : a.toNat + b.toNat < 2 ^ 128) :
    ExecStmt config frame evm (marketFieldAdd field result)
      (.ok (marketUpdateFrame frame updated) evm) := by
  exact ExecStmt.assign (uint128AddSource
    (evalExpr_structField
      (by simp only [evalExpr?, hm, EvalResult.ofOption]; rfl) hf)
    (by simp only [evalExpr?, hb, EvalResult.ofOption]) hsum)
    (assignLocalField hm hf hu)

theorem marketFieldAddSourceReverts {frame : Frame} {evm : State}
    {fields : List (Ident × Value)} {field result : Ident} {a b : UInt256}
    (hm : frame.locals.get? "market" = some (.struct "Market" fields))
    (hf : lookupField? (.struct "Market" fields) field = some (uint256Value a))
    (hb : frame.locals.get? result = some (uint256Value b))
    (hover : 2 ^ 128 ≤ a.toNat + b.toNat) :
    ExecStmt config frame evm (marketFieldAdd field result) .reverted := by
  exact ExecStmt.assignExprRevert (uint128AddSourceReverts
    (evalExpr_structField
      (by simp only [evalExpr?, hm, EvalResult.ofOption]; rfl) hf)
    (by simp only [evalExpr?, hb, EvalResult.ofOption]) hover)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
