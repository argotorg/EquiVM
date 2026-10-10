import Benchmarks.Morpho.MetaMorphoV1_1.CursorCastSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketValueUpdates
import Benchmarks.Morpho.MetaMorphoV1_1.CastAddFieldRoutines

/-! Source execution of a cursor-returning cast followed by a checked market-field sum. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem castFieldSourcePrefix {frame : Frame} {evm : State} {expr : Expr}
    {fields : List (Ident × Value)} {updated : Value} {old value ptr : UInt256}
    (field result : Ident) (tail : List Stmt)
    (hcontract : frame.contract = contract)
    (hslot : (result == slotsAndCursorName) = false)
    (hmarket : (result == "market") = false) (hcursor : (cursorName == result) = false)
    (hm : frame.locals.get? "market" = some (.struct "Market" fields))
    (hf : lookupField? (.struct "Market" fields) field = some (uint256Value old))
    (hu : updateField? (.struct "Market" fields) field (uint256Value (old + value)) =
      some updated)
    (hx : evalExpr? config frame evm expr = .ok (uint256Value value))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfit : castAddFits ptr value old) :
    ABlock config evm frame
      (cursorCall allocatedToUint128Function.name [expr] result ++
        marketFieldAdd field result :: tail)
      (marketUpdateFrame (cursorCastFrame frame result value ptr) updated) tail := by
  constructor
  intro answer htail
  apply (cursorCastSourcePrefix result _ hcontract hslot hx hp hfit.1 hfit.2.1).run
  apply ExecBlock.consNormal (marketFieldAddSource ?_ hf hu
    (cursorCastFrame_value _ _ _ _ hcursor) hfit.2.2) htail
  rw [cursorCastFrame_preserves _ _ _ _ _ (by decide) hmarket (by decide)]
  exact hm

theorem castFieldSourceReverts {frame : Frame} {evm : State} {expr : Expr}
    {fields : List (Ident × Value)} {old value ptr : UInt256}
    (field result : Ident) (tail : List Stmt)
    (hcontract : frame.contract = contract)
    (hslot : (result == slotsAndCursorName) = false)
    (hmarket : (result == "market") = false) (hcursor : (cursorName == result) = false)
    (hm : frame.locals.get? "market" = some (.struct "Market" fields))
    (hf : lookupField? (.struct "Market" fields) field = some (uint256Value old))
    (hx : evalExpr? config frame evm expr = .ok (uint256Value value))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hbad : ¬ castAddFits ptr value old) :
    ExecBlock config frame evm
      (cursorCall allocatedToUint128Function.name [expr] result ++
        marketFieldAdd field result :: tail) .reverted := by
  by_cases halloc : allocationFits ptr ⟨64⟩
  · by_cases hfit : value.toNat < 2 ^ 128
    · apply (cursorCastSourcePrefix result _ hcontract hslot hx hp halloc hfit).run
      apply ExecBlock.consRevert (marketFieldAddSourceReverts ?_ hf
        (cursorCastFrame_value _ _ _ _ hcursor)
        (Nat.le_of_not_lt (fun hsum ↦ hbad ⟨halloc, hfit, hsum⟩)))
      rw [cursorCastFrame_preserves _ _ _ _ _ (by decide) hmarket (by decide)]
      exact hm
    · exact cursorCastSourceReverts result _ hcontract hx hp (.inr (Nat.le_of_not_lt hfit))
  · exact cursorCastSourceReverts result _ hcontract hx hp (.inl halloc)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
