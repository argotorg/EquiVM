import Benchmarks.Midnight.BitmapSource
import Benchmarks.Midnight.InternalCall
import Benchmarks.Midnight.PositionViewSourceBase

/-! The shared source call to clear one collateral bitmap bit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: clear a bit with arbitrary argument expressions and result name.
theorem callBitmapClear {cfg : Config} {frame : Frame} {evm : EVM.State}
    {bitmap bit : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int bitmap.toNat, .int bit.toNat])
    (hbit : bit.toNat < 256) :
    ExecStmt cfg frame evm (.internalCall "UtilsLib_clearBit" args name)
      (.ok (wordLocal frame name (bitmapClear bitmap bit)) evm) := by
  let locals : Store := ((∅ : Store).insert "bit" (.int bit.toNat)).insert
    "bitmap" (.int bitmap.toNat)
  apply internalCallFunctionReturn (callee := bitmapClearFunction) (locals := locals)
    (value := some [.int (bitmapClear bitmap bit).toNat]) he
  · rw [hc]; rfl
  · rfl
  · exact bitmapClearSource (by exact store_get_self _ _ _)
      (by simp only [locals, store_get_ne _ _ (show ("bitmap" == "bit") = false from rfl),
        store_get_self]) hbit

end Benchmarks.Midnight
