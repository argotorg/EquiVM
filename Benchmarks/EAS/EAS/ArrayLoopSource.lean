import Benchmarks.EAS.EAS.ResolveManySource
import Benchmarks.EAS.Attester.LocalArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def localCastIncrement (name : Ident) : Stmt := .assign .localVar {base := name}
  (.cast (.binary .add (.var name) (.intLit 1)) (.elem (.int abiUInt256Int)))
def localArrayGuard (index array : Ident) : Expr :=
  .binary .lt (.var index) (.arrayLength .localVar {base := array})

-- GENERALIZES resolveManyIncrementSource to any local counter.
theorem execLocalCastIncrement {cfg : Config} {frame : Frame} {evm : EVM.State} {name : Ident} {i : Nat}
    (hi : frame.locals.get? name = some (.int (Int.ofNat i))) (hb : i+1 < UInt256.size) :
    ExecStmt fork cfg frame evm (localCastIncrement name)
      (.ok {frame with locals := frame.locals.insert name (.int (Int.ofNat (i+1)))} evm) := by
  have he := evalCastUint256Add (cfg := cfg) (evm := evm) (frame := frame)
    (a := .var name) (b := .intLit 1) (x := i) (y := 1) (evalLocalValue hi) (by simp only [evalExpr?]; rfl)
  rw [Nat.mod_eq_of_lt hb] at he
  exact ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalValue hi)

-- LIBRARY CANDIDATE: an array loop guard evaluated through local bindings.
theorem evalLocalArrayGuard {cfg : Config} {frame : Frame} {evm : EVM.State} {index array : Ident}
    {i : Nat} {values : List Value}
    (hi : frame.locals.get? index = some (.int (Int.ofNat i)))
    (ha : frame.locals.get? array = some (.array values)) :
    evalExpr? cfg frame evm (localArrayGuard index array) = .ok (.bool (decide (i < values.length))) := by
  have hl := evalLocalArrayLength (cfg := cfg) (evm := evm) ha
  simp only [localArrayGuard,evalExpr?,hi,hl,EvalResult.ofOption,EvalResult.bind,bind,
    evalBinaryOp_lt_int_ok,Int.ofNat_eq_natCast,Nat.cast_lt]

-- LIBRARY CANDIDATE: copying one bytes32 element between source memory arrays.
theorem execLocalWordArrayCopy {cfg : Config} {frame : Frame} {evm : EVM.State}
    {dst src di si : Ident} {words values : List UInt256} {i j : Nat}
    (hd : frame.locals.get? dst = some (.array (words.map wordBytes32Value)))
    (hs : frame.locals.get? src = some (.array (values.map wordBytes32Value)))
    (hi : frame.locals.get? di = some (.int (Int.ofNat i)))
    (hj : frame.locals.get? si = some (.int (Int.ofNat j)))
    (hib : i < words.length) (hjb : j < values.length) :
    ExecStmt fork cfg frame evm (.assign .localVar {base := dst,steps := [.aindex (.var di)]} (.index (.var src) (.var si)))
      (.ok {frame with locals := frame.locals.insert dst (.array ((words.set i values[j]).map wordBytes32Value))} evm) := by
  have he : evalExpr? cfg frame evm (.index (.var src) (.var si)) = .ok (wordBytes32Value values[j]) :=
    evalArrayIndex (evalLocalValue hs) (evalLocalValue hj) (by simpa only [List.length_map] using hjb) (List.getElem_map ..) rfl
  apply ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he
  simpa only [List.map_set] using assignLocalArrayIndex hd hi (by simpa only [List.length_map] using hib)

end Benchmarks.EAS.EAS
