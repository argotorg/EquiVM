import Examples.Ripemd160.SolmHelpers

/-!
# RIPEMD-160 Solm internal calls

Caller-side wrappers for the authored helper functions.  These lemmas only compose ordinary
`ExecStmt.internalCall` executions with the helper body proofs in `SolmHelpers`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace Ripemd160

abbrev natValue (n : Nat) : Value := .int (Int.ofNat n)

theorem evalNatVar {L : Store} {evm : EVM.State} {name : Ident} {n : Nat}
    (h : L.get? name = some (natValue n)) :
    evalExpr? config { contract := contract, locals := L } evm (.var name) = .ok (natValue n) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [h]

theorem evalNatAdd {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .add a b) =
      .ok (natValue (x + y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  norm_num

theorem evalNatMul {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .mul a b) =
      .ok (natValue (x * y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  norm_num

theorem evalNatDiv {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat} (hy : y ≠ 0)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .div a b) =
      .ok (natValue (x / y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  rw [if_neg (by simpa using hy)]
  norm_num

theorem evalNatMod {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat} (hy : y ≠ 0)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .mod a b) =
      .ok (natValue (x % y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  rw [if_neg (by simpa using hy)]
  norm_num

theorem evalNatLt {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .lt a b) =
      .ok (.bool (decide (x < y))) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  simp

theorem evalNatEq {L : Store} {evm : EVM.State} {a b : Expr} {x y : Nat}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (natValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (natValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .eq a b) =
      .ok (.bool (decide (x = y))) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, natValue]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [decide_eq_false hxy]
    congr 2
    rw [beq_eq_false_iff_ne]
    intro hvalue
    rw [Value.int.injEq] at hvalue
    exact hxy (Int.ofNat.inj hvalue)

theorem paddedByteCall {L : Store} (evm : EVM.State) (data : ByteArray) (pos : Nat)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hpos : pos < Model.paddedLength data.size)
    (hdata : L.get? "data" = some (.bytes data))
    (hposVar : evalExpr? config { contract := contract, locals := L } evm posExpr =
      .ok (natValue pos))
    (hbit : L.get? "bitLen" = some (natValue (data.size * 8)))
    (hpad : L.get? "paddedLen" = some (natValue (Model.paddedLength data.size))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "paddedByte"
        [.var "data", posExpr, .var "bitLen", .var "paddedLen"] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (natValue (Model.paddedByte data pos))) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm
      [.var "data", posExpr, .var "bitLen", .var "paddedLen"] =
      .ok [.bytes data, natValue pos, natValue (data.size * 8),
        natValue (Model.paddedLength data.size)] := by
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hdata, hposVar,
      hbit, hpad, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "paddedByte" =
      some paddedByteFunction.toCallable := by rfl
  have hbind : bindParams? paddedByteFunction.params
      [.bytes data, natValue pos, natValue (data.size * 8),
        natValue (Model.paddedLength data.size)] =
      some (paddedLocals data pos (data.size * 8) (Model.paddedLength data.size)) := by
    rfl
  have hbody := paddedByteBodyReturns evm data pos hsmall hpos
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := "paddedByte") (retVar := retVar)
    (args := [.var "data", posExpr, .var "bitLen", .var "paddedLen"])
    (argVals := [.bytes data, natValue pos, natValue (data.size * 8),
      natValue (Model.paddedLength data.size)])
    (callee := paddedByteFunction)
    (value := some [natValue (Model.paddedByte data pos)]) hargs hlookup hbind hbody
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem rotl32Call {L : Store} (evm : EVM.State) (x : UInt256) (n : Nat)
    (hx : x.toNat < 2 ^ 32) (hn : n < 16)
    (hxEval : evalExpr? config { contract := contract, locals := L } evm xExpr =
      .ok (wordValue x))
    (hnEval : evalExpr? config { contract := contract, locals := L } evm nExpr =
      .ok (wordValue (UInt256.ofNat n))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "rotl32" [xExpr, nExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (wordValue (runtimeRol32 x (UInt256.ofNat n)))) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm [xExpr, nExpr] =
      .ok [wordValue x, wordValue (UInt256.ofNat n)] := by
    simp only [evalExprs?, hxEval, hnEval, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "rotl32" = some rotl32Function.toCallable := by rfl
  have hbind : bindParams? rotl32Function.params
      [wordValue x, wordValue (UInt256.ofNat n)] = some (xnLocals x n) := by rfl
  have hbody := rotl32BodyReturns evm x n hn
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := "rotl32") (retVar := retVar)
    (args := [xExpr, nExpr]) (argVals := [wordValue x, wordValue (UInt256.ofNat n)])
    (callee := rotl32Function) (value := some [wordValue (runtimeRol32 x (UInt256.ofNat n))])
    hargs hlookup hbind hbody
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem swap32Call {L : Store} (evm : EVM.State) (x : UInt256)
    (hx : x.toNat < 2 ^ 32)
    (hxEval : evalExpr? config { contract := contract, locals := L } evm xExpr =
      .ok (wordValue x)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "swap32" [xExpr] retVar)
      (.ok { contract := contract, locals :=
        L.insert retVar (wordValue (runtimeSwap32 x)) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm [xExpr] =
      .ok [wordValue x] := by
    simp only [evalExprs?, hxEval, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "swap32" = some swap32Function.toCallable := by
    rfl
  have hbind : bindParams? swap32Function.params [wordValue x] = some (xLocals x) := by
    rfl
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := "swap32") (retVar := retVar)
    (args := [xExpr]) (argVals := [wordValue x]) (callee := swap32Function)
    (value := some [wordValue (runtimeSwap32 x)]) hargs hlookup hbind
    (swap32BodyReturns evm x hx)
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem nibbleCall {L : Store} (evm : EVM.State) (row : UInt256) (idx : Nat)
    (hi : idx < 16)
    (hrow : evalExpr? config { contract := contract, locals := L } evm rowExpr =
      .ok (wordValue row))
    (hidx : evalExpr? config { contract := contract, locals := L } evm idxExpr =
      .ok (wordValue (UInt256.ofNat idx))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "nibble" [rowExpr, idxExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (wordValue (runtimeRowEntry row (UInt256.ofNat idx)))) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm
      [rowExpr, idxExpr] = .ok [wordValue row, wordValue (UInt256.ofNat idx)] := by
    simp only [evalExprs?, hrow, hidx, EvalResult.bind, bind, pure]
  have hlookup : lookupCallable? contract "nibble" = some nibbleFunction.toCallable := by rfl
  have hbind : bindParams? nibbleFunction.params
      [wordValue row, wordValue (UInt256.ofNat idx)] = some (rowIndexLocals row idx) := by rfl
  have hbody := nibbleBodyReturns evm row idx hi
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := "nibble") (retVar := retVar)
    (args := [rowExpr, idxExpr]) (argVals := [wordValue row, wordValue (UInt256.ofNat idx)])
    (callee := nibbleFunction)
    (value := some [wordValue (runtimeRowEntry row (UInt256.ofNat idx))])
    hargs hlookup hbind hbody
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem rowCall {L : Store} (evm : EVM.State) (g : Nat) (hg : g < 5)
    (name : Ident) (retVar : Ident) (callee : FunctionDecl) (result : Nat)
    (harg : evalExpr? config { contract := contract, locals := L } evm gExpr =
      .ok (natValue g))
    (hlookup : lookupCallable? contract name = some callee.toCallable)
    (hbind : bindParams? callee.params [natValue g] = some (gLocals g))
    (hbody : ExecFuncBody config { contract := contract, locals := gLocals g } evm callee.body
      (.returned { contract := contract, locals := gLocals g } evm
        (some [natValue result]))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall name [gExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (natValue result)) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm [gExpr] =
      .ok [natValue g] := by simp only [evalExprs?, harg, EvalResult.bind, bind, pure]
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := name) (retVar := retVar)
    (args := [gExpr]) (argVals := [natValue g]) (callee := callee)
    (value := some [natValue result]) hargs hlookup hbind hbody
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem wordRowLCall {L : Store} (evm : EVM.State) (g : Nat) (hg : g < 5)
    (harg : evalExpr? config { contract := contract, locals := L } evm gExpr =
      .ok (natValue g)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "wordRowL" [gExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (natValue (Model.leftWordRow g))) } evm) := by
  exact rowCall evm g hg "wordRowL" retVar wordRowLFunction (Model.leftWordRow g)
    harg rfl rfl (wordRowLBodyReturns evm g hg)

theorem rotRowLCall {L : Store} (evm : EVM.State) (g : Nat) (hg : g < 5)
    (harg : evalExpr? config { contract := contract, locals := L } evm gExpr =
      .ok (natValue g)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "rotRowL" [gExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (natValue (Model.leftRotationRow g))) } evm) := by
  exact rowCall evm g hg "rotRowL" retVar rotRowLFunction (Model.leftRotationRow g)
    harg rfl rfl (rotRowLBodyReturns evm g hg)

theorem wordRowRCall {L : Store} (evm : EVM.State) (g : Nat) (hg : g < 5)
    (harg : evalExpr? config { contract := contract, locals := L } evm gExpr =
      .ok (natValue g)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "wordRowR" [gExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (natValue (Model.rightWordRow g))) } evm) := by
  exact rowCall evm g hg "wordRowR" retVar wordRowRFunction (Model.rightWordRow g)
    harg rfl rfl (wordRowRBodyReturns evm g hg)

theorem rotRowRCall {L : Store} (evm : EVM.State) (g : Nat) (hg : g < 5)
    (harg : evalExpr? config { contract := contract, locals := L } evm gExpr =
      .ok (natValue g)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "rotRowR" [gExpr] retVar)
      (.ok { contract := contract, locals :=
        (L.insert retVar (natValue (Model.rightRotationRow g))) } evm) := by
  exact rowCall evm g hg "rotRowR" retVar rotRowRFunction (Model.rightRotationRow g)
    harg rfl rfl (rotRowRBodyReturns evm g hg)

theorem booleanCall {L : Store} (evm : EVM.State) (name retVar : Ident)
    (callee : FunctionDecl) (x y z result : UInt256)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z))
    (hlookup : lookupCallable? contract name = some callee.toCallable)
    (hbind : bindParams? callee.params [wordValue x, wordValue y, wordValue z] =
      some (xyzLocals x y z))
    (hbody : ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm callee.body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue result]))) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall name [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (wordValue result)) } evm) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm
      [xExpr, yExpr, zExpr] = .ok [wordValue x, wordValue y, wordValue z] := by
    simp only [evalExprs?, hx, hy, hz, EvalResult.bind, bind, pure]
  have hcall := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := L })
    (evm := evm) (calleeEvm := evm) (name := name) (retVar := retVar)
    (args := [xExpr, yExpr, zExpr]) (argVals := [wordValue x, wordValue y, wordValue z])
    (callee := callee) (value := some [wordValue result]) hargs hlookup hbind hbody
  simpa [resumeAfterInternalCall, collapseReturns] using hcall

theorem f0Call {L : Store} (evm : EVM.State) (x y z : UInt256)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "f0" [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar
        (wordValue (UInt256.xor (UInt256.xor x y) z))) } evm) := by
  exact booleanCall evm "f0" retVar f0Function x y z _ hx hy hz rfl rfl
    (f0BodyReturns evm x y z)

theorem f1Call {L : Store} (evm : EVM.State) (x y z : UInt256) (hx32 : x.toNat < 2 ^ 32)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "f1" [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (wordValue
        (UInt256.lor (UInt256.land x y) (UInt256.land (UInt256.lnot x) z)))) } evm) := by
  exact booleanCall evm "f1" retVar f1Function x y z _ hx hy hz rfl rfl
    (f1BodyReturns evm x y z hx32)

theorem f2Call {L : Store} (evm : EVM.State) (x y z : UInt256) (hy32 : y.toNat < 2 ^ 32)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "f2" [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (wordValue
        (UInt256.xor (UInt256.lor x (UInt256.lnot y)) z))) } evm) := by
  exact booleanCall evm "f2" retVar f2Function x y z _ hx hy hz rfl rfl
    (f2BodyReturns evm x y z hy32)

theorem f3Call {L : Store} (evm : EVM.State) (x y z : UInt256) (hz32 : z.toNat < 2 ^ 32)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "f3" [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (wordValue
        (UInt256.lor (UInt256.land x z) (UInt256.land y (UInt256.lnot z))))) } evm) := by
  exact booleanCall evm "f3" retVar f3Function x y z _ hx hy hz rfl rfl
    (f3BodyReturns evm x y z hz32)

theorem f4Call {L : Store} (evm : EVM.State) (x y z : UInt256) (hz32 : z.toNat < 2 ^ 32)
    (hx : evalExpr? config { contract := contract, locals := L } evm xExpr = .ok (wordValue x))
    (hy : evalExpr? config { contract := contract, locals := L } evm yExpr = .ok (wordValue y))
    (hz : evalExpr? config { contract := contract, locals := L } evm zExpr = .ok (wordValue z)) :
    ExecStmt config { contract := contract, locals := L } evm
      (.internalCall "f4" [xExpr, yExpr, zExpr] retVar)
      (.ok { contract := contract, locals := (L.insert retVar (wordValue
        (UInt256.xor x (UInt256.lor y (UInt256.lnot z))))) } evm) := by
  exact booleanCall evm "f4" retVar f4Function x y z _ hx hy hz rfl rfl
    (f4BodyReturns evm x y z hz32)

end Ripemd160
