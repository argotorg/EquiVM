import Benchmarks.CompoundIII.Comet.TotalsStorage
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def presentValueWord (index principal : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul principal index) ⟨1000000000000000⟩

theorem presentValue_mul_lt {index principal : UInt256}
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^104) :
    principal.toNat * index.toNat < 2^168 := by
  calc
    _ < 2^104 * 2^64 := Nat.mul_lt_mul_of_lt_of_lt hp hi
    _ = 2^168 := by decide

theorem presentValueWord_lt {index principal : UInt256}
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^104) :
    (presentValueWord index principal).toNat < 2^168 := by
  have hmul := presentValue_mul_lt hi hp
  unfold presentValueWord
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt (lt_trans hmul (by decide))]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hmul

def presentValueName (borrow : Bool) : Ident :=
  if borrow then "presentValueBorrow" else "presentValueSupply"

def presentValueIndexName (borrow : Bool) : Ident :=
  if borrow then "baseBorrowIndex_" else "baseSupplyIndex_"

def presentValueLocals (borrow : Bool) (index principal : UInt256) : Store :=
  ((∅ : Store).insert "principalValue_" (.int principal.toNat)).insert
    (presentValueIndexName borrow) (.int index.toNat)

def presentValueCallable (borrow : Bool) : CallableDecl :=
  { params := [⟨presentValueIndexName borrow, .elem (.int (.uint ⟨64, by decide⟩))⟩,
      ⟨"principalValue_", .elem (.int (.uint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := [.return [.binary .div
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul
        (.cast (.var "principalValue_") (.elem (.int (.uint ⟨256, by decide⟩))))
        (.var (presentValueIndexName borrow)))) (.intLit 1000000000000000)]] }

theorem presentValueCallable_lookup (borrow : Bool) :
    lookupCallable? contract (presentValueName borrow) = some (presentValueCallable borrow) := by
  cases borrow <;> rfl

theorem presentValueCallable_returns (evm : EVM.State) (imms : Store)
    (borrow : Bool) (index principal : UInt256)
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^104) :
    ExecFuncBody config
      { contract := contract, locals := presentValueLocals borrow index principal, immutables := imms }
      evm (presentValueCallable borrow).body
      (.returned
        { contract := contract, locals := presentValueLocals borrow index principal, immutables := imms }
        evm (some [.int (presentValueWord index principal).toNat])) := by
  let frame : Frame :=
    { contract := contract, locals := presentValueLocals borrow index principal, immutables := imms }
  have heI : evalExpr? config frame evm (.var (presentValueIndexName borrow)) =
      .ok (.int (Int.ofNat index.toNat)) := by
    simp only [evalExpr?, frame, presentValueLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_self_eq_true, if_true, EvalResult.ofOption]
    rfl
  have heP : evalExpr? config frame evm (.var "principalValue_") =
      .ok (.int (Int.ofNat principal.toNat)) := by
    cases borrow <;>
      simp only [evalExpr?, frame, presentValueLocals, presentValueIndexName,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption] <;> rfl
  have heCast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) heP
  rw [normalizeInt_uint256_word] at heCast
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply divSourceOk (b := ⟨1000000000000000⟩)
  · exact checkedMulSourceOk heCast heI (lt_trans (presentValue_mul_lt hi hp) (by decide))
  · norm_num [evalExpr?, pure, UInt256.toNat, UInt256.size]
  · decide

theorem presentValue_call (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (index principal : UInt256) (indexExpr principalExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract)
    (hi : index.toNat < 2^64) (hp : principal.toNat < 2^104)
    (heI : evalExpr? config frame evm indexExpr = .ok (.int index.toNat))
    (heP : evalExpr? config frame evm principalExpr = .ok (.int principal.toNat)) :
    ExecStmt config frame evm
      (.internalCall (presentValueName borrow) [indexExpr, principalExpr] ret)
      (.ok { frame with
        locals := frame.locals.insert ret (.int (presentValueWord index principal).toNat) } evm) := by
  exact ExecStmt.internalCallReturn (callee := presentValueCallable borrow)
    (locals := presentValueLocals borrow index principal)
    (cfg := config) (solm := frame) (evm := evm)
    (args := [indexExpr, principalExpr]) (argVals := [.int index.toNat, .int principal.toNat])
    (by simp only [evalExprs?, heI, heP, pure, bind, EvalResult.bind])
    (by rw [hc]; exact presentValueCallable_lookup borrow)
    (by cases borrow <;> rfl)
    (by simpa only [hc] using presentValueCallable_returns evm frame.immutables borrow index principal hi hp)

end Benchmarks.CompoundIII.Comet
