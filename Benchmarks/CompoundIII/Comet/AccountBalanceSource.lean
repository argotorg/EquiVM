import Benchmarks.CompoundIII.Comet.CurrentIndicesSource
import Benchmarks.CompoundIII.Comet.UserBasicFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def accountBalanceEntry (v : CometWithExtendedAssetListImmutables)
    (addr : AccountAddress) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "account" (.address addr),
    immutables := immStore v }

def accountBalanceRead (borrow : Bool) : List Stmt :=
  [.letDecl (indexLocalName borrow) (some (.elem (.int (.uint ⟨64, by decide⟩))))
      (.tupleGet (.var "__c1") (if borrow then 1 else 0)),
    .letDecl "principal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
      (.storage ⟨"userBasic", [.mindex (.var "account"), .field "principal"]⟩)]

def accountBalanceFrame (v : CometWithExtendedAssetListImmutables)
    (addr : AccountAddress) (borrow : Bool) (w0 w1 time basic : UInt256) : Frame :=
  let f := currentIndicesFrame (accountBalanceEntry v addr) v w0 w1 time
  { f with locals := (f.locals.insert (indexLocalName borrow)
      (.int (currentIndex v w0 w1 time borrow).toNat)).insert "principal" (.int (signed104 basic)) }

theorem accountBalancePrefix (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (addr : AccountAddress) (borrow : Bool)
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)
    ExecBlock config (accountBalanceEntry v addr) evm (currentIndicesBlock ++ accountBalanceRead borrow)
      (.ok (accountBalanceFrame v addr borrow w0 w1 time basic) evm) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr)
  let f0 := accountBalanceEntry v addr
  let f1 := currentIndicesFrame f0 v w0 w1 time
  let f2 : Frame :=
    { f1 with
      locals := f1.locals.insert (indexLocalName borrow)
        (.int (currentIndex v w0 w1 time borrow).toNat) }
  have hpref := currentIndicesBlock_result v f0 evm rfl rfl (by simp [f0, accountBalanceEntry])
  dsimp only at hpref
  rw [if_pos hv] at hpref
  have heidx : evalExpr? config f1 evm (.tupleGet (.var "__c1") (if borrow then 1 else 0)) =
      .ok (.int (currentIndex v w0 w1 time borrow).toNat) := by
    cases borrow <;> simp only [evalExpr?, f1, currentIndicesFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind] <;> rfl
  have hebasic : evalExpr? config f2 evm
      (.storage ⟨"userBasic", [.mindex (.var "account"), .field "principal"]⟩) =
      .ok (.int (signed104 basic)) := by
    exact evalUserBasicPrincipalOf evm f2.locals (immStore v) addr (.var "account")
      (by cases borrow <;> simp [f2, f1, currentIndicesFrame, f0, accountBalanceEntry, indexLocalName])
      (by
        cases borrow <;>
          simp only [evalExpr?, f2, f1, currentIndicesFrame, f0, accountBalanceEntry,
            indexLocalName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            EvalResult.ofOption] <;> rfl)
  apply execBlockAppendOk hpref
  exact ExecBlock.consNormal (ExecStmt.letDecl heidx)
    (ExecBlock.consNormal (ExecStmt.letDecl hebasic) ExecBlock.nil)

theorem accountBalancePrincipalEval (v : CometWithExtendedAssetListImmutables)
    (addr : AccountAddress) (borrow : Bool) (w0 w1 time basic : UInt256) (evm : EVM.State) :
    evalExpr? config (accountBalanceFrame v addr borrow w0 w1 time basic) evm (.var "principal") =
      .ok (.int (signed104 basic)) := by
  simp only [evalExpr?, accountBalanceFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rfl

theorem accountBalanceIndexGet (v : CometWithExtendedAssetListImmutables)
    (addr : AccountAddress) (borrow : Bool) (w0 w1 time basic : UInt256) :
    (accountBalanceFrame v addr borrow w0 w1 time basic).locals.get? (indexLocalName borrow) =
      some (.int (currentIndex v w0 w1 time borrow).toNat) := by
  cases borrow <;> simp only [accountBalanceFrame, indexLocalName, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

end Benchmarks.CompoundIII.Comet
