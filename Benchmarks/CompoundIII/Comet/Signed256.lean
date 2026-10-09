import Benchmarks.CompoundIII.Comet.PrincipalWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_048

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def signed256Callable : CallableDecl :=
  { params := [⟨"n", abiUInt256⟩]
    returnType := [.elem (.int (.sint ⟨256, by decide⟩))]
    body := [.require (.binary .le (.var "n")
      (.cast (.intLit (2^255 - 1)) (.elem (.int (.uint ⟨256, by decide⟩))))),
      .return [.cast (.var "n") (.elem (.int (.sint ⟨256, by decide⟩)))]] }

theorem signed256Callable_lookup :
    lookupCallable? contract "signed256" = some signed256Callable := rfl

theorem signed256Callable_result (evm : EVM.State) (imms : Store) (n : UInt256) :
    let frame : Frame :=
      { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
    if n.toNat < 2^255 then
      ExecFuncBody config frame evm signed256Callable.body
        (.returned frame evm (some [.int n.toNat]))
    else ExecFuncBody config frame evm signed256Callable.body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
  have he : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hc : evalExpr? config frame evm
      (.binary .le (.var "n") (.cast (.intLit (2^255 - 1)) (.elem (.int (.uint ⟨256, by decide⟩))))) =
      .ok (.bool (decide (n.toNat < 2^255))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, castValue?, abiUInt256,
      normalizeInt, evalBinaryOp?, EvalResult.ofOption]
    congr 3
    change ((n.toNat : Int) ≤ 2^255 - 1) = (n.toNat < 2^255)
    apply propext
    omega
  split_ifs with hn
  · apply ExecFuncBody.execBlockRet
    apply (ABlock.start.requireStep (hc.trans (by rw [decide_eq_true hn]))).returns
    have hcast := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) he
    rw [normalizeInt_sint256_word_of_lt n hn] at hcast
    exact hcast
  · apply ExecFuncBody.execBlockRevert
    exact ABlock.start.requireRevert (hc.trans (by rw [decide_eq_false hn]))

theorem signed256_call_ok (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n.toNat)) (hn : n.toNat < 2^255) :
    ExecStmt config frame evm (.internalCall "signed256" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int n.toNat) } evm) := by
  have hb := signed256Callable_result evm frame.immutables n
  dsimp only at hb
  rw [if_pos hn] at hb
  exact ExecStmt.internalCallReturn (callee := signed256Callable)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int n.toNat])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact signed256Callable_lookup) rfl (by simpa only [hc] using hb)

theorem signed256_call_revert (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n.toNat)) (hn : ¬ n.toNat < 2^255) :
    ExecStmt config frame evm (.internalCall "signed256" [expr] ret) .reverted := by
  have hb := signed256Callable_result evm frame.immutables n
  dsimp only at hb
  rw [if_neg hn] at hb
  exact ExecStmt.internalCallRevert (callee := signed256Callable)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int n.toNat])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact signed256Callable_lookup) rfl (by simpa only [hc] using hb)

theorem cometSigned256 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hn : n.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10129⟩ (n :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_10129_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (ugt_zero (by change n.toNat ≤ 2^255 - 1; omega)) h
  exact ⟨_, _, cometWithExtendedAssetList_block_10144
    (immWords := wordsOf (immStore v)) (by omega) hret r1⟩

theorem cometSigned256_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hn : ¬ n.toNat < 2^255)
    (h : RD (deployedRuntime v) ee g s0 ⟨10129⟩ (n :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_10129_taken
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [ugt_one (by change 2^255 - 1 < n.toNat; omega)]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometWithExtendedAssetList_block_10146
    (immWords := wordsOf (immStore v)) (by simpa using hstack) r1

end Benchmarks.CompoundIII.Comet
