import Benchmarks.CompoundIII.Comet.PrincipalWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def unsigned104Callable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.sint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨104, by decide⟩))]
    body := [.require (.binary .ge (.var "n") (.intLit 0)),
      .return [.cast (.var "n") (.elem (.int (.uint ⟨104, by decide⟩)))]] }

theorem unsigned104Callable_lookup :
    lookupCallable? contract "unsigned104" = some unsigned104Callable := rfl

theorem unsigned104Callable_returns (evm : EVM.State) (imms : Store)
    (n : UInt256) (hn : n.toNat < 2^104) :
    let frame : Frame :=
      { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
    ExecFuncBody config frame evm unsigned104Callable.body
      (.returned frame evm (some [.int n.toNat])) := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
  have he : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hc : evalExpr? config frame evm (.binary .ge (.var "n") (.intLit 0)) =
      .ok (.bool true) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    simp
  apply ExecFuncBody.execBlockRet
  apply (ABlock.start.requireStep hc).returns
  have hn' : normalizeInt (.uint ⟨104, by decide⟩) (Int.ofNat n.toNat) = Int.ofNat n.toNat :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (by
      change (n.toNat : Int) < (2^104 : Nat)
      exact_mod_cast hn)
  have hcast := evalExpr_cast_int (intType := .uint ⟨104, by decide⟩) he
  rw [hn'] at hcast
  exact hcast

theorem unsigned104_call (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n.toNat)) (hn : n.toNat < 2^104) :
    ExecStmt config frame evm (.internalCall "unsigned104" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int n.toNat) } evm) := by
  exact ExecStmt.internalCallReturn (callee := unsigned104Callable)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int n.toNat])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact unsigned104Callable_lookup) rfl
    (by simpa only [hc] using unsigned104Callable_returns evm frame.immutables n hn)

theorem cometUnsigned104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {n ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hn : n.toNat < 2^103)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17913⟩ (n :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_17913_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by
      rw [signextend104_low hn]
      exact slt_lit_zero (by decide) (Nat.zero_le _) (lt_trans hn (by decide))) h
  have r2 := cometWithExtendedAssetList_block_17925
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hvalid r1
  simp only [cometWithExtendedAssetList_block_17925_stack] at r2
  rw [u256_land_comm, u256LandMaskCleanOfToNat _ _ (bits := 104) rfl
    (lt_trans hn (by decide))] at r2
  exact ⟨_, _, r2⟩

end Benchmarks.CompoundIII.Comet
