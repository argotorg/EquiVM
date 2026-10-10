import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_020
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

def boolWord (b : Bool) : UInt256 := if b then ⟨1⟩ else ⟨0⟩

-- LIBRARY CANDIDATE: connect canonical ABI bool words and their source values.
def BoolCanonical (w : UInt256) : Prop := w = ⟨0⟩ ∨ w = ⟨1⟩

instance (w : UInt256) : Decidable (BoolCanonical w) := inferInstanceAs (Decidable (_ ∨ _))

theorem boolWord_of_canonical {w : UInt256} (hc : BoolCanonical w) :
    boolWord (decide (w ≠ ⟨0⟩)) = w := by
  rcases hc with rfl | rfl <;> decide

theorem decodeScalarWord_bool_result {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem .bool) bytes start =
      if BoolCanonical (ABI.bytesToWord ((bytes.drop start).take 32)) then
        some (.bool (decide (ABI.bytesToWord ((bytes.drop start).take 32) ≠ ⟨0⟩)), start + 32)
      else none := by
  by_cases hz : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨0⟩
  · rw [decodeScalarWord_bool_ok_zero hlen hz,
      if_pos (show BoolCanonical _ from Or.inl hz), hz]
    rfl
  · by_cases ho : ABI.bytesToWord ((bytes.drop start).take 32) = ⟨1⟩
    · rw [decodeScalarWord_bool_ok_one hlen ho,
        if_pos (show BoolCanonical _ from Or.inr ho), ho]
      rfl
    · rw [decodeScalarWord_bool_none_noncanon hlen hz ho,
        if_neg (by simpa only [BoolCanonical, not_or] using And.intro hz ho)]

set_option maxRecDepth 10000

theorem cometDecodeBool {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {off ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨3348⟩ (off :: ret :: R) mem aw rdata σ k C) :
    if BoolCanonical (calldataWord ee.calldata off.toNat) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (calldataWord ee.calldata off.toNat :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hc : BoolCanonical (calldataWord ee.calldata off.toNat)
  · rw [if_pos hc]
    have hclean := (boolWordClean_iff _).mpr hc
    have rd1 := cometWithExtendedAssetList_block_3348_fallthrough
      (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.sub _ _ = ⟨0⟩; rw [hclean, u256_sub_self]) h
    have rd2 := cometWithExtendedAssetList_block_3360
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret rd1
    exact ⟨_, _, rd2⟩
  · rw [if_neg hc]
    have hne : calldataWord ee.calldata off.toNat ≠
        UInt256.isZero (UInt256.isZero (calldataWord ee.calldata off.toNat)) := by
      intro he
      exact hc ((boolWordClean_iff _).mp he.symm)
    have rd1 := cometWithExtendedAssetList_block_3348_taken
      (immWords := wordsOf (immStore v)) hstack (u256_sub_ne_zero_of_ne hne)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) rd1

def toUInt8Callable : CallableDecl :=
  { params := [⟨"x", .elem .bool⟩], returnType := [.elem (.int (.uint ⟨8, by decide⟩))]
    body := [.return [.ite (.var "x") (.intLit 1) (.intLit 0)]] }

theorem cometDecodeBool_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {off ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hc : BoolCanonical (calldataWord ee.calldata off.toNat))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨3348⟩ (off :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (calldataWord ee.calldata off.toNat :: R) mem aw rdata σ k' C' := by
  have hr := cometDecodeBool (v := v) hstack hret h
  rwa [if_pos hc] at hr

theorem cometDecodeBool_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {off ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hc : ¬ BoolCanonical (calldataWord ee.calldata off.toNat))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨3348⟩ (off :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hr := cometDecodeBool (v := v) hstack hret h
  rwa [if_neg hc] at hr

theorem toUInt8Callable_lookup : lookupCallable? contract "toUInt8" = some toUInt8Callable := rfl

theorem toUInt8_call (frame : Frame) (evm : EVM.State) (arg : Expr) (ret : Ident) (b : Bool)
    (hc : frame.contract = contract) (he : evalExpr? config frame evm arg = .ok (.bool b)) :
    ExecStmt config frame evm (.internalCall "toUInt8" [arg] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int (boolWord b).toNat) } evm) := by
  have hb : ExecFuncBody config
      { frame with locals := (∅ : Store).insert "x" (.bool b) } evm toUInt8Callable.body
      (.returned { frame with locals := (∅ : Store).insert "x" (.bool b) }
        evm (some [.int (boolWord b).toNat])) := by
    apply ExecFuncBody.execBlockRet
    apply ABlock.start.returns
    cases b <;> simp [boolWord, evalExpr?, EvalResult.ofOption, pure,
      bind, EvalResult.bind] <;> rfl
  exact ExecStmt.internalCallReturn (callee := toUInt8Callable)
    (evalExprs?_singleton he) (by rw [hc]; exact toUInt8Callable_lookup) rfl hb

theorem cometToUInt8 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256} (b : Bool)
    (hstack : R.length + 4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11118⟩
      (boolWord b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (boolWord b :: R) mem aw rdata σ k' C' := by
  cases b with
  | false =>
      have rd1 := cometWithExtendedAssetList_block_11118_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := cometWithExtendedAssetList_block_2425 (immWords := wordsOf (immStore v))
        (by omega) hret rd1
      exact ⟨_, _, rd2⟩
  | true =>
      have rd1 := cometWithExtendedAssetList_block_11118_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by decide) h
      have rd2 := cometWithExtendedAssetList_block_11127 (immWords := wordsOf (immStore v))
        (by omega) hret rd1
      exact ⟨_, _, rd2⟩

end Benchmarks.CompoundIII.Comet
