import Benchmarks.Morpho.MorphoBlue.ExtSloadsSourceStep
import Benchmarks.EAS.Attester.WordArrayABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem extSloadsSourceLoop (evm : EVM.State) (imms : Store) (slots : List Value)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots)
    (hn : slots.length < UInt256.size) (remaining : Nat) :
    ∀ locals res i, ExtSloadsLocals slots res i locals → i + remaining = slots.length →
      res.length = slots.length →
      (∀ j, j < i → res[j]? = some (wordBytes32Value (extSloadsValue evm j))) →
      ∃ locals', ExecStmt config { contract := contract, locals := locals, immutables := imms }
        evm (.while extSloadsCond extSloadsLoopBody)
        (.ok { contract := contract, locals := locals', immutables := imms } evm) ∧
        locals'.get? "res" = some (.array (wordArrayValues (extSloadsValue evm) 0 slots.length)) := by
  induction remaining with
  | zero =>
      intro locals res i hl hi hr hp
      have hin : i = slots.length := by omega
      have he : res = wordArrayValues (extSloadsValue evm) 0 slots.length := by
        apply List.ext_getElem?
        intro j
        by_cases hj : j < slots.length
        · rw [hp j (by omega), wordArrayValues_getElem _ _ _ _ hj, Nat.zero_add]
        · rw [List.getElem?_eq_none (by omega),
            List.getElem?_eq_none (by rw [wordArrayValues_length]; omega)]
      refine ⟨locals, .whileFalse ?_, ?_⟩
      · simpa only [extSloadsCond, hin, lt_self_iff_false, decide_false]
          using evalLocalNatLt (cfg := config) (evm := evm)
            (solm := { contract := contract, locals := locals, immutables := imms })
            hl.index_eq hl.count_eq
      · simpa only [he] using hl.result_eq
  | succ remaining ih =>
      intro locals res i hl hi hr hp
      obtain ⟨next, hs, hl'⟩ := extSloadsLoopStep evm locals imms slots res i hl (by omega)
        hr (by omega) hd
      have hp' : ∀ j, j < i + 1 →
          (res.set i (wordBytes32Value (extSloadsValue evm i)))[j]? =
            some (wordBytes32Value (extSloadsValue evm j)) := by
        intro j hj
        by_cases he : i = j
        · subst j; exact List.getElem?_set_self (by omega)
        · rw [List.getElem?_set_ne he]
          exact hp j (by omega)
      obtain ⟨last, hw, hlast⟩ := ih next _ (i + 1) hl' (by omega)
        (by simpa only [List.length_set] using hr) hp'
      refine ⟨last, .whileTrue ?_ hs hw, hlast⟩
      simpa only [extSloadsCond, show i < slots.length by omega, decide_true]
        using evalLocalNatLt (cfg := config) (evm := evm)
          (solm := { contract := contract, locals := locals, immutables := imms })
          hl.index_eq hl.count_eq

def extSloadsArgs (slots : List Value) : Store := (∅ : Store).insert "slots" (.array slots)
def extSloadsCountFrame (slots : List Value) (cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, locals := ((extSloadsArgs slots).insert "__calldata" (.bytes cd)).insert
      "nSlots" (.int (Int.ofNat slots.length)), immutables := imms }

def extSloadsAllocationGuard : Expr := .binary .le
  (.binary .add (.intLit 128)
    (.binary .mul (.intLit 32) (.binary .add (.var "nSlots") (.intLit 1))))
  (.binary .sub (.binary .exp (.intLit 2) (.intLit 64)) (.intLit 1))

theorem extSloadsAllocationGuard_eval {frame : Frame} {evm : EVM.State} {n : Nat}
    (hn : frame.locals.get? "nSlots" = some (.int (Int.ofNat n))) :
    evalExpr? config frame evm extSloadsAllocationGuard =
      .ok (.bool (decide (128 + 32 * (n + 1) ≤ solcMaxU64))) := by
  simp only [extSloadsAllocationGuard, evalExpr?, hn, EvalResult.ofOption,
    bind, pure, EvalResult.bind, evalBinaryOp?]
  norm_num [Int.toNat, solcMaxU64]
  omega

theorem extSloadsSourcePrelude (slots : List Value) (evm : EVM.State) (imms : Store)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) :
    ABlock config evm { contract := contract, locals := extSloadsArgs slots, immutables := imms }
      extSloadsTransition.body (extSloadsCountFrame slots evm.executionEnv.calldata imms)
      (extSloadsTransition.body.drop 5) := by
  have hn : slots.length ≤ solcMaxU64 := by rw [hd.length]; exact hd.bounds.2.2.2.2.1
  have hprefix : ABlock config evm
      { contract := contract, locals := extSloadsArgs slots, immutables := imms }
      extSloadsTransition.body (extSloadsCountFrame slots evm.executionEnv.calldata imms)
      (extSloadsTransition.body.drop 4) :=
    (calldataPrelude_ok hcv (by have := hd.bounds.2.1; omega)).letStep
      (evalLocalArrayLength (by
        simp only [extSloadsArgs, store_get_ne (k := "__calldata") (a := "slots") _ _ (by decide),
          store_get_self]))
  apply ABlock.requireStep hprefix
  change evalExpr? config (extSloadsCountFrame slots evm.executionEnv.calldata imms) evm
    (.binary .le (.var "nSlots")
      (.binary .sub (.binary .exp (.intLit 2) (.intLit 64)) (.intLit 1))) = _
  simp only [evalExpr?, extSloadsCountFrame, store_get_self, EvalResult.ofOption,
    bind, pure, EvalResult.bind, evalBinaryOp?]
  norm_num [solcMaxU64, Int.toNat] at hn ⊢
  omega

theorem morphoExtSloadsSource (slots : List Value) (evm : EVM.State) (imms : Store)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : 128 + 32 * (slots.length + 1) ≤ solcMaxU64) :
    ∃ frame, ExecTransitionBody config contract evm (extSloadsArgs slots) extSloadsTransition.body
      (.returned frame evm (some [.array (wordArrayValues (extSloadsValue evm) 0 slots.length)]))
      imms := by
  let f := extSloadsCountFrame slots evm.executionEnv.calldata imms
  let res := List.replicate slots.length (wordBytes32Value ⟨0⟩)
  let loopLocals := (f.locals.insert "res" (.array res)).insert "i" (.int 0)
  have hn : slots.length < UInt256.size := by
    have hb := hd.bounds.2.2.2.2.1
    rw [← hd.length] at hb
    norm_num [solcMaxU64, UInt256.size] at hb ⊢
    omega
  have hl : ExtSloadsLocals slots res 0 loopLocals := by
    constructor <;>
      simp [loopLocals, f, extSloadsCountFrame, extSloadsArgs, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  obtain ⟨last, hloop, hlast⟩ := extSloadsSourceLoop evm imms slots hd hn slots.length
    loopLocals res 0 hl (by omega) (List.length_replicate ..) (by omega)
  refine ⟨{ contract := contract, locals := last, immutables := imms },
    ExecFuncBody.execBlockRet ?_⟩
  have hp := (extSloadsSourcePrelude slots evm imms hd hcv).requireStep
    (by simpa only [ha, decide_true] using (extSloadsAllocationGuard_eval
      (evm := evm) (frame := f) (store_get_self _ _ _)))
  have hr := hp.letStep (evalLocalNewArray (store_get_self _ _ _)
    (show defaultValue? (.elem (.bytes abiBytes32Width)) = .ok (wordBytes32Value ⟨0⟩) by
      native_decide))
  have hi := hr.letStep (show evalExpr? config _ evm (.intLit 0) = .ok (.int 0) by
    simp only [evalExpr?, pure])
  exact (hi.whileStep hloop).returns (evalLocalValue hlast)

theorem morphoExtSloadsSourceAllocationRevert (slots : List Value) (evm : EVM.State) (imms : Store)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (ha : ¬ 128 + 32 * (slots.length + 1) ≤ solcMaxU64) :
    ExecTransitionBody config contract evm (extSloadsArgs slots) extSloadsTransition.body
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (extSloadsSourcePrelude slots evm imms hd hcv).requireRevert
  simpa only [ha, decide_false] using extSloadsAllocationGuard_eval
    (evm := evm) (frame := extSloadsCountFrame slots evm.executionEnv.calldata imms)
    (store_get_self _ _ _)

end Benchmarks.Morpho.MorphoBlue
