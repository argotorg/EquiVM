import Benchmarks.UniswapV4PoolManager.WordRangeSourceStep

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

def wordRangeArgs (start : UInt256) (n : Nat) : Store :=
  ((∅ : Store).insert "startSlot" (wordBytes32Value start)).insert "nSlots" (.int (Int.ofNat n))

def wordRangeResultFrame (evm : EVM.State) (imms : Store) (start : UInt256) (n : Nat) : Frame :=
  {contract := contract, immutables := imms,
   locals := ((wordRangeArgs start n).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
     "result" (.array (List.replicate n (wordBytes32Value ⟨0⟩)))}

def wordRangeFirstFrame (evm : EVM.State) (imms : Store) (start : UInt256) (n : Nat) : Frame :=
  let f := wordRangeResultFrame evm imms start n
  {f with locals := f.locals.insert "first" (.int (Int.ofNat
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner start).toNat))}

theorem wordRangePrelude (evm : EVM.State) (imms : Store) (start : UInt256) (n : Nat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ABlock config evm {contract := contract, locals := wordRangeArgs start n, immutables := imms}
      extsload_bytes32_uint256Transition.body (wordRangeFirstFrame evm imms start n)
      (extsload_bytes32_uint256Transition.body.drop 5) := by
  refine ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_ |>.letStep ?_ |>.letStep ?_
  · simpa only [hhi, decide_true] using calldataSizeGuard_eval config contract (wordRangeArgs start n) imms evm
  · exact evalLocalNewArray ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
      (show defaultValue? (.elem (.bytes abiBytes32Width)) = .ok (wordBytes32Value ⟨0⟩) by native_decide)
  · apply rawSlots_read rfl
    · simp only [wordRangeArgs,
        store_get_ne (k := "result") (a := "rawSlots") _ _ (by decide),
        store_get_ne (k := "__calldata") (a := "rawSlots") _ _ (by decide),
        store_get_ne (k := "nSlots") (a := "rawSlots") _ _ (by decide),
        store_get_ne (k := "startSlot") (a := "rawSlots") _ _ (by decide), store_get_empty]
    · apply evalCastValue (evalLocalValue ?_) (castBytes32ToUint256 start)
      simp only [wordRangeArgs,
        store_get_ne (k := "result") (a := "startSlot") _ _ (by decide),
        store_get_ne (k := "__calldata") (a := "startSlot") _ _ (by decide),
        store_get_ne (k := "nSlots") (a := "startSlot") _ _ (by decide), store_get_self]

theorem wordRangeSource (evm : EVM.State) (imms : Store) (start : UInt256) (n : Nat)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ∃ f, ExecTransitionBody config contract evm (wordRangeArgs start n)
      extsload_bytes32_uint256Transition.body
      (.returned f evm (some [.array (wordArrayValues (wordRangeValue evm start) 0 n)])) imms := by
  let f := wordRangeFirstFrame evm imms start n
  let res := List.replicate n (wordBytes32Value ⟨0⟩)
  have hres : f.locals.get? "result" = some (.array res) :=
    (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  have hn : f.locals.get? "nSlots" = some (.int (Int.ofNat n)) := by
    simp only [f, wordRangeFirstFrame, wordRangeResultFrame, wordRangeArgs,
      store_get_ne (k := "first") (a := "nSlots") _ _ (by decide),
      store_get_ne (k := "result") (a := "nSlots") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "nSlots") _ _ (by decide), store_get_self]
  have hs : f.locals.get? "startSlot" = some (wordBytes32Value start) := by
    simp only [f, wordRangeFirstFrame, wordRangeResultFrame, wordRangeArgs,
      store_get_ne (k := "first") (a := "startSlot") _ _ (by decide),
      store_get_ne (k := "result") (a := "startSlot") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "startSlot") _ _ (by decide),
      store_get_ne (k := "nSlots") (a := "startSlot") _ _ (by decide), store_get_self]
  have hraw : f.locals.get? "rawSlots" = none := by
    simp only [f, wordRangeFirstFrame, wordRangeResultFrame, wordRangeArgs,
      store_get_ne (k := "first") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "result") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "nSlots") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "startSlot") (a := "rawSlots") _ _ (by decide), store_get_empty]
  have heq := evalNatEqZero (cfg := config) (f := f) (evm := evm) (evalLocalValue hn)
  have hp := wordRangePrelude evm imms start n hwv hhi
  by_cases hz : n = 0
  · subst n
    refine ⟨f, ExecFuncBody.execBlockRet (hp.run ?_)⟩
    simp only [wordArrayValues, wordArrayWords, List.map_nil]
    change ExecBlock config f evm _ (.returned f evm (some [.array []]))
    have hr0 : f.locals.get? "result" = some (.array []) := by
      simpa only [res, List.replicate_zero] using hres
    exact ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [decide_true] using heq)
      (ABlock.start.returns (evalLocalValue hr0)))
  · let res1 := res.set 0 (wordBytes32Value (wordRangeValue evm start 0))
    let f1 := {f with locals := f.locals.insert "result" (.array res1)}
    let locals := f1.locals.insert "i" (.int 1)
    have hl : WordRangeLocals start n res1 1 locals := by
      constructor
      · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hs)
      · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hn)
      · exact store_get_self _ _ _
      · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
      · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hraw)
    obtain ⟨last, hloop, hlast⟩ := wordRangeSourceLoop evm imms start n (n-1) locals res1 1 hl
      (by omega) (by simp only [res1, res, List.length_set, List.length_replicate]) (by
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        exact List.getElem?_set_self (by simp only [res, List.length_replicate]; omega))
    have hfirst : evalExpr? config f evm (.cast (.var "first") (.elem (.bytes abiBytes32Width))) =
        .ok (wordBytes32Value (wordRangeValue evm start 0)) := by
      rw [wordRangeValue_zero]
      exact evalCastValue (evalLocalValue (store_get_self _ _ _)) (castUint256ToBytes32 _)
    have hassign := ExecStmt.assign hfirst
      (assignLocalArrayAt hres (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat 0)) by
        simp only [evalExpr?, pure]; rfl)
        (by simp only [res, List.length_replicate]; omega))
    refine ⟨{contract := contract, locals := last, immutables := imms},
      ExecFuncBody.execBlockRet (hp.run ?_)⟩
    exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hz, decide_false] using heq) ExecBlock.nil)
      (ExecBlock.consNormal hassign ((ABlock.start.letStep (by simp only [evalExpr?, pure])
        |>.whileStep hloop).returns (evalLocalValue hlast)))

end Benchmarks.UniswapV4PoolManager
