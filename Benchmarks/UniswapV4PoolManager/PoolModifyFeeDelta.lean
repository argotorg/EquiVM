import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFeeDeltaFrame (f : Frame) (owed0 owed1 : UInt256) : Frame :=
  let f0 := {f with locals := f.locals.insert "__c9" (.int (Int.ofNat owed0.toNat))}
  let f1 := {f0 with locals := f0.locals.insert "__c10" (.int (Int.ofNat owed1.toNat))}
  let f2 := {f1 with locals := f1.locals.insert "__c11" (.int (EVM.signed (balanceDeltaWord owed0 owed1)))}
  {f2 with locals := f2.locals.insert "feeDelta" (.int (EVM.signed (balanceDeltaWord owed0 owed1)))}
def poolModifyFeeDeltaResult (f : Frame) (evm : State) (owed0 owed1 : UInt256) : ExecResult :=
  if owed0.toNat < 2^127 ∧ owed1.toNat < 2^127 then .ok (poolModifyFeeDeltaFrame f owed0 owed1) evm else .reverted

theorem poolModifyFeeDelta {f : Frame} {evm : State} {owed0 owed1 : UInt256} {old : Value}
    (hf : f.contract = contract)
    (h0 : f.locals.get? "feesOwed0" = some (.int (Int.ofNat owed0.toNat)))
    (h1 : f.locals.get? "feesOwed1" = some (.int (Int.ofNat owed1.toNat)))
    (hfee : f.locals.get? "feeDelta" = some old) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 19).take 4)
      (poolModifyFeeDeltaResult f evm owed0 owed1) := by
  by_cases hf0 : owed0.toNat < 2^127
  · let f0 := {f with locals := f.locals.insert "__c9" (.int (Int.ofNat owed0.toNat))}
    have hc0 := uintToInt128Call (f := f) (evm := evm) hf (evalLocalValue h0) hf0 "__c9"
    have h1' : f0.locals.get? "feesOwed1" = some (.int (Int.ofNat owed1.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c9" == "feesOwed1") = false)).trans h1
    by_cases hf1 : owed1.toNat < 2^127
    · rw [poolModifyFeeDeltaResult, if_pos ⟨hf0, hf1⟩]
      let f1 := {f0 with locals := f0.locals.insert "__c10" (.int (Int.ofNat owed1.toNat))}
      let f2 := {f1 with locals := f1.locals.insert "__c11" (.int (EVM.signed (balanceDeltaWord owed0 owed1)))}
      have hc1 := uintToInt128Call (f := f0) (evm := evm) hf (evalLocalValue h1') hf1 "__c10"
      have hsign0 : EVM.signed owed0 = Int.ofNat owed0.toNat := by
        rw [signed_eq_normalize, normalizeInt_sint256_word_of_lt _ (by change owed0.toNat < 2^255; omega)]
      have hsign1 : EVM.signed owed1 = Int.ofNat owed1.toNat := by
        rw [signed_eq_normalize, normalizeInt_sint256_word_of_lt _ (by change owed1.toNat < 2^255; omega)]
      have he0 : evalExpr? config f1 evm (.var "__c9") = .ok (.int (EVM.signed owed0)) := by
        rw [hsign0]
        exact evalLocalValue ((store_get_ne _ _ (by decide : ("__c10" == "__c9") = false)).trans (store_get_self _ _ _))
      have he1 : evalExpr? config f1 evm (.var "__c10") = .ok (.int (EVM.signed owed1)) := by
        rw [hsign1]
        exact evalLocalValue (store_get_self _ _ _)
      have hpack := balanceDeltaCall (f := f1) (evm := evm) hf he0 he1 "__c11"
      have hassign : ExecStmt config f2 evm poolModifyFunction.body[22]!
          (.ok (poolModifyFeeDeltaFrame f owed0 owed1) evm) :=
        ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalValue
          ((store_get_ne3 _ _ _ _ (by decide : ("__c9" == "feeDelta") = false)
            (by decide : ("__c10" == "feeDelta") = false) (by decide : ("__c11" == "feeDelta") = false)).trans hfee))
      exact ExecBlock.consNormal hc0 (ExecBlock.consNormal hc1 (ExecBlock.consNormal hpack (execBlock_singleton hassign)))
    · rw [poolModifyFeeDeltaResult, if_neg (fun hh => hf1 hh.2)]
      exact ExecBlock.consNormal hc0 (ExecBlock.consRevert
        (uintToInt128CallReverts (f := f0) (evm := evm) hf (evalLocalValue h1') hf1 "__c10"))
  · rw [poolModifyFeeDeltaResult, if_neg (fun hh => hf0 hh.1)]
    exact ExecBlock.consRevert (uintToInt128CallReverts (f := f) (evm := evm) hf (evalLocalValue h0) hf0 "__c9")

theorem poolModifyFeeDeltaResult_normal {f f' : Frame} {evm post : State} {owed0 owed1 : UInt256}
    (h : poolModifyFeeDeltaResult f evm owed0 owed1 = .ok f' post) :
    f' = poolModifyFeeDeltaFrame f owed0 owed1 ∧ post = evm := by
  unfold poolModifyFeeDeltaResult at h
  split_ifs at h <;> cases h
  exact ⟨rfl, rfl⟩

theorem poolModifyFeeDeltaFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (owed0 owed1 : UInt256) :
    PoolModifyContext (poolModifyFeeDeltaFrame f owed0 owed1) id p :=
  (((hc.insert "__c9" _ (by decide)).insert "__c10" _ (by decide)).insert "__c11" _ (by decide)).insert
    "feeDelta" _ (by decide)

theorem poolModifyFeeDeltaFrame_get (f : Frame) (owed0 owed1 : UInt256) (name : Ident)
    (h0 : ("__c9" == name) = false) (h1 : ("__c10" == name) = false)
    (hp : ("__c11" == name) = false) (hf : ("feeDelta" == name) = false) :
    (poolModifyFeeDeltaFrame f owed0 owed1).locals.get? name = f.locals.get? name :=
  store_get_ne4 _ _ _ _ _ h0 h1 hp hf

end Benchmarks.UniswapV4PoolManager
