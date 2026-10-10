import Benchmarks.UniswapV4PoolManager.PoolDonateModel
import Benchmarks.UniswapV4PoolManager.SafeCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: the checked int128 negation expressed as its EVM word.
theorem evalNegateInt128AsWord {cfg : Config} {f : Frame} {evm : State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat w.toNat))) (hf : w.toNat < 2^127) :
    evalExpr? cfg f evm (.cast (.binary .sub (.intLit 0) e) (.elem (.int (.sint ⟨128, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.sub ⟨0⟩ w))) := by
  have hn : EVM.signed (UInt256.sub ⟨0⟩ w) = -(Int.ofNat w.toNat) := by
    rw [← wordOfInt_neg_natCast_eq_sub_zero]
    apply signed_wordOfInt
    change -(2^255 : Int) ≤ -(w.toNat : Int) ∧ -(w.toNat : Int) < 2^255
    constructor <;> omega
  rw [hn]
  exact evalNegateInt128Word he hf

def poolDonateDeltaFrame (f : Frame) (amount0 amount1 : UInt256) : Frame :=
  let s0 := f.locals.insert "__c0" (.int (Int.ofNat amount0.toNat))
  let s1 := s0.insert "__c1" (.int (Int.ofNat amount1.toNat))
  let s2 := s1.insert "__c2" (.int (EVM.signed (poolDonateDelta amount0 amount1)))
  {f with locals := s2.insert "delta" (.int (EVM.signed (poolDonateDelta amount0 amount1)))}

theorem poolDonateDeltaSource {f : Frame} {evm : State} {amount0 amount1 : UInt256} {old : Value}
    (hf : f.contract = contract)
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm ((poolDonateFunction.body.drop 3).take 4)
      (if amount0.toNat < 2^127 ∧ amount1.toNat < 2^127 then
        .ok (poolDonateDeltaFrame f amount0 amount1) evm else .reverted) := by
  by_cases ha : amount0.toNat < 2^127
  · let f0 : Frame := {f with locals := f.locals.insert "__c0" (.int (Int.ofNat amount0.toNat))}
    have hc0 := uintToInt128Call (evm := evm) hf (evalLocalValue h0) ha "__c0"
    have h1' : f0.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c0" == "amount1") = false)).trans h1
    by_cases hb : amount1.toNat < 2^127
    · rw [if_pos ⟨ha, hb⟩]
      let f1 : Frame := {f0 with locals := f0.locals.insert "__c1" (.int (Int.ofNat amount1.toNat))}
      let f2 : Frame := {f1 with locals := f1.locals.insert "__c2" (.int (EVM.signed (poolDonateDelta amount0 amount1)))}
      have hc1 := uintToInt128Call (evm := evm) (f := f0) hf (evalLocalValue h1') hb "__c1"
      have he0 := evalNegateInt128AsWord (cfg := config) (f := f1) (evm := evm) (evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c1" == "__c0") = false)).trans (store_get_self _ _ _))) ha
      have he1 := evalNegateInt128AsWord (cfg := config) (f := f1) (evm := evm) (evalLocalValue (store_get_self _ _ _)) hb
      have hc2 := balanceDeltaCall (f := f1) (evm := evm) hf he0 he1 "__c2"
      have hass : ExecStmt config f2 evm poolDonateFunction.body[6]!
          (.ok (poolDonateDeltaFrame f amount0 amount1) evm) :=
        ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
          (assignLocalValue ((store_get_ne3 _ _ _ _ (by decide : ("__c0" == "delta") = false)
            (by decide : ("__c1" == "delta") = false) (by decide : ("__c2" == "delta") = false)).trans hd))
      exact ExecBlock.consNormal hc0 (ExecBlock.consNormal hc1 (ExecBlock.consNormal hc2 (execBlock_singleton hass)))
    · rw [if_neg (fun hh => hb hh.2)]
      exact ExecBlock.consNormal hc0 (ExecBlock.consRevert (uintToInt128CallReverts (f := f0) hf (evalLocalValue h1') hb "__c1"))
  · rw [if_neg (fun hh => ha hh.1)]
    exact ExecBlock.consRevert (uintToInt128CallReverts hf (evalLocalValue h0) ha "__c0")

theorem poolDonateDeltaFrame_get (f : Frame) (amount0 amount1 : UInt256) (name : Ident)
    (h0 : ("__c0" == name) = false) (h1 : ("__c1" == name) = false)
    (h2 : ("__c2" == name) = false) (hd : ("delta" == name) = false) :
    (poolDonateDeltaFrame f amount0 amount1).locals.get? name = f.locals.get? name :=
  store_get_ne4 _ _ _ _ _ h0 h1 h2 hd

end Benchmarks.UniswapV4PoolManager
