import Benchmarks.UniswapV4PoolManager.PoolSwapLPSelectSource
import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeSource
import Benchmarks.UniswapV4PoolManager.WordConditionalSource
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLPInitFrame (f : Frame) (packed override : UInt256) : Frame :=
  poolSwapLPSelectFrame (wordLocal (valueLocal f "__c6" (.bool (lpFeeIsOverride override))) "lpFee" ⟨0⟩) packed override

theorem poolSwapLPInitFrame_contract (f : Frame) (packed override : UInt256) :
    (poolSwapLPInitFrame f packed override).contract = f.contract := by
  simp only [poolSwapLPInitFrame, poolSwapLPSelectFrame_contract, wordLocal_contract, valueLocal_contract]

theorem poolSwapLPInitFrame_get (f : Frame) (packed override : UInt256) (key : Ident)
    (h6 : ("__c6" == key) = false) (ho : ("overrideFee" == key) = false)
    (hs : ("storedFee" == key) = false) (hl : ("lpFee" == key) = false) :
    (poolSwapLPInitFrame f packed override).locals.get? key = f.locals.get? key := by
  simp only [poolSwapLPInitFrame, poolSwapLPSelectFrame_get _ _ _ key ho hs hl,
    wordLocal_get, valueLocal_get, h6, hl, Bool.false_eq_true, if_false]

theorem poolSwapLPInitFrame_fee (f : Frame) (packed override : UInt256) :
    (poolSwapLPInitFrame f packed override).locals.get? "lpFee" =
      some (.int (Int.ofNat (poolSwapLPFeeWord packed override).toNat)) :=
  poolSwapLPSelectFrame_fee _ packed override

theorem poolSwapLPInitSource {f : Frame} {evm : State} {packed : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hs : f.locals.get? "slot0Start" = some (wordBytes32Value packed)) (hc : p.lpFeeOverride.toNat < 2^24) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 18).take 3)
      (if poolSwapLPFeeValid p.lpFeeOverride then .ok (poolSwapLPInitFrame f packed p.lpFeeOverride) evm else .reverted) := by
  let f1 := valueLocal f "__c6" (.bool (lpFeeIsOverride p.lpFeeOverride))
  let f2 := wordLocal f1 "lpFee" ⟨0⟩
  have h0 : ExecStmt config f evm poolSwapFunction.body[18]! (.ok f1 evm) :=
    lpFeeOverrideCall hf hc (evalStructField (field := "lpFeeOverride") (evalLocalValue hp) rfl) "__c6"
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[19]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hp2 : f2.locals.get? "params" = some (poolSwapParamsValue p) :=
    (store_get_ne2 _ _ _ (by decide : ("__c6" == "params") = false) (by decide : ("lpFee" == "params") = false)).trans hp
  have hs2 : f2.locals.get? "slot0Start" = some (wordBytes32Value packed) :=
    (store_get_ne2 _ _ _ (by decide : ("__c6" == "slot0Start") = false) (by decide : ("lpFee" == "slot0Start") = false)).trans hs
  have hg2 : f2.locals.get? "__c6" = some (.bool (lpFeeIsOverride p.lpFeeOverride)) :=
    (store_get_ne _ _ (by decide : ("lpFee" == "__c6") = false)).trans (store_get_self _ _ _)
  have h2 := poolSwapLPSelectSource (f := f2) (evm := evm) hf hp2 hs2 hg2 (store_get_self _ _ _) hc
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (execBlock_singleton h2))

def poolSwapEffectiveFee (protocol lpFee : UInt256) : UInt256 :=
  if protocol = ⟨0⟩ then lpFee else protocolSwapFeeWord protocol lpFee

theorem poolSwapEffectiveFee_bound (protocol : UInt256) {lpFee : UInt256} (hl : lpFee.toNat < 2^24) :
    (poolSwapEffectiveFee protocol lpFee).toNat < 2^24 := by
  unfold poolSwapEffectiveFee
  split
  · exact hl
  · exact protocolSwapFeeWord_bound protocol lpFee

def poolSwapFeeInitFrame (f : Frame) (protocol lpFee : UInt256) : Frame :=
  wordLocal (wordLocal f "__c9" (protocolSwapFeeWord protocol lpFee)) "swapFee" (poolSwapEffectiveFee protocol lpFee)

theorem poolSwapFeeInitFrame_contract (f : Frame) (protocol lpFee : UInt256) :
    (poolSwapFeeInitFrame f protocol lpFee).contract = f.contract := by
  simp only [poolSwapFeeInitFrame, wordLocal_contract]

theorem poolSwapFeeInitFrame_fee (f : Frame) (protocol lpFee : UInt256) :
    (poolSwapFeeInitFrame f protocol lpFee).locals.get? "swapFee" =
      some (.int (Int.ofNat (poolSwapEffectiveFee protocol lpFee).toNat)) := store_get_self _ _ _

theorem poolSwapFeeInitFrame_get (f : Frame) (protocol lpFee : UInt256) (key : Ident)
    (h9 : ("__c9" == key) = false) (hf : ("swapFee" == key) = false) :
    (poolSwapFeeInitFrame f protocol lpFee).locals.get? key = f.locals.get? key :=
  store_get_ne2 _ _ _ h9 hf

theorem poolSwapFeeInitSource {f : Frame} {evm : State} {protocol lpFee : UInt256} {old : Value}
    (hf : f.contract = contract) (hc : protocol.toNat < 2^16) (hlc : lpFee.toNat < 2^24)
    (hp : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)))
    (hl : f.locals.get? "lpFee" = some (.int (Int.ofNat lpFee.toNat)))
    (hs : f.locals.get? "swapFee" = some old) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 21).take 2)
      (.ok (poolSwapFeeInitFrame f protocol lpFee) evm) := by
  let f1 := wordLocal f "__c9" (protocolSwapFeeWord protocol lpFee)
  have he := evalExpr_cast_int (intType := .uint ⟨16, by decide⟩) (evalLocalValue (cfg := config) (evm := evm) hp)
  have hn := normalizeInt_uint_eq_self ⟨16, by decide⟩ (Int.ofNat protocol.toNat)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hc)
  rw [hn] at he
  have h0 : ExecStmt config f evm poolSwapFunction.body[21]! (.ok f1 evm) :=
    protocolSwapFeeCall hf hc hlc he (evalLocalValue hl) "__c9"
  have hp1 : f1.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c9" == "protocolFee") = false)).trans hp
  have hl1 : f1.locals.get? "lpFee" = some (.int (Int.ofNat lpFee.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c9" == "lpFee") = false)).trans hl
  have hs1 : f1.locals.get? "swapFee" = some old :=
    (store_get_ne _ _ (by decide : ("__c9" == "swapFee") = false)).trans hs
  have hg := evalEqWords (evalLocalValue (cfg := config) (evm := evm) hp1)
    (show evalExpr? config f1 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by simp only [evalExpr?, pure]; rfl)
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[22]! (.ok (poolSwapFeeInitFrame f protocol lpFee) evm) :=
    ExecStmt.assign (evalWordConditional hg (evalLocalValue hl1) (evalLocalValue (store_get_self _ _ _))) (assignLocalValue hs1)
  exact ExecBlock.consNormal h0 (execBlock_singleton h1)

end Benchmarks.UniswapV4PoolManager
