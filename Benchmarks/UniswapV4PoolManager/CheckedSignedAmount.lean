import Benchmarks.UniswapV4PoolManager.SignedAmountsSource
import Benchmarks.UniswapV4PoolManager.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def checkedSignedAmountBlock (one : Bool) (ea eb ed : Expr) (amountRet castRet : Ident) : List Stmt :=
  [.internalCall (signedAmountName one) [ea, eb, ed] amountRet,
   .internalCall "SafeCast_toInt128" [.var amountRet] castRet]
def checkedSignedAmountFrame (f : Frame) (amountRet castRet : Ident) (w : UInt256) : Frame :=
  {f with locals := (f.locals.insert amountRet (.int (EVM.signed w))).insert castRet (.int (EVM.signed w))}
def checkedSignedAmountFits (one : Bool) (a b : UInt256) (delta : Int) : Prop :=
  signedAmountFits one a b delta ∧ signedFits ⟨128, by decide⟩ (EVM.signed (signedAmountWord one a b delta))
instance (one : Bool) (a b : UInt256) (delta : Int) : Decidable (checkedSignedAmountFits one a b delta) :=
  inferInstanceAs (Decidable (_ ∧ _))
def checkedSignedAmountResult (f : Frame) (evm : State) (one : Bool) (a b : UInt256) (delta : Int)
    (amountRet castRet : Ident) : ExecResult :=
  if checkedSignedAmountFits one a b delta then
    .ok (checkedSignedAmountFrame f amountRet castRet (signedAmountWord one a b delta)) evm else .reverted

theorem checkedSignedAmount {f : Frame} {evm : State} {a b : UInt256} {delta : Int} {ea eb ed : Expr}
    (hf : f.contract = contract) (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (heb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hed : evalExpr? config f evm ed = .ok (.int delta)) (one : Bool) (amountRet castRet : Ident) :
    ExecBlock config f evm (checkedSignedAmountBlock one ea eb ed amountRet castRet)
      (checkedSignedAmountResult f evm one a b delta amountRet castRet) := by
  have hcall := signedAmountCall hf ha hb hdlo hdhi hea heb hed one amountRet
  by_cases hfit : signedAmountFits one a b delta
  · rw [if_pos hfit] at hcall
    let f1 := {f with locals := f.locals.insert amountRet (.int (EVM.signed (signedAmountWord one a b delta)))}
    have hcast := signedToInt128Call (f := f1) (evm := evm) hf (evalLocalValue (store_get_self _ _ _)) castRet
    by_cases hc : signedFits ⟨128, by decide⟩ (EVM.signed (signedAmountWord one a b delta))
    · rw [checkedSignedAmountResult, if_pos ⟨hfit, hc⟩]
      rw [if_pos hc] at hcast
      exact ExecBlock.consNormal hcall (execBlock_singleton hcast)
    · rw [checkedSignedAmountResult, if_neg (fun hh => hc hh.2)]
      rw [if_neg hc] at hcast
      exact ExecBlock.consNormal hcall (ExecBlock.consRevert hcast)
  · rw [checkedSignedAmountResult, if_neg (fun hh => hfit hh.1)]
    exact ExecBlock.consRevert (by simpa only [if_neg hfit] using hcall)

theorem checkedSignedAmountResult_normal {f f' : Frame} {evm post : State} {one : Bool}
    {a b : UInt256} {delta : Int} {amountRet castRet : Ident}
    (h : checkedSignedAmountResult f evm one a b delta amountRet castRet = .ok f' post) :
    f' = checkedSignedAmountFrame f amountRet castRet (signedAmountWord one a b delta) ∧ post = evm := by
  unfold checkedSignedAmountResult at h
  split_ifs at h <;> cases h
  exact ⟨rfl, rfl⟩

end Benchmarks.UniswapV4PoolManager
