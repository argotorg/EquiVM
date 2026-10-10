import Benchmarks.UniswapV4PoolManager.BeforeSwapDeltaSource
import Benchmarks.UniswapV4PoolManager.BeforeSwapFeeSource
import Benchmarks.UniswapV4PoolManager.HookWrapperSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapParse (hook : AccountAddress) : Prop := UInt256.land (accountWord hook) ⟨8⟩ ≠ ⟨0⟩
instance (hook : AccountAddress) : Decidable (beforeSwapParse hook) := inferInstanceAs (Decidable (_ ≠ _))
def beforeSwapReplyAmount (hook : AccountAddress) (amount : UInt256) (out : ByteArray) : UInt256 :=
  if beforeSwapParse hook then amount+beforeSwapSpecified out else amount
def beforeSwapReplyHook (hook : AccountAddress) (out : ByteArray) : UInt256 :=
  if beforeSwapParse hook then calldataWord out 32 else ⟨0⟩
def beforeSwapReplyStmts : List Stmt :=
  [.require (.binary .eq (.arrayLength .localVar {base := "result"}) (.intLit 96)),
   beforeSwapFeeStmt,
   .ite (hookPermissionExpr (.var "self") ⟨8⟩) beforeSwapDeltaStmts []]
def beforeSwapReplyResult (f : Frame) (evm : State) (hook : AccountAddress) (key : PoolKeyWords)
    (amount : UInt256) (out : ByteArray) : ExecResult :=
  if out.size = 96 then
    if beforeSwapParse hook then beforeSwapDeltaResult (beforeSwapFeeFrame f key out) evm amount out
    else .ok (beforeSwapFeeFrame f key out) evm
  else .reverted

theorem beforeSwapReplySource {f : Frame} {evm : State} {hook : AccountAddress} {key : PoolKeyWords}
    {amount : UInt256} {out : ByteArray} {oldHook oldFee : Value}
    (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hh : f.locals.get? "hookReturn" = some oldHook)
    (hf : f.locals.get? "lpFeeOverride" = some oldFee)
    (hr : f.locals.get? "result" = some (.bytes out)) :
    ExecBlock config f evm beforeSwapReplyStmts (beforeSwapReplyResult f evm hook key amount out) := by
  have hlen := evalNatEqLiteral (cfg := config) (evm := evm) (k := 96) (evalLocalBytesLength hr)
  by_cases hsize : out.size = 96
  · rw [beforeSwapReplyResult, if_pos hsize]
    have hfee := beforeSwapFeeSource (evm := evm) hk hr hf (by omega : 96 ≤ out.size)
    have hget := beforeSwapFeeFrame_get f key out
    have hflag := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm)
      ((hget "self" (by decide)).trans hs)) ⟨8⟩ (by decide)
    change evalExpr? config (beforeSwapFeeFrame f key out) evm _ =
      .ok (.bool (decide (beforeSwapParse hook))) at hflag
    by_cases hp : beforeSwapParse hook
    · rw [if_pos hp]
      exact ExecBlock.consNormal (ExecStmt.requireTrue (hlen.trans (by rw [decide_eq_true hsize])))
        (ExecBlock.consNormal hfee (execBlock_singleton
          (ExecStmt.iteTrue (hflag.trans (by rw [decide_eq_true hp]))
            (beforeSwapDeltaSource ((hget "amountToSwap" (by decide)).trans ha)
              ((hget "hookReturn" (by decide)).trans hh) ((hget "result" (by decide)).trans hr) (by omega)))))
    · rw [if_neg hp]
      exact ExecBlock.consNormal (ExecStmt.requireTrue (hlen.trans (by rw [decide_eq_true hsize])))
        (ExecBlock.consNormal hfee (execBlock_singleton
          (ExecStmt.iteFalse (hflag.trans (by rw [decide_eq_false hp])) ExecBlock.nil)))
  · rw [beforeSwapReplyResult, if_neg hsize]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (hlen.trans (by rw [decide_eq_false hsize])))

theorem beforeSwapReplyResult_locals {f f' : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {amount : UInt256} {out : ByteArray}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hh : f.locals.get? "hookReturn" = some (.int 0))
    (hf : f.locals.get? "lpFeeOverride" = some (.int 0))
    (hr : beforeSwapReplyResult f evm hook key amount out = .ok f' post) :
    post = evm ∧
    f'.locals.get? "amountToSwap" = some (.int (EVM.signed (beforeSwapReplyAmount hook amount out))) ∧
    f'.locals.get? "hookReturn" = some (.int (EVM.signed (beforeSwapReplyHook hook out))) ∧
    f'.locals.get? "lpFeeOverride" = some (.int (Int.ofNat (beforeSwapFee key out).toNat)) := by
  rw [beforeSwapReplyResult] at hr
  split_ifs at hr with hsize hp
  · simpa only [beforeSwapReplyAmount, beforeSwapReplyHook, if_pos hp] using
      beforeSwapDeltaResult_locals ((beforeSwapFeeFrame_get f key out "amountToSwap" (by decide)).trans ha)
        (beforeSwapFeeFrame_fee key out hf) hr
  · cases hr
    refine ⟨rfl, ?_, ?_, beforeSwapFeeFrame_fee key out hf⟩
    · simpa only [beforeSwapReplyAmount, if_neg hp] using
        (beforeSwapFeeFrame_get f key out "amountToSwap" (by decide)).trans ha
    · simpa only [beforeSwapReplyHook, if_neg hp, show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl] using
        (beforeSwapFeeFrame_get f key out "hookReturn" (by decide)).trans hh

end Benchmarks.UniswapV4PoolManager
