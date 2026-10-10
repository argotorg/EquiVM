import Benchmarks.UniswapV4PoolManager.ModifyLiquidityAfterSource
import Benchmarks.UniswapV4PoolManager.AfterLiquidityHookTrace
import Benchmarks.UniswapV4PoolManager.AfterLiquidityReplyMemory
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityAfterHookTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (before : Frame) (key : PoolKeyWords) (keyPtr fees junk : UInt256)
    (R : List UInt256) (f : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ ∃ caller hookDelta mem rdata free,
    f = modifyLiquidityAfterHookFrame before caller hookDelta ∧ PoolKeyView mem keyPtr key ∧
    free.toNat+64 < UInt256.size ∧ memLoad (UInt256.ofNat 64) mem = free ∧ ∃ aw k C,
      RD (deployedRuntime v) I g s0 ⟨6222⟩
        ([hookDelta, caller, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
        mem aw rdata post.accountMap k C

theorem modifyLiquidityAfterCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len junk : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {k C : Nat} {R : List UInt256} {oldHook : Value}
    (v : PoolManagerImmutables) (hstack : R.length+32 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hkeylocal : f.locals.get? "key" = some (poolKeyValue key))
    (hparamslocal : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "callerDelta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hh : f.locals.get? "hookDelta" = some oldHook)
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkl : 96 ≤ keyPtr.toNat) (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hfb : free.toNat+3600 ≤ solcMaxU64) (hlen : len.toNat ≤ solcMaxU64)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨14427⟩
      ([key.hooks, keyPtr, paramsPtr, delta, fees, src, len, ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm ((modifyLiquidityTransition.body.drop 26).take 3) result ∧
      blockResultTrace (deployedRuntime v) g s0
        (modifyLiquidityAfterHookTrace v I g s0 f key keyPtr fees junk R) (fun _ _ => False) result := by
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hw : accountWord hook = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
  have hfit : free.toNat+len.toNat+576 < UInt256.size := by
    change _ ≤ 2^64-1 at hfb hlen
    change _ < 2^256
    omega
  rcases afterLiquidityHookTrace (ret := ⟨6222⟩)
      (R := [⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R) f v
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hI hσ0 hk hp hc hl hu hkb hpb (by omega) hfit hsrc hgas hpaid hfree
      (by rw [deployedRuntime_jumps]; jump_dest) (by rw [hw]; exact h) with
    hog | ⟨post, z, out, hcall, _, henv, hworld, hout, hr⟩
  · exact .inl hog
  have hkeyeval := evalLocalValue (cfg := config) (evm := evm) hkeylocal
  have hstmt := afterLiquidityCall hf (evalStructField hkeyeval (field := "hooks") rfl)
    hkeyeval (evalLocalValue hparamslocal) (evalLocalValue hd) (evalLocalValue he) (evalLocalValue hb)
    hc hl hu (by simpa only [hI] using hcall) "__c8"
  simp only [afterLiquidityInvocationResult, hI] at hstmt
  unfold afterLiquidityTraceResult at hr
  have hdone {state : State} {caller hookDelta free' : UInt256} {mem' rdata' : ByteArray}
      (hs : ExecStmt config f evm modifyLiquidityTransition.body[26]!
        (.ok (modifyLiquidityAfterCallFrame f caller hookDelta) state))
      (henv' : state.executionEnv = I) (hworld' : state.σ₀ = s0.σ₀)
      (hkey' : PoolKeyView mem' keyPtr key) (hfreefit : free'.toNat+64 < UInt256.size)
      (hfree' : memLoad (UInt256.ofNat 64) mem' = free')
      (ht : afterLiquidityReturnTrace v I g s0 mem' rdata' state.accountMap ⟨6222⟩ caller hookDelta
        ([⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)) :
      ∃ result, ExecBlock config f evm ((modifyLiquidityTransition.body.drop 26).take 3) result ∧
        blockResultTrace (deployedRuntime v) g s0
          (modifyLiquidityAfterHookTrace v I g s0 f key keyPtr fees junk R) (fun _ _ => False) result := by
    refine ⟨_, ExecBlock.consNormal hs (modifyLiquidityAfterAssignSource hd hh),
      henv', hworld', caller, hookDelta, mem', rdata', free', rfl, hkey', hfreefit, hfree', ?_⟩
    exact ht
  have hactive (caller hookDelta : UInt256)
      (hs : ExecStmt config f evm modifyLiquidityTransition.body[26]!
        (.ok (modifyLiquidityAfterCallFrame f caller hookDelta) post))
      (ht : afterLiquidityReturnTrace v I g s0
        (afterLiquidityReplyMemory (afterLiquidityAdd p) I.calldata mem src.toNat free len I.source key p delta fees out)
        out post.accountMap ⟨6222⟩ caller hookDelta ([⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)) := by
    have hwide : free.toNat+len.toNat+out.size+768 < UInt256.size := by
      change _ ≤ 2^64-1 at hfb hlen
      change _ < 2^256
      omega
    exact hdone hs henv hworld
      ⟨hk.slice.afterLiquidityReply (afterLiquidityAdd p) I.calldata src.toNat free len I.source key p delta fees out
        hsrc hkl (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb)
        hfit, hk.fits⟩
      (afterLiquidityReplyFree_bounds free len out hwide).2
      (afterLiquidityReplyMemory_free _ _ _ _ _ _ _ _ _ _ _ _ (by omega) hfit) ht
  by_cases hself : I.source = hook
  · rw [if_pos hself] at hr hstmt
    exact .inr (hdone hstmt hI hσ0 hk (by omega) hfree hr)
  rw [if_neg hself] at hr hstmt
  by_cases ha : afterLiquidityActive hook p
  · rw [if_pos ha, afterLiquidityActiveResult] at hr
    rw [if_pos ha] at hstmt
    by_cases hv : z = true ∧ hookReplyValid (afterLiquidityPayload (afterLiquidityAdd p) I.source key p delta fees
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) out
    · rw [if_pos hv] at hr hstmt
      by_cases hbad : afterLiquidityParse hook (afterLiquidityAdd p) = true ∧ out.size ≠ 64
      · rw [if_pos hbad] at hr hstmt
        exact .inr ⟨.reverted, ExecBlock.consRevert hstmt, hr⟩
      · rw [if_neg hbad] at hr hstmt
        by_cases hsub : balanceDeltaCombineFits true delta (hookDeltaWord out (afterLiquidityParse hook (afterLiquidityAdd p)))
        · rw [if_pos hsub] at hr hstmt
          exact .inr (hactive _ _ hstmt hr)
        · rw [if_neg hsub] at hr hstmt
          exact .inr ⟨.reverted, ExecBlock.consRevert hstmt, hr⟩
    · rw [if_neg hv] at hr hstmt
      exact .inr ⟨.reverted, ExecBlock.consRevert hstmt, hr⟩
  · rw [if_neg ha] at hr hstmt
    exact .inr (hdone hstmt hI hσ0 hk (by omega) hfree hr)

end Benchmarks.UniswapV4PoolManager
