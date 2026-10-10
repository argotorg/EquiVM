import Benchmarks.UniswapV4PoolManager.BeforeLiquidityHookTrace
import Benchmarks.UniswapV4PoolManager.BeforeLiquidityCall
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.PoolStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityAfterBeforeTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 post : State) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (keyPtr paramsPtr src len id junk : UInt256) (R : List UInt256) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ ∃ mem rdata free,
    PoolKeyView mem keyPtr key ∧ MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)) ∧
    MemorySlice mem 128 (wordBytes [poolSlot id]) ∧
    keyPtr.toNat+160 ≤ free.toNat ∧ paramsPtr.toNat+128 ≤ free.toNat ∧
    free.toNat+4000 ≤ solcMaxU64 ∧ memLoad (UInt256.ofNat 64) mem = free ∧
    beforeLiquidityContinuation v I g s0 mem rdata post.accountMap src paramsPtr len keyPtr id junk R

theorem modifyLiquidityBeforeCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len id junk : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+28 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hslot : MemorySlice mem 128 (wordBytes [poolSlot id]))
    (hkl : 160 ≤ keyPtr.toNat) (hpl : 160 ≤ paramsPtr.toNat)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hfb : free.toNat+4000 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hlen : len.toNat ≤ solcMaxU64)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+46)
    (h : RD (deployedRuntime v) I g s0 ⟨5474⟩
      ([src, paramsPtr, len, keyPtr, id, junk] ++ R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm modifyLiquidityTransition.body[15]! result ∧
      blockResultTrace (deployedRuntime v) g s0
        (fun f' post => f' = {f with locals := f.locals.insert "__c5" .unit} ∧
          modifyLiquidityAfterBeforeTrace v I g s0 post key p keyPtr paramsPtr src len id junk R)
        (fun _ _ => False) result := by
  let hook := AccountAddress.ofNat key.hooks.toNat
  have hw : accountWord hook = key.hooks :=
    (accountWord_fromId key.hooks).trans (solcAddrMask_clean hc.2.2.2.2)
  have hfit : free.toNat+len.toNat+512 < UInt256.size := by
    change _ ≤ 2^64-1 at hfb hlen
    change _ < 2^256
    omega
  rcases beforeLiquidityHookTrace v hstack hI hσ0 hkey hparams hc hw hl hu hkb hpb
      (by omega) hfit hsrc hgas hpaid hfree h with
    hog | ⟨post, z, out, hcall, _, hbound, henv, hworld, _, hr⟩
  · exact .inl hog
  have hkeyeval := evalLocalValue (cfg := config) (evm := evm) hk
  have hstmt := beforeLiquidityCall hf (evalStructField hkeyeval (field := "hooks") rfl)
    hkeyeval (evalLocalValue hp) (evalLocalValue hd) hc hl hu (by simpa only [hI] using hcall) "__c5"
  simp only [beforeLiquidityInvocationResult, hI] at hstmt
  unfold beforeLiquidityTraceResult at hr
  have hskip (ht : beforeLiquidityContinuation v I g s0 mem rdata evm.accountMap
      src paramsPtr len keyPtr id junk R) :
      modifyLiquidityAfterBeforeTrace v I g s0 evm key p keyPtr paramsPtr src len id junk R :=
    ⟨hI, hσ0, mem, rdata, free, hkey, hparams, hslot, hkb, hpb, hfb, hfree, ht⟩
  have hactive (add : Bool) (hb : (beforeLiquidityFree free len).toNat+out.size+4096 ≤ solcMaxU64)
      (ht : beforeLiquidityContinuation v I g s0
        (beforeLiquidityReplyMemory add I.calldata mem src.toNat free len I.source key p out) out
        post.accountMap src paramsPtr len keyPtr id junk R) :
      modifyLiquidityAfterBeforeTrace v I g s0 post key p keyPtr paramsPtr src len id junk R := by
    have hs := beforeLiquidityReplyFree_bounds free len out hfit hb
    refine ⟨henv, hworld, _, out, beforeLiquidityReplyFree free len out, ?_, ?_, ?_,
      by omega, by omega, hs.2, ?_, ht⟩
    · exact ⟨hkey.slice.beforeLiquidityReply add I.calldata src.toNat free len I.source key p out
        hsrc (by omega) (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb)
        hfit, hkey.fits⟩
    · exact hparams.beforeLiquidityReply add I.calldata src.toNat free len I.source key p out
        hsrc (by omega) (by simpa only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil] using hpb) hfit
    · exact hslot.beforeLiquidityReply add I.calldata src.toNat free len I.source key p out
        hsrc (by decide) (by rw [wordBytes_size]; change 128+32*1 ≤ free.toNat; omega) hfit
    · exact beforeLiquidityReplyMemory_free _ _ _ _ _ _ _ _ _ _ (by omega) hfit
  by_cases hself : I.source = hook
  · rw [if_pos hself] at hr hstmt
    exact .inr ⟨_, hstmt, rfl, hskip hr⟩
  rw [if_neg hself] at hr hstmt
  by_cases ha : beforeLiquidityEnabled hook p true
  · rw [if_pos ha] at hr hstmt
    by_cases hv : z = true ∧ hookReplyValid (beforeLiquidityPayload true I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) out
    · rw [if_pos hv] at hr hstmt
      exact .inr ⟨_, hstmt, rfl, hactive true (hbound true hself ha hv) hr⟩
    · rw [if_neg hv] at hr hstmt
      exact .inr ⟨_, hstmt, hr⟩
  rw [if_neg ha] at hr hstmt
  by_cases hn : beforeLiquidityEnabled hook p false
  · rw [if_pos hn] at hr hstmt
    by_cases hv : z = true ∧ hookReplyValid (beforeLiquidityPayload false I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) out
    · rw [if_pos hv] at hr hstmt
      exact .inr ⟨_, hstmt, rfl, hactive false (hbound false hself hn hv) hr⟩
    · rw [if_neg hv] at hr hstmt
      exact .inr ⟨_, hstmt, hr⟩
  · rw [if_neg hn] at hr hstmt
    exact .inr ⟨_, hstmt, rfl, hskip hr⟩

end Benchmarks.UniswapV4PoolManager
