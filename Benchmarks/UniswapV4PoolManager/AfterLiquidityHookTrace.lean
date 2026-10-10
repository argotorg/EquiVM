import Benchmarks.UniswapV4PoolManager.AfterLiquiditySelectTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def afterLiquidityTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm post : State) (mem rdata : ByteArray) (free src len ret delta fees : UInt256)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (hook : AccountAddress) (z : Bool) (out : ByteArray)
    (R : List UInt256) : Prop :=
  let old := afterLiquidityReturnTrace v I g s0 mem rdata evm.accountMap ret delta ⟨0⟩ R
  if I.source = hook then old
  else if afterLiquidityActive hook p then
    afterLiquidityActiveResult v I g s0 post (afterLiquidityAdd p) mem src free len ret hook key p delta fees z out R
  else old

theorem afterLiquidityHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+27 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+576 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14427⟩
      (accountWord hook :: keyPtr :: paramsPtr :: delta :: fees :: src :: len :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      (I.source ≠ hook → afterLiquidityActive hook p →
        callViaEVM evm hook 0 (afterLiquidityPayload (afterLiquidityAdd p) I.source key p delta fees
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out)) ∧
      (I.source ≠ hook → afterLiquidityActive hook p → AllocationBounds free (afterLiquidityAllocationSize len)) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      afterLiquidityTraceResult v I g s0 evm post mem rdata free src len ret delta fees key p hook z out R := by
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  by_cases hself : I.source = hook
  · have rd1 := poolManager_block_14427_taken (by omega)
      (by rw [hclean]; change UInt256.eq (accountWord I.source) (accountWord hook) ≠ ⟨0⟩
          rw [heq.mp hself, uInt256_eq_self]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManager_block_14764 (by simp only [List.length_cons]; omega) hret rd1
    refine .inr ⟨evm, false, .empty, (fun hn _ => (hn hself).elim),
      (fun hn _ => (hn hself).elim), hI, hσ0, by decide, ?_⟩
    rw [afterLiquidityTraceResult, if_pos hself]
    exact ⟨_, _, _, rd2⟩
  · have rd1 := poolManager_block_14427_fallthrough (by omega)
      (by rw [hclean]; exact uInt256_eq_zero_of_ne (fun hh => hself (heq.mpr (uInt256_eq_one_eq hh)))) h
    have hd : memLoad (paramsPtr+UInt256.ofNat 64) mem = p.delta :=
      hp.word_load (i := 2) (word := p.delta) rfl (by rw [uadd_word_ofNat_toNat paramsPtr 64 (by omega)])
    have hs := afterLiquiditySelectTrace v (by omega) (by omega) hd hret rd1
    by_cases ha : afterLiquidityActive hook p
    · rw [afterLiquiditySelection, if_pos ha] at hs
      obtain ⟨aw2, k2, C2, hp2, rd2⟩ := hs
      rcases afterLiquidityActiveTrace f v (afterLiquidityAdd p) hstack hI hσ0 hk hp hc hl hu hkb hpb
        hlo hf hsrc hgas hp2 hfree hret rd2 with
        hog | ⟨post, z, out, hb, hcall, henv, hworld, ho, hr⟩
      · exact .inl hog
      refine .inr ⟨post, z, out, (fun _ _ => hcall), (fun _ _ => hb), henv, hworld, ho, ?_⟩
      simpa only [afterLiquidityTraceResult, if_neg hself, if_pos ha] using hr
    · rw [afterLiquiditySelection, if_neg ha] at hs
      refine .inr ⟨evm, false, .empty, (fun _ hh => (ha hh).elim),
        (fun _ hh => (ha hh).elim), hI, hσ0, by decide, ?_⟩
      simpa only [afterLiquidityTraceResult, if_neg hself, if_neg ha] using hs

end Benchmarks.UniswapV4PoolManager
