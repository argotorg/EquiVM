import Benchmarks.UniswapV4PoolManager.BeforeLiquidityBranchTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeLiquidityTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm post : State) (mem rdata : ByteArray) (free src params len keyPtr a b : UInt256)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (hook : AccountAddress) (z : Bool) (out : ByteArray)
    (R : List UInt256) : Prop :=
  let old := beforeLiquidityContinuation v I g s0 mem rdata evm.accountMap src params len keyPtr a b R
  let called := fun add =>
    if z = true ∧ hookReplyValid (beforeLiquidityPayload add I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) out then
      beforeLiquidityContinuation v I g s0
        (beforeLiquidityReplyMemory add I.calldata mem src.toNat free len I.source key p out) out
        post.accountMap src params len keyPtr a b R
    else RDrev (deployedRuntime v) g s0
  if I.source = hook then old
  else if beforeLiquidityEnabled hook p true then called true
  else if beforeLiquidityEnabled hook p false then called false
  else old

theorem beforeLiquidityHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free a b keyPtr paramsPtr src len : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (hstack : R.length+28 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hw : accountWord hook = key.hooks)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060)
    -- The first block pays 46 gas before entering the hook-selection routine.
    (hpaid : Cₘ aw ≤ C+46)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨5474⟩
      (src :: paramsPtr :: len :: keyPtr :: a :: b :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      (∀ add, I.source ≠ hook → beforeLiquidityEnabled hook p add →
        callViaEVM evm hook 0 (beforeLiquidityPayload add I.source key p
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out)) ∧
      (∀ add, I.source ≠ hook → beforeLiquidityEnabled hook p add →
        AllocationBounds free (beforeLiquidityAllocationSize len)) ∧
      (∀ add, I.source ≠ hook → beforeLiquidityEnabled hook p add →
        z = true ∧ hookReplyValid (beforeLiquidityPayload add I.source key p
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out →
        (beforeLiquidityFree free len).toNat+out.size+4096 ≤ solcMaxU64) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      beforeLiquidityTraceResult v I g s0 evm post mem rdata free src paramsPtr len keyPtr a b key p hook z out R := by
  have hload : memLoad (keyPtr+UInt256.ofNat 128) mem = accountWord hook :=
    (hk.load (i := 4) (word := key.hooks) rfl).trans hw.symm
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  have hcond : UInt256.sub (UInt256.ofNat I.source.val)
      (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128) mem)
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = ⟨0⟩ ↔ I.source = hook := by
    rw [hload, hclean, u256_sub_eq_zero_iff_eq]
    exact heq.symm
  by_cases hself : I.source = hook
  · have rd := poolManager_block_5474_fallthrough (by simp only [List.length_cons]; omega) (hcond.mpr hself) h
    simp only [poolManager_block_5474_fallthrough_stack, hload, hclean] at rd
    refine .inr ⟨evm, false, .empty, (fun _ hn _ => (hn hself).elim),
      (fun _ hn _ => (hn hself).elim), (fun _ hn _ _ => (hn hself).elim), hI, hσ0, by decide, ?_⟩
    rw [beforeLiquidityTraceResult, if_pos hself]
    refine ⟨_, _, _, _, _, ?_, rd⟩
    dsimp only [memExpansionCost]
    omega
  · have rd := poolManager_block_5474_taken (by simp only [List.length_cons]; omega)
      (fun hh => hself (hcond.mp hh)) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_5474_taken_stack, hload, hclean] at rd
    have hpaid' : Cₘ (M aw (keyPtr+UInt256.ofNat 128) ⟨32⟩) ≤
        C+(46+memExpansionCost aw (keyPtr+UInt256.ofNat 128) ⟨32⟩) := by
      dsimp only [memExpansionCost]; omega
    have hd : memLoad (paramsPtr+UInt256.ofNat 64) mem = p.delta :=
      hp.word_load (i := 2) (word := p.delta) rfl (by rw [uadd_word_ofNat_toNat paramsPtr 64 (by omega)])
    have hs := beforeLiquiditySelectTrace v (by omega) hpaid' hd rd
    have hex (ha : beforeLiquidityEnabled hook p true) (hr : beforeLiquidityEnabled hook p false) : False := by
      have hp := ha.1
      have hn := hr.1
      change 0 < EVM.signed p.delta at hp
      change EVM.signed p.delta ≤ 0 at hn
      omega
    by_cases ha : beforeLiquidityEnabled hook p true
    · rw [beforeLiquiditySelection, if_pos ha] at hs
      rcases beforeLiquidityBranchCallTrace v true hstack hI hσ0 hk hp hc hl hu hkb hpb hlo hf hsrc hgas hfree hs with
        hog | ⟨post, z, out, hb, hcall, henv, hworld, ho, hbound, hr⟩
      · exact .inl hog
      refine .inr ⟨post, z, out, ?_, (fun _ _ _ => hb), ?_, henv, hworld, ho, ?_⟩
      · intro add _ hen
        cases add with
        | false => exact (hex ha hen).elim
        | true => exact hcall
      · intro add _ hen hv
        cases add with
        | false => exact (hex ha hen).elim
        | true => exact hbound hv
      · simpa only [beforeLiquidityTraceResult, if_neg hself, if_pos ha] using hr
    · rw [beforeLiquiditySelection, if_neg ha] at hs
      by_cases hn : beforeLiquidityEnabled hook p false
      · rw [if_pos hn] at hs
        rcases beforeLiquidityBranchCallTrace v false hstack hI hσ0 hk hp hc hl hu hkb hpb hlo hf hsrc hgas hfree hs with
          hog | ⟨post, z, out, hb, hcall, henv, hworld, ho, hbound, hr⟩
        · exact .inl hog
        refine .inr ⟨post, z, out, ?_, (fun _ _ _ => hb), ?_, henv, hworld, ho, ?_⟩
        · intro add _ hen
          cases add with
          | false => exact hcall
          | true => exact (ha hen).elim
        · intro add _ hen hv
          cases add with
          | false => exact hbound hv
          | true => exact (ha hen).elim
        · simpa only [beforeLiquidityTraceResult, if_neg hself, if_neg ha, if_pos hn] using hr
      · rw [if_neg hn] at hs
        have himpossible (add : Bool) : ¬beforeLiquidityEnabled hook p add := by cases add <;> assumption
        refine .inr ⟨evm, false, .empty, (fun add _ hen => (himpossible add hen).elim),
          (fun add _ hen => (himpossible add hen).elim),
          (fun add _ hen _ => (himpossible add hen).elim), hI, hσ0, by decide, ?_⟩
        simpa only [beforeLiquidityTraceResult, if_neg hself, if_neg ha, if_neg hn] using hs

end Benchmarks.UniswapV4PoolManager
