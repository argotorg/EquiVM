import Benchmarks.UniswapV4PoolManager.InitializeValidationTrace
import Benchmarks.UniswapV4PoolManager.InitializeHooksCorrect
import Benchmarks.UniswapV4PoolManager.NoDelegateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem initializeBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {key : PoolKeyWords} {price free keyPtr junk aw : UInt256}
    {mem rdata : ByteArray} {old : Value} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (him : f.immutables = immStore v)
    (hc : PoolKeyCanonical key) (hprice : price.toNat < 2^160)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "tick" = some old) (hn : f.locals.get? "_pools" = none)
    (hv : PoolKeyView mem keyPtr key) (hl : 96 ≤ keyPtr.toNat)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hs : free.toNat ≤ 1024) (haw : aw.toNat ≤ 2048)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4081⟩
      (price :: keyPtr :: price :: junk :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm (initializeTransition.body.drop 5) result ∧
      signedResultTrace ⟨24, by decide⟩ (deployedRuntime v) g s0 result := by
  have rd1 := poolManagerBlocks.poolManager_block_4081 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hdelegate := noDelegateCallTrace v (by simp only [List.length_cons]; omega)
    (by rw [deployedRuntime_jumps]; jump_dest) rd1
  have hcall := noDelegateCallCall (evm := evm) v hf him "__c0"
  rw [hI] at hcall
  by_cases heq : I.codeOwner = v.original
  · rw [if_pos heq] at hdelegate hcall
    obtain ⟨k1, C1, rd2⟩ := hdelegate
    let f1 : Frame := {f with locals := f.locals.insert "__c0" .unit}
    have hkey : f1.locals.get? "key" = some (poolKeyValue key) :=
      (store_get_ne _ _ (by decide : ("__c0" == "key") = false)).trans hk
    have hsource := initializeValidationSource (f := f1) (evm := evm) hf hc hkey
    have htrace := initializeValidationTrace v (by simp only [List.length_cons]; omega)
      hv hc haw (by omega) rd2
    by_cases hvalid : initializeKeyValid key
    · rw [if_pos hvalid] at hsource htrace
      obtain ⟨aw2, k2, C2, haw2, rd3⟩ := htrace
      let f2 := initializeValidationFrame f1 key
      have hkeep (name : Ident) (h0 : ("__c0" == name) = false)
          (h1 : ("__c1" == name) = false) (h2 : ("lpFee" == name) = false) :
          f2.locals.get? name = f.locals.get? name := store_get_ne3 _ _ _ _ h0 h1 h2
      rcases initializeHooksCorrect (f := f2) v hstack hI hσ0 hf hc hprice
          (initialLPFeeWord_bound hvalid.2.2.2.2)
          ((hkeep "key" (by decide) (by decide) (by decide)).trans hk)
          ((hkeep "sqrtPriceX96" (by decide) (by decide) (by decide)).trans hp)
          (store_get_self _ _ _)
          ((hkeep "tick" (by decide) (by decide) (by decide)).trans ht)
          ((hkeep "_pools" (by decide) (by decide) (by decide)).trans hn)
          hv hl hb hs haw2 hgas hfree rd3 with hog | ⟨result, hbody, hr⟩
      · exact .inl hog
      · exact .inr ⟨result, execFuncBody_prepend (execBlock_singleton hcall)
          (execFuncBody_prepend hsource hbody), hr⟩
    · rw [if_neg hvalid] at hsource htrace
      exact .inr ⟨.reverted, execFuncBody_prepend (execBlock_singleton hcall) hsource, htrace⟩
  · rw [if_neg heq] at hdelegate hcall
    exact .inr ⟨.reverted, .execBlockRevert (ExecBlock.consRevert hcall), hdelegate⟩

end Benchmarks.UniswapV4PoolManager
