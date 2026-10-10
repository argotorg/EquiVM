import Benchmarks.UniswapV4PoolManager.DonateEventCorrect
import Benchmarks.UniswapV4PoolManager.AccountPoolCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateAccountingCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {f : Frame} {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len delta id junk j0 j1 : UInt256}
    {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hi : f.locals.get? "poolId" = some (wordBytes32Value id))
    (hkey : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hkl : 96 ≤ keyPtr.toNat)
    (hfit : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10284⟩
      (j0 :: j1 :: id :: (keyPtr+UInt256.ofNat 128) :: keyPtr :: src :: amount1 :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (donateTransition.body.drop 17) result ∧
      abiResultTrace donateTransition.returnType (deployedRuntime v) g s0 result := by
  have rd := poolManagerBlocks.poolManager_block_10284
    (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have ht := accountPoolCallCostTrace (ret := ⟨10297⟩) (target := I.source)
    (R := [id, keyPtr+UInt256.ofNat 128, keyPtr, src, amount1, amount0, len, delta, ⟨32⟩, junk]++R)
    f "__c7" v (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hI hkey (by omega) (by rw [deployedRuntime_jumps]; jump_dest) rd
  have hs := accountPoolCall hf (evalLocalValue (evm := evm) hk) (evalLocalValue hd)
    (show evalExpr? config f evm (.env .caller) = .ok (.address I.source) by
      simp only [evalExpr?, envValue, hI, pure]) "__c7"
  change ExecStmt config f evm donateTransition.body[17]!
    (resumeCallResult f "__c7" (accountPoolResult (accountPoolCalleeFrame f key delta I.source) evm key delta I.source)) at hs
  generalize hx : resumeCallResult f "__c7"
    (accountPoolResult (accountPoolCalleeFrame f key delta I.source) evm key delta I.source) = result at hs ht
  cases result with
  | ok ff post =>
    obtain ⟨rfl, rfl, aw1, k1, C1, hp1, rd1⟩ := ht
    have hI' := (accountPoolPost_env evm key delta I.source).trans hI
    have hσ0' := (accountPoolPost_world evm key delta I.source).trans hσ0
    have hf' : ({f with locals := f.locals.insert "__c7" .unit} : Frame).contract = contract := hf
    have hk' := (store_get_ne _ .unit (by decide : ("__c7" == "key") = false)).trans hk
    have h0' := (store_get_ne _ .unit (by decide : ("__c7" == "amount0") = false)).trans h0
    have h1' := (store_get_ne _ .unit (by decide : ("__c7" == "amount1") = false)).trans h1
    have hd' := (store_get_ne _ .unit (by decide : ("__c7" == "delta") = false)).trans hd
    have hb' := (store_get_ne _ .unit (by decide : ("__c7" == "hookData") = false)).trans hb
    have hi' := (store_get_ne _ .unit (by decide : ("__c7" == "poolId") = false)).trans hi
    have hfree' := (accountPoolMemory_load mem key delta I.source (UInt256.ofNat 64) (by decide)
      (by have := hkey.inBounds; change 96 ≤ mem.size; omega)).trans hfree
    rcases donateEventCorrect v hstack hI' hσ0' hf' hk' h0' h1' hd' hb' hi'
        (hkey.accountPool delta I.source (by omega)) hc hkb hkl hfit hsrc hgas (by omega) hfree' rd1 with
      hog | ⟨result, hbody, htrace⟩
    · exact .inl hog
    · exact .inr ⟨result, ExecBlock.consNormal hs hbody, htrace⟩
  | reverted => exact .inr ⟨.reverted, ExecBlock.consRevert hs, ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, ExecBlock.consStatic hs, ht⟩
  | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
