import Benchmarks.Morpho.MorphoBlue.AuthorizationSigTimestamp
import Benchmarks.Morpho.MorphoBlue.AuthorizationSigSourceNonce
import Benchmarks.Morpho.MorphoBlue.IncrementRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationHashTail (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 256, UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask,
    UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192,
    UInt256.ofNat 0] ++ R

def authorizationNonceMem (a : AuthorizationWords) : ByteArray :=
  twoWordHashMem a.authorizer (UInt256.ofNat 7) (authorizationExpiredMem a)

def authorizationNonceStoreStack (a : AuthorizationWords) (n : UInt256) (R : List UInt256) : List UInt256 :=
  [n + UInt256.ofNat 1, authorizationNonceSlot a, n, a.nonce, UInt256.ofNat 6120] ++
    authorizationHashTail R

theorem morphoAuthorizationNoncePrepare {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hc : a.Canonical)
    (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6004)
      (authorizationNonceStack R) (authorizationExpiredMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13051)
      ([authorizationUsedNonce a σ ee, UInt256.ofNat 6058, authorizationNonceSlot a,
        authorizationUsedNonce a σ ee, a.nonce, UInt256.ofNat 6120] ++ authorizationHashTail R)
      (authorizationNonceMem a) aw' out σ k' C' := by
  have hp := (authorizationExpiredMem_properties a).2.2.1
  have h0 : memLoad (UInt256.ofNat 128) (authorizationExpiredMem a) = a.authorizer := hp ⟨0, by decide⟩
  have h3 : memLoad (UInt256.ofNat 224) (authorizationExpiredMem a) = a.nonce := hp ⟨3, by decide⟩
  obtain ⟨k1, C1, rd1⟩ := morphoBlocks.morpho_block_6004 (immWords := wordsOf (immStore v))
    (by change R.length + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_6004_stack, morphoBlocks.morpho_block_6004_memory] at rd1
  have hm : UInt256.land a.authorizer
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = a.authorizer :=
    solcAddrMask_clean hc.1
  rw [h0, h3, hm] at rd1
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (authorizationNonceMem a) =
      authorizationNonceSlot a := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (authorizationNonceMem a)) σ ee,
      UInt256.ofNat 6058, keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (authorizationNonceMem a),
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (authorizationNonceMem a)) σ ee,
      a.nonce, UInt256.ofNat 6120] ++ authorizationHashTail R)
    (authorizationNonceMem a) _ _ _ _ _ at rd1
  rw [hh] at rd1
  exact ⟨_, _, _, rd1⟩

theorem morphoAuthorizationNonceIncrement {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hc : a.Canonical)
    (hstack : R.length + 24 ≤ 1024)
    (hfit : (authorizationUsedNonce a σ ee).toNat + 1 < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6004)
      (authorizationNonceStack R) (authorizationExpiredMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6058)
      (authorizationNonceStoreStack a (authorizationUsedNonce a σ ee) R)
      (authorizationNonceMem a) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationNoncePrepare (v := v) a hc hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedIncrementOk (v := v)
    (ret := UInt256.ofNat 6058)
    (R := [authorizationNonceSlot a, authorizationUsedNonce a σ ee, a.nonce,
      UInt256.ofNat 6120] ++ authorizationHashTail R)
    (by simp [authorizationHashTail]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd1
  exact ⟨_, _, _, rd2⟩

theorem morphoAuthorizationNonceOverflow {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hc : a.Canonical)
    (hstack : R.length + 24 ≤ 1024)
    (hfit : UInt256.size ≤ (authorizationUsedNonce a σ ee).toNat + 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6004)
      (authorizationNonceStack R) (authorizationExpiredMem a) aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationNoncePrepare (v := v) a hc hstack h
  exact morphoCheckedIncrementOverflow (v := v)
    (ret := UInt256.ofNat 6058)
    (R := [authorizationNonceSlot a, authorizationUsedNonce a σ ee, a.nonce,
      UInt256.ofNat 6120] ++ authorizationHashTail R)
    (by simp [authorizationHashTail]; omega) hfit rd1

end Benchmarks.Morpho.MorphoBlue
