import Benchmarks.Morpho.MorphoBlue.AuthorizationSigRecoveredMemory
import Benchmarks.Morpho.MorphoBlue.WordCallOutputMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000


def authorizationNonceEventTopic : UInt256 :=
  UInt256.ofNat 96755043271346810483655308149819952342970126887685366761742111973171219597760

def authorizationVerifiedTail (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 224, UInt256.ofNat 128, solcAddrMask, solcAddrMask, authorizationNonceEventTopic,
    UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

def authorizationSignatureCheckWord (a : AuthorizationWords) (out : ByteArray) : UInt256 :=
  if ecrecoverWord out = UInt256.ofNat 0 then UInt256.ofNat 0 else UInt256.eq a.authorizer (ecrecoverWord out)

def authorizationInvalidSignatureWord : UInt256 :=
  UInt256.ofNat 47688019310969423947927603677703526806861028988571120983126164496379122024448

def authorizationVerifiedMem (v : MorphoImmutables) (a : AuthorizationWords)
    (cd out : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 17) authorizationInvalidSignatureWord (authorizationRecoveredMem v a cd out)

theorem morphoAuthorizationRecoveryFailed {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (a : AuthorizationWords) (ho : EcrecoverOutput out) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6410)
      (UInt256.ofNat 0 :: authorizationRecoveryTail R) (authorizationRecoveredMem v a ee.calldata out)
      aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r := morphoBlocks.morpho_block_6410_taken (immWords := wordsOf (immStore v))
    (by simp [authorizationRecoveryTail]; omega) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_6694 (immWords := wordsOf (immStore v))
    (by change R.length + 11 ≤ 1024; omega)
    (by
      simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add]
      rw [UInt256.toNat_ofNat_of_lt (by have hh := ho.size; change out.size < 2 ^ 256; omega)]) r

theorem morphoAuthorizationRecoveryCompare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (a : AuthorizationWords) (hc : a.Canonical) (ho : EcrecoverOutput out)
    (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6415)
      (authorizationRecoveryTail R) (authorizationRecoveredMem v a ee.calldata out) aw out σ k C) :
    ∃ aw' k' C' discard, RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6467)
      ([discard, authorizationSignatureCheckWord a out, UInt256.ofNat 6527] ++ authorizationVerifiedTail R)
      (authorizationRecoveredMem v a ee.calldata out) aw' out σ k' C' := by
  have hp := authorizationRecoveredMem_properties v a ee.calldata out ho
  have hm := solcAddrMask_clean ho.wordCanonical
  have hm' : UInt256.land (memLoad (UInt256.ofNat 0) (authorizationRecoveredMem v a ee.calldata out))
      solcAddrMask = ecrecoverWord out := by rw [hp.2.2.1, hm]
  have ha : memLoad (UInt256.ofNat 128) (authorizationRecoveredMem v a ee.calldata out) = a.authorizer :=
    hp.2.1 ⟨0, by decide⟩
  have hma := solcAddrMask_clean hc.1
  by_cases hz : ecrecoverWord out = UInt256.ofNat 0
  · have r := morphoBlocks.morpho_block_6415_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 14 ≤ 1024; omega) (by rw [hm', hz]; decide) h
    dsimp only [morphoBlocks.morpho_block_6415_fallthrough_stack] at r
    rw [hm', hz] at r
    simp only [authorizationSignatureCheckWord, hz, ↓reduceIte]
    exact ⟨_, _, _, _, r⟩
  · have hi : UInt256.isZero (UInt256.isZero (ecrecoverWord out)) ≠ UInt256.ofNat 0 := by
      rw [isZero_eq_zero_of_ne hz]; decide
    have r := morphoBlocks.morpho_block_6415_taken (immWords := wordsOf (immStore v))
      (by change R.length + 14 ≤ 1024; omega) (by rw [hm']; exact hi)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    have r1 := morphoBlocks.morpho_block_6681 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 7 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) r
    dsimp only [morphoBlocks.morpho_block_6681_stack,
      morphoBlocks.morpho_block_6415_taken_stack] at r1
    rw [hm', ha, hma] at r1
    simp only [authorizationSignatureCheckWord, hz, ↓reduceIte]
    exact ⟨_, _, _, _, r1⟩


theorem authorizationVerifiedMem_properties (v : MorphoImmutables) (a : AuthorizationWords)
    (cd out : ByteArray) (ho : EcrecoverOutput out) :
    (authorizationVerifiedMem v a cd out).size = 896 ∧
      a.InMemory (authorizationVerifiedMem v a cd out) ∧
      memLoad (UInt256.ofNat 64) (authorizationVerifiedMem v a cd out) = UInt256.ofNat 832 ∧
      morphoErrorLength (authorizationVerifiedMem v a cd out) (UInt256.ofNat 768) = UInt256.ofNat 17 := by
  have hp := authorizationRecoveredMem_properties v a cd out ho
  have hm := morphoErrorMem_properties_general (UInt256.ofNat 17) authorizationInvalidSignatureWord
    (UInt256.ofNat 768) (authorizationRecoveredMem v a cd out) (by decide) hp.2.2.2 (by omega)
    (by rw [hp.1]; exact USize.size_pos) (by decide)
  refine ⟨?_, ?_, hm.2.1.trans (by decide), hm.2.2⟩
  · rw [authorizationVerifiedMem, hm.1, hp.1]; rfl
  · exact hp.2.1.prefix (morphoErrorMem_prefix _ _ (by omega) hp.2.2.2
      (by rw [hp.1]; exact USize.size_pos) (by decide)) (by decide) (by omega)

theorem morphoAuthorizationSignatureMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw discard : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (a : AuthorizationWords) (ho : EcrecoverOutput out) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6467)
      ([discard, authorizationSignatureCheckWord a out, UInt256.ofNat 6527] ++ authorizationVerifiedTail R)
      (authorizationRecoveredMem v a ee.calldata out) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([authorizationSignatureCheckWord a out, UInt256.ofNat 768, UInt256.ofNat 6527] ++ authorizationVerifiedTail R)
      (authorizationVerifiedMem v a ee.calldata out) aw' out σ k' C' := by
  have hf := (authorizationRecoveredMem_properties v a ee.calldata out ho).2.2.2
  have r := morphoBlocks.morpho_block_6467 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_6467_stack] at r
  rw [hf] at r
  obtain ⟨a1, k1, C1, r1⟩ := morphoAlloc64 (v := v) (ret := UInt256.ofNat 6481)
    (R := [authorizationSignatureCheckWord a out, UInt256.ofNat 768, UInt256.ofNat 6527] ++
      authorizationVerifiedTail R)
    (by simp [authorizationVerifiedTail]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) r
  have r2 := morphoBlocks.morpho_block_6481 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) r1
  dsimp only [authorizationVerifiedMem, morphoErrorMem]
  rw [hf]
  exact ⟨_, _, _, r2⟩

def AuthorizationSignatureValid (a : AuthorizationWords) (out : ByteArray) : Prop :=
  ecrecoverWord out ≠ UInt256.ofNat 0 ∧ a.authorizer = ecrecoverWord out

instance (a : AuthorizationWords) (out : ByteArray) : Decidable (AuthorizationSignatureValid a out) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem morphoAuthorizationSignatureVerify {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (a : AuthorizationWords) (hc : a.Canonical) (ho : EcrecoverOutput out)
    (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6410)
      (UInt256.ofNat 1 :: authorizationRecoveryTail R) (authorizationRecoveredMem v a ee.calldata out)
      aw out σ k C) :
    if AuthorizationSignatureValid a out then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6527) (authorizationVerifiedTail R)
        (authorizationVerifiedMem v a ee.calldata out) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r0 := morphoBlocks.morpho_block_6410_fallthrough (immWords := wordsOf (immStore v))
    (by simp [authorizationRecoveryTail]; omega) (by decide) h
  obtain ⟨a1, k1, C1, discard, r1⟩ := morphoAuthorizationRecoveryCompare (v := v) a hc ho hstack r0
  obtain ⟨a2, k2, C2, r2⟩ := morphoAuthorizationSignatureMessage (v := v) a ho hstack r1
  by_cases hv : AuthorizationSignatureValid a out
  · rw [if_pos hv]
    have hcond : UInt256.isZero (authorizationSignatureCheckWord a out) = UInt256.ofNat 0 := by
      rw [authorizationSignatureCheckWord, if_neg hv.1, hv.2, uInt256_eq_self]; decide
    obtain ⟨k3, C3, r3⟩ := morphoRequireTrue (v := v) (ret := UInt256.ofNat 6527)
      (R := authorizationVerifiedTail R) (by simp [authorizationVerifiedTail]; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hcond r2
    exact ⟨_, _, _, r3⟩
  · rw [if_neg hv]
    have hcond : authorizationSignatureCheckWord a out = UInt256.ofNat 0 := by
      by_cases hz : ecrecoverWord out = UInt256.ofNat 0
      · simp only [authorizationSignatureCheckWord, hz, ↓reduceIte]
      · rw [authorizationSignatureCheckWord, if_neg hz]
        exact u256_eq_of_ne (fun he ↦ hv ⟨hz, he⟩)
    have hp := (authorizationVerifiedMem_properties v a ee.calldata out ho).2.2.2
    exact morphoRequireFalseShort (v := v) (ret := UInt256.ofNat 6527)
      (R := authorizationVerifiedTail R) (by simp [authorizationVerifiedTail]; omega)
      hcond (by rw [hp]; decide) (by rw [hp]; decide) r2

end Benchmarks.Morpho.MorphoBlue
