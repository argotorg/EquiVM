import Benchmarks.Morpho.MorphoBlue.AuthorizationSigMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationNonceStack (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 256, UInt256.ofNat 224, UInt256.ofNat 256, UInt256.ofNat 128,
    UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem morphoAuthorizationTimestampCheck {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 22 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5940)
      (authorizationDecodedStack a R) (authorizationDecodedMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.gt (UInt256.ofNat ee.header.timestamp) a.deadline),
        UInt256.ofNat 288, UInt256.ofNat 6004] ++ authorizationNonceStack R)
      (authorizationExpiredMem a) aw' out σ k' C' := by
  have hf := authorizationDecodedMem_free a
  have rd0 := morphoBlocks.morpho_block_5940 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_5940_stack] at rd0
  rw [hf] at rd0
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAlloc64 (v := v) (ret := UInt256.ofNat 5955)
    (R := [a.deadline, UInt256.ofNat 288, UInt256.ofNat 6004] ++ authorizationNonceStack R)
    (by simp [authorizationNonceStack]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd0
  have rd2 := morphoBlocks.morpho_block_5955 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 11 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [authorizationExpiredMem, morphoErrorMem]
  rw [hf]
  exact ⟨_, _, _, rd2⟩

theorem morphoAuthorizationTimestampOk {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 22 ≤ 1024)
    (ht : (UInt256.ofNat ee.header.timestamp).toNat ≤ a.deadline.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5940)
      (authorizationDecodedStack a R) (authorizationDecodedMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6004)
      (authorizationNonceStack R) (authorizationExpiredMem a) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationTimestampCheck (v := v) a hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (ret := UInt256.ofNat 6004)
    (R := authorizationNonceStack R) (by simp [authorizationNonceStack]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [ugt_zero ht]; decide) rd1
  exact ⟨_, _, _, rd2⟩

theorem morphoAuthorizationTimestampRevert {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 22 ≤ 1024)
    (ht : ¬ (UInt256.ofNat ee.header.timestamp).toNat ≤ a.deadline.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5940)
      (authorizationDecodedStack a R) (authorizationDecodedMem a) aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationTimestampCheck (v := v) a hstack h
  have hp := (authorizationExpiredMem_properties a).2.2.2
  exact morphoRequireFalseShort (v := v) (ret := UInt256.ofNat 6004)
    (R := authorizationNonceStack R) (by simp [authorizationNonceStack]; omega)
    (by rw [ugt_one (by omega)]; rfl) (by rw [hp]; decide) (by rw [hp]; decide) rd1

end Benchmarks.Morpho.MorphoBlue
