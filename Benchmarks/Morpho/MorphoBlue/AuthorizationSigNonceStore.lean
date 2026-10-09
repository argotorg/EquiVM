import Benchmarks.Morpho.MorphoBlue.AuthorizationSigNonceReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationInvalidNonceWord : UInt256 :=
  UInt256.ofNat 47688019310969423947805581323216735338428712860599360121287913556607181520896

def authorizationCheckedMem (a : AuthorizationWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 13) authorizationInvalidNonceWord (authorizationNonceMem a)

def authorizationNonceAccounts (a : AuthorizationWords) (n : UInt256) (σ : AccountMap)
    (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (authorizationNonceSlot a) (n + UInt256.ofNat 1)

theorem authorizationNonceMem_properties (a : AuthorizationWords) :
    (authorizationNonceMem a).size = 352 ∧
      memLoad (UInt256.ofNat 64) (authorizationNonceMem a) = UInt256.ofNat 352 ∧
      a.InMemory (authorizationNonceMem a) := by
  have hp := authorizationExpiredMem_properties a
  refine ⟨?_, ?_, hp.2.2.1.hash (by omega) _ _⟩
  · rw [authorizationNonceMem, twoWordHashMem_size_of_ge_64' _ _ (by omega), hp.1]
  · rw [authorizationNonceMem, twoWordHashMem_memLoad_above64 _ _ _
      (by decide) (by rw [hp.1]; decide), hp.2.1]

theorem authorizationCheckedMem_properties (a : AuthorizationWords) :
    (authorizationCheckedMem a).size = 416 ∧
      memLoad (UInt256.ofNat 64) (authorizationCheckedMem a) = UInt256.ofNat 416 ∧
      a.InMemory (authorizationCheckedMem a) ∧
      morphoErrorLength (authorizationCheckedMem a) (UInt256.ofNat 352) = UInt256.ofNat 13 := by
  have hp := authorizationNonceMem_properties a
  have hh := morphoErrorMem_properties (UInt256.ofNat 13) authorizationInvalidNonceWord
    (UInt256.ofNat 352) (authorizationNonceMem a) hp.1 hp.2.1 (by decide) (by decide)
  exact ⟨hh.1, hh.2.1, hp.2.2.message hp.1 hp.2.1 (by decide) (by decide) _ _, hh.2.2⟩

theorem morphoAuthorizationNonceStoreStatic {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out mem : ByteArray} {aw n slot : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 2 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6058)
      (n :: slot :: R) mem aw out σ k C) : RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨6058⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨6059⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r2 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨6060⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

theorem morphoAuthorizationNonceStoreCheck {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw n : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6058)
      (authorizationNonceStoreStack a n R) (authorizationNonceMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.eq a.nonce n, UInt256.ofNat 352, UInt256.ofNat 6120] ++ authorizationHashTail R)
      (authorizationCheckedMem a) aw' out (authorizationNonceAccounts a n σ ee) k' C' := by
  have hf := (authorizationNonceMem_properties a).2.1
  obtain ⟨k1, C1, rd1⟩ := morphoBlocks.morpho_block_6058 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 6 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_6058_stack] at rd1
  rw [hf] at rd1
  obtain ⟨a2, k2, C2, rd2⟩ := morphoAlloc64 (v := v) (ret := UInt256.ofNat 6073)
    (R := [a.nonce, n, UInt256.ofNat 352, UInt256.ofNat 6120] ++ authorizationHashTail R)
    (by simp [authorizationHashTail]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_6073 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  dsimp only [authorizationCheckedMem, morphoErrorMem]
  rw [hf]
  exact ⟨_, _, _, rd3⟩

theorem morphoAuthorizationNonceStoreOk {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw n : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true) (hn : a.nonce = n)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6058)
      (authorizationNonceStoreStack a n R) (authorizationNonceMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6120)
      (authorizationHashTail R) (authorizationCheckedMem a) aw' out
      (authorizationNonceAccounts a n σ ee) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationNonceStoreCheck (v := v) a hstack hperm h
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v) (ret := UInt256.ofNat 6120)
    (R := authorizationHashTail R) (by simp [authorizationHashTail]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hn, uInt256_eq_self]; decide) rd1
  exact ⟨_, _, _, rd2⟩

theorem morphoAuthorizationNonceStoreRevert {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw n : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true) (hn : a.nonce ≠ n)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6058)
      (authorizationNonceStoreStack a n R) (authorizationNonceMem a) aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAuthorizationNonceStoreCheck (v := v) a hstack hperm h
  have hp := (authorizationCheckedMem_properties a).2.2.2
  exact morphoRequireFalseShort (v := v) (ret := UInt256.ofNat 6120)
    (R := authorizationHashTail R) (by simp [authorizationHashTail]; omega)
    (u256_eq_of_ne hn) (by rw [hp]; decide) (by rw [hp]; decide) rd1

end Benchmarks.Morpho.MorphoBlue
