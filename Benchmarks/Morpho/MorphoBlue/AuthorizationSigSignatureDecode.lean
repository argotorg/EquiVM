import Benchmarks.Morpho.MorphoBlue.AuthorizationSigSignatureSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000


def authorizationSignatureStack (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 416, UInt256.ofNat 768, authorizationDigest v a, UInt256.ofNat 0,
    signatureRecoveryWord cd, UInt256.ofNat 224, solcAddrMask, UInt256.ofNat 128,
    UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem morphoAuthorizationSignatureDecode {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hstack : R.length + 24 ≤ 1024)
    (hv : (signatureRecoveryWord ee.calldata).toNat < 256)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6347)
      (authorizationDigestStack R) (authorizationDigestMem v a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6372)
      (authorizationSignatureStack v a ee.calldata R) (authorizationDigestReadyMem v a)
      aw' out σ k' C' := by
  have hm : UInt256.land (signatureRecoveryWord ee.calldata) (UInt256.ofNat 255) =
      signatureRecoveryWord ee.calldata := u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide) hv
  have r := morphoBlocks.morpho_block_6347_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 14 ≤ 1024; omega)
    (by
      change UInt256.sub (signatureRecoveryWord ee.calldata)
        (UInt256.land (signatureRecoveryWord ee.calldata) (UInt256.ofNat 255)) = _
      rw [hm, u256_sub_self]; rfl) h
  have hp := authorizationDigestReadyMem_properties v a
  dsimp only [morphoBlocks.morpho_block_6347_fallthrough_stack,
    morphoBlocks.morpho_block_6347_fallthrough_memory] at r
  change RD _ _ _ _ _
    ([UInt256.ofNat 416, UInt256.ofNat 768,
      keccakWord (UInt256.ofNat 672) (memLoad (UInt256.ofNat 640) (authorizationDigestReadyMem v a))
        (authorizationDigestReadyMem v a), UInt256.ofNat 0,
      UInt256.land (signatureRecoveryWord ee.calldata) (UInt256.ofNat 255),
      UInt256.ofNat 224, solcAddrMask, UInt256.ofNat 128, UInt256.ofNat 32,
      UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R)
    (authorizationDigestReadyMem v a) _ _ _ _ _ at r
  rw [hp.2.2.1, hp.2.2.2, hm] at r
  exact ⟨_, _, _, r⟩

theorem morphoAuthorizationSignatureDecodeRevert {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hstack : R.length + 24 ≤ 1024)
    (hv : ¬ (signatureRecoveryWord ee.calldata).toNat < 256)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6347)
      (authorizationDigestStack R) (authorizationDigestMem v a) aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : (UInt256.land (signatureRecoveryWord ee.calldata) (UInt256.ofNat 255)).toNat < 256 :=
    u256LandMaskToNatLtOfToNat (bits := 8) _ _ (by decide)
  have hn : signatureRecoveryWord ee.calldata ≠
      UInt256.land (signatureRecoveryWord ee.calldata) (UInt256.ofNat 255) := by
    intro he; exact hv (he.symm ▸ hm)
  have r := morphoBlocks.morpho_block_6347_taken (immWords := wordsOf (immStore v))
    (by change R.length + 14 ≤ 1024; omega) (u256_sub_ne_zero_of_ne hn)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_6705 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 6 ≤ 1024; omega) r

end Benchmarks.Morpho.MorphoBlue
