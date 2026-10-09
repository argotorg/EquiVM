import Benchmarks.Morpho.MorphoBlue.AuthorizationSigSourceDecode
import Benchmarks.Morpho.MorphoBlue.SafeTransferEncode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationDecodedMem (a : AuthorizationWords) : ByteArray :=
  writeCascade (writeWord solcFreePtrMem 64 (UInt256.ofNat 288))
    (returnWordWrites 128 [a.authorizer, a.authorized, a.enabled, a.nonce, a.deadline])

def authorizationDecodedStack (a : AuthorizationWords) (R : List UInt256) : List UInt256 :=
  [a.deadline, UInt256.ofNat 256, UInt256.ofNat 224, UInt256.ofNat 256,
    UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem morphoAuthorizationSigDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hs : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5766) (UInt256.ofNat 0 :: R) solcFreePtrMem aw out σ k C) :
    (¬ AuthorizationSigBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (AuthorizationSigBounds ee.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5940)
        (authorizationDecodedStack (authorizationFromCalldata ee.calldata) R)
        (authorizationDecodedMem (authorizationFromCalldata ee.calldata)) aw' out σ k' C') := by
  have hbad (hc : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 256) = ⟨1⟩) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_5766_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (by rw [u256_add_comm, wordAddNegFour, hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_1234 (immWords := wordsOf (immStore v))
      (by omega) rd
  by_cases hl : 260 ≤ ee.calldata.size
  swap
  · exact .inl ⟨fun hb ↦ hl hb.1,
      hbad (solcCalldataStaticLenCheckShort (words := 8) hs (by omega) hsize (by decide))⟩
  by_cases hh : ee.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl ⟨fun hb ↦ hh hb.2.1,
      hbad (solcCalldataStaticLenCheckHuge (words := 8) (by omega) hsize (by decide))⟩
  have rd1 := morphoBlocks.morpho_block_5766_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by
      rw [u256_add_comm, wordAddNegFour]
      exact solcCalldataStaticLenCheckOk (words := 8) hl hh hsize) h
  have hc5 := solcCalldataStaticLenCheckOk (words := 5) (by omega : 4 + 32 * 5 ≤ ee.calldata.size) hh hsize
  have rd2 := morphoBlocks.morpho_block_5811_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega) (by
      change UInt256.sgt (UInt256.ofNat 160) _ = _
      change UInt256.slt _ (UInt256.ofNat 160) = _
      rw [u256_add_comm, wordAddNegFour]
      exact hc5) rd1
  have rd3 := morphoBlocks.morpho_block_5818 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hfree : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  dsimp only [morphoBlocks.morpho_block_5818_stack] at rd3
  rw [hfree] at rd3
  obtain ⟨a4, k4, C4, rd4⟩ := morphoTransferAllocate (v := v) true
    (ret := UInt256.ofNat 5829) (R := UInt256.ofNat 128 :: UInt256.ofNat 256 :: UInt256.ofNat 0 :: R)
    (by simp; omega) (by rw [morphoPatchedValidJumps v]; jump_dest) (by decide) rd3
  have rd5 := morphoBlocks.morpho_block_5829 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 2 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  by_cases ha : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
  swap
  · exact .inl ⟨fun hb ↦ ha hb.2.2.1,
      morphoDecodeAddress4Revert (v := v) (by simp; omega) ha rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoDecodeAddress4Ok (v := v)
    (ret := UInt256.ofNat 5837) (R := UInt256.ofNat 128 :: UInt256.ofNat 256 :: UInt256.ofNat 0 :: R)
    (by simp; omega) (by rw [morphoPatchedValidJumps v]; jump_dest) ha rd5
  have rd7 := morphoBlocks.morpho_block_5837 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd6
  by_cases hb : (calldataWord ee.calldata 36).toNat < EVM.addressModulus
  swap
  · exact .inl ⟨fun hc ↦ hb hc.2.2.2.1,
      morphoDecodeAddress36Revert (v := v) (by simp; omega) hb rd7⟩
  obtain ⟨k8, C8, rd8⟩ := morphoDecodeAddress36Ok (v := v)
    (ret := UInt256.ofNat 5847) (R := UInt256.ofNat 128 :: UInt256.ofNat 256 :: UInt256.ofNat 0 :: R)
    (by simp; omega) (by rw [morphoPatchedValidJumps v]; jump_dest) hb rd7
  by_cases hc : calldataWord ee.calldata 68 = ⟨0⟩ ∨ calldataWord ee.calldata 68 = ⟨1⟩
  swap
  · have rd := morphoBlocks.morpho_block_5847_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (by
        apply u256_sub_ne_zero_of_ne
        intro he
        exact hc ((boolWordClean_iff _).mp he.symm))
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd8
    exact .inl ⟨fun hz ↦ hc hz.2.2.2.2,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
        (by change R.length + 6 + 2 ≤ 1024; omega) rd⟩
  have rd9 := morphoBlocks.morpho_block_5847_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by
      change UInt256.sub (calldataWord ee.calldata 68)
        (UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 68))) = _
      rw [(boolWordClean_iff _).mpr hc, u256_sub_self]; rfl) rd8
  have rd10 := morphoBlocks.morpho_block_5871_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by
      rw [show UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772 =
        UInt256.sub ⟨0⟩ (UInt256.ofNat 164) by decide, word_add_sub_zero]
      exact solcDecodeLenCheckOk (by exact hl) (by change ee.calldata.size < 2 ^ 255 + 164; omega) hsize (by decide)) rd9
  exact .inr ⟨⟨hl, hh, ha, hb, hc⟩, _, _, _, rd10⟩

end Benchmarks.Morpho.MorphoBlue
