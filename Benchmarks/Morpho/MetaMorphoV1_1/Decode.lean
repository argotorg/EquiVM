import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Shared calldata guards and the runtime address decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

-- LIBRARY CANDIDATE: normalize the via-IR NOT/ADD spelling of calldata size minus four.
theorem calldataNot3_eq_sub {size : Nat} (h4 : 4 ≤ size) (hsize : size < UInt256.size) :
    UInt256.lnot ⟨3⟩ + UInt256.ofNat size = UInt256.sub (UInt256.ofNat size) ⟨4⟩ := by
  rw [lnot3_add_returnSize h4 hsize]
  apply u256_inj
  rw [ulit_toNat' _ (by omega)]
  exact (usub_ofNat_word_toNat (c := ⟨4⟩) h4 hsize).symm

-- LIBRARY CANDIDATE: the SUB-based ABI address check passes exactly for a clean word.
theorem addressSubMask_zero (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.sub w (UInt256.land w solcAddrMask) = ⟨0⟩ := by
  rw [solcAddrMask_clean hcanon, u256_sub_eq_zero_iff_eq]

-- LIBRARY CANDIDATE: a noncanonical address has a nonzero SUB-based check result.
theorem addressSubMask_nonzero (w : UInt256) (hnc : ¬ w.toNat < EVM.addressModulus) :
    UInt256.sub w (UInt256.land w solcAddrMask) ≠ ⟨0⟩ := by
  intro hz
  have heq := u256_sub_eq_zero_iff_eq.mp hz
  have hc := solcAddrMask_result_canonical w
  rw [← heq] at hc
  exact hnc hc

-- GENERALIZES the single-transition RDrev.reEquivNonPayable to an already dispatched arm.
theorem dispatchedRevert {cfg : Config} {ctr : ContractDecl} {transition : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hd : dispatchMsg ctr I.calldata = some transition)
    (h : RDrev code g (initState σ σ₀ g A I))
    (hbody : ∀ args, ExecTransitionBody cfg ctr (initState σ σ₀ g A I)
      args transition.body .reverted imms)
    (hfallback : ctr.fallback = none := by rfl) (hreceive : ctr.receive = none := by rfl) :
    runtimeRefinementFor cfg ctr σ σ₀ g.toUInt256 A I imms := by
  cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      (transitionSignature transition).paramTypes I.calldata with
  | none => exact h.reEquivDecodingFailed hcode hd hdec hfallback hreceive
  | some args =>
    exact h.reEquivExecutionRevert hcode hd hdec (hbody args) hfallback hreceive

set_option maxRecDepth 2000 in
theorem decodeAddressAt4 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  have rd11184 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11163_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata 4)
        (UInt256.land (calldataWord I.calldata 4) solcAddrMask) = ⟨0⟩
      exact addressSubMask_zero _ hcanon) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11184
    (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using (show R.length + 2 ≤ 1024 by omega))
    hvalid rd11184
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem decodeAddressAt4Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11163_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata 4)
        (UInt256.land (calldataWord I.calldata 4) solcAddrMask) ≠ ⟨0⟩
      exact addressSubMask_nonzero _ hnc)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v))
    (by simpa only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_11163_taken_stack,
      List.length_cons] using (show R.length + 1 + 1 + 2 ≤ 1024 by omega)) rd917

set_option maxRecDepth 2000 in
theorem decodeAddressAt36 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11185⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (calldataWord I.calldata 36 :: R) mem aw rdata σ k' C' := by
  have rd11206 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11185_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata 36)
        (UInt256.land (calldataWord I.calldata 36) solcAddrMask) = ⟨0⟩
      exact addressSubMask_zero _ hcanon) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11206
    (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using (show R.length + 2 ≤ 1024 by omega))
    hvalid rd11206
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem decodeAddressAt36Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11185⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11185_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (calldataWord I.calldata 36)
        (UInt256.land (calldataWord I.calldata 36) solcAddrMask) ≠ ⟨0⟩
      exact addressSubMask_nonzero _ hnc)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v))
    (by simpa only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_11185_taken_stack,
      List.length_cons] using (show R.length + 1 + 1 + 2 ≤ 1024 by omega)) rd917

end Benchmarks.Morpho.MetaMorphoV1_1
