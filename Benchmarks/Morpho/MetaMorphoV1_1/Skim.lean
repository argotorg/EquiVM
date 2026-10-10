import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SkimEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SkimSimulation

/-!
# MetaMorphoV1_1 `skim(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2710; reach lemma `metaMorphoV1_1ReachSkimBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `skim(address)`: the theorem `Correct.lean` routes selector 57 to. -/
theorem metaMorphoV1_1SkimBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 57)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 57) rfl hsel
  have hd : dispatchMsg contract I.calldata = some skimTransition := by
    apply metaMorphoV1_1Dispatch_skim <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSkimBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (skimRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  by_cases hlen : 36 ≤ I.calldata.size
  case neg =>
    have hrev := skimRevertLength v (by simp) hwv (by
      rw [calldataNot3_eq_sub hsz hsize,
        solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
      decide) rd
    exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    have hrev := skimRevertLength v (by simp) hwv (by
      rw [calldataNot3_eq_sub hsz hsize,
        solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
      decide) rd
    exact hrev.reEquivDecodingFailed hcode hd
      (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
  obtain ⟨_, _, rd11163⟩ := skimReachDecoder v (by simp) hwv hlen hhi hsize rd
  by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  case neg =>
    exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
      hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
  have hdec := decodeCalldata_address_ok (x := "token") hlen hhi hcanon
  obtain ⟨_, _, rd2735⟩ := decodeAddressAt4 v (by simp) hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd11163
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let token := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  have hs : SourceState evm I σ evm := SourceState.init
  by_cases heq : skimRecipientAddress evm = ⟨0, by decide⟩
  case pos =>
    exact (skimRevertRecipient v (by simp) hs heq rd2735).reEquivExecutionRevert hcode hd hdec
      (skimBodyRevertsRecipient evm (immStore v) token hwv hhi heq)
  obtain ⟨_, _, _, rd2755⟩ := skimReachBalance v (by simp) hs heq rd2735
  have hw : UInt256.ofNat token.toNat = calldataWord I.calldata 4 := by
    change EVM.word (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).val = _
    rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean hcanon]
  rw [← hw] at rd2755
  rcases skimBodySimulation v (immStore v) token (by simp) hs
    (skimPrefix evm (immStore v) token hwv hhi heq) rd2755 with
    ⟨hsource, hrev⟩ | ⟨evm', frame', hsource, hret⟩ | ⟨hsource, hstatic⟩
  · exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · exact hret.reEquivExecutionGen hcode hd hdec hsource rfl voidReturnEquiv
  · exact hstatic.reEquivStaticHalt hcode hd hdec hsource

end Benchmarks.Morpho.MetaMorphoV1_1
