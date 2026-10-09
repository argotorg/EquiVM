import Benchmarks.Morpho.MorphoBlue.ExtSloadsFinish

/-!
# Morpho `extSloads(bytes32[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 6760; reach lemma `morphoReachExtSloadsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

/-- `extSloads(bytes32[])`: the theorem `Correct.lean` routes selector 14 to. -/
theorem morphoExtSloadsBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 14) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some extSloadsTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k, C, rd⟩ := morphoReachExtSloadsBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd0 := morphoBlocks.morpho_block_6760_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd0
    cases hdec : decodeCalldata ["slots"] [.dynamicArray abiBytes32] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd0 := morphoBlocks.morpho_block_6760_fallthrough (immWords := wordsOf (immStore v))
    (by decide) hcv rd
  rcases morphoExtSloadsDecode (v := v) hsz hsize rd0 with ⟨hbad, hr⟩ | ⟨hb, aw1, k1, C1, rd1⟩
  · exact reEquivSelectorDecodingFailed hcode hr hd (decodeCalldata_wordArray_none "slots" hbad)
  · obtain ⟨slots, hslots, hdec⟩ := decodeCalldata_wordArray_exists "slots" hb
    have hn : slots.length ≤ solcMaxU64 := by rw [hslots.length]; exact hb.2.2.2.2.1
    have he : calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) =
        UInt256.ofNat slots.length := by rw [hslots.length, u256_ofNat_toNat]
    rw [he] at rd1
    rcases morphoExtSloadsPrepare (v := v) hn hsize rd1 with ⟨ha, hr⟩ | ⟨ha, aw2, k2, C2, rd2⟩
    · exact reEquivSelectorRevert hcode hr hd hdec
        (morphoExtSloadsSourceAllocationRevert slots _ (immStore v) hslots hcv ha)
    · have hr := morphoExtSloadsFinish (v := v) hb.2.2.1 hn rd2
      obtain ⟨frame, hbody⟩ := morphoExtSloadsSource slots (initState σ σ₀ (.ofUInt256 g) A I)
        (immStore v) hslots hcv ha
      apply reEquivSelectorExecution (cfg := config) hcode hr hd hdec hbody
      exact .returned rfl (wordArrayReturn_encoding (extSloadsWords σ I) slots.length)

end Benchmarks.Morpho.MorphoBlue
