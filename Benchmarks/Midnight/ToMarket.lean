import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.ToMarketStoredDecode

/-!
# Midnight `toMarket(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 719; reach lemma `midnightReachToMarketBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `toMarket(bytes32)`: the theorem `Correct.lean` routes selector 55 to. -/
theorem midnightToMarketBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 55)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 55) rfl hsel
  have hd : dispatchMsg contract I.calldata = some toMarketTransition := by
    apply midnightDispatch_toMarket <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachToMarketBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_719_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_725_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hdec := midnightDecodeBytes32 "id" (by decide) (by decide) h36 hhi hsize
        obtain ⟨aw3, k3, C3, rd3⟩ := midnightToMarketGetTick (by simp) rd2
        let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let id := calldataWord I.calldata 4
        let tick := marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)
        have ht : marketTickSpacing (marketFeeWord evm id) = tick := rfl
        by_cases hinit : 0 < tick.toNat
        · have hnz : tick ≠ UInt256.ofNat 0 := by
            intro he
            rw [he] at hinit
            change 0 < 0 at hinit
            omega
          have hzero : UInt256.isZero tick = UInt256.ofNat 0 := isZero_eq_zero_of_ne hnz
          have rd4 := midnightBlocks.midnight_block_846_fallthrough (by simp) hzero rd3
          simp only [midnightBlocks.midnight_block_846_fallthrough_stack] at rd4
          by_cases hcodesize : (extCodeSizeWord σ id).toNat ≤ 18446744073709550464
          · obtain ⟨aw5, k5, C5, rd5⟩ := midnightToMarketCodeCopy (by simp) hcodesize rd4
            rcases midnightToMarketStoredDecode (by simp) hcodesize rd5 with
              ⟨hbad, hr⟩ | ⟨m, hm, hfit, hr⟩
            · exact hr.reEquivExecutionRevert hcode hd hdec
                (toMarketDataReverts evm id hwv hhi (ht ▸ hinit) hcodesize hbad)
            · exact hr.reEquivExecution hcode hd hdec
                (toMarketDataReturns evm id m hwv hhi (ht ▸ hinit) hcodesize hm hfit)
                (returnEquiv_of_encode m.encodeReturn)
          · have hr := midnightToMarketCodeTooLarge (by simp) hcodesize rd4
            exact hr.reEquivExecutionRevert hcode hd hdec
              (toMarketCodeTooLarge evm id hwv hhi (ht ▸ hinit) hcodesize)
        · have hz : tick = UInt256.ofNat 0 := u256_inj (by change tick.toNat = 0; omega)
          have rd4 := midnightBlocks.midnight_block_846_taken (by simp)
            (by change UInt256.isZero tick ≠ UInt256.ofNat 0; rw [hz]; decide) (by jump_dest) rd3
          have hr := midnightBlocks.midnight_block_1275 (by simp
            [midnightBlocks.midnight_block_846_taken_stack]) rd4
          exact hr.reEquivExecutionRevert hcode hd hdec
            (toMarketUninitialized evm id hwv hhi (ht ▸ hinit))
      · have rd2 := midnightBlocks.midnight_block_725_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "id" (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_725_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "id" (.bytes abiBytes32Width) (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_719_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (toMarketTransition.params.map Param.name)
        (transitionSignature toMarketTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
