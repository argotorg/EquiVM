import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.MarketEntryTrace
import Benchmarks.Midnight.PositionViewCall
import Benchmarks.Midnight.PositionViewTrace
import Benchmarks.Midnight.ReturnThree128

/-!
# Midnight `updatePositionView((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2568; reach lemma `midnightReachUpdatePositionViewBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `updatePositionView((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address)`: the theorem `Correct.lean` routes selector 46 to. -/
theorem midnightUpdatePositionViewBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 46)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 46) rfl hsel
  have hd : dispatchMsg contract I.calldata = some updatePositionViewTransition := by
    apply midnightDispatch_updatePositionView <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachUpdatePositionViewBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_2568_fallthrough (by simp) hwv rd
    have rd2 := midnightBlocks.midnight_block_2574 (by simp) (by jump_dest) rd1
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightMarketIdUserDecoder (by simp)
        hsz hsize hselector midnightEntryMemory_freePtr (by jump_dest) rd2 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h100, hhi, hu, mem', root, aw3, k3, C3, hroot, hstored, hfree, rd3⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · have rd4 := midnightBlocks.midnight_block_2588 (by simp) (by jump_dest) rd3
      have hm : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 128) mem' = m.maturity :=
        hstored.words.load_offset ⟨4, by change 4 < 8; decide⟩ rfl
      have hmem : 1088 ≤ mem'.size := hstored.words.size
      let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let id := calldataWord I.calldata 36
      let user := calldataWord I.calldata 68
      let pc := positionPostCredit evm id user
      let pp := positionPostPending evm id user
      let fee := positionViewFee evm m id user
      have hrun := midnightPositionViewInternal (by simp)
        hu (by decide) (by change 960 + 32 ≤ mem'.size; omega) hm (by jump_dest) rd4
      change (¬ PositionViewSourceSafe evm m id user ∧ RDrev midnightBytecode _ _) ∨
        (PositionViewSourceSafe evm m id user ∧ ∃ aw' k' C',
          RD midnightBytecode I _ _ ⟨2594⟩
            (fee :: UInt256.sub (low128 pp) fee :: UInt256.sub (low128 pc) fee ::
              ⟨1184⟩ :: [solcSelectorWord I])
            (positionSlashMemory mem' id user (positionFieldWord evm id user 2))
            aw' ByteArray.empty σ k' C') at hrun
      rcases hrun with ⟨hbad, hr⟩ | ⟨hsafe, aw5, k5, C5, rd5⟩
      · exact hr.reEquivExecutionRevert hcode hd hdec
          (positionViewBodyReverts evm m id user hu hwv (by change I.calldata.size < 2^255 + 4; omega) hbad)
      · have hfee : fee.toNat < 2 ^ 128 := positionAccruedFee_lt _ _ _ _
        have hcredit : (UInt256.sub (low128 pc) fee).toNat < 2 ^ 128 := by
          rw [usub_toNat (show fee.toNat ≤ (low128 pc).toNat from hsafe.2.2.1)]
          have h := low128_lt pc
          omega
        have hpending : (UInt256.sub (low128 pp) fee).toNat < 2 ^ 128 := by
          rw [usub_toNat (show fee.toNat ≤ (low128 pp).toNat from hsafe.2.2.2)]
          have h := low128_lt pp
          omega
        have hf : memLoad (UInt256.ofNat 64)
            (positionSlashMemory mem' id user (positionFieldWord evm id user 2)) = root := by
          rw [positionSlashMemory_load _ _ _ _ _ (by decide)
            (by change 96 ≤ mem'.size; omega), hfree]
        have hr := midnightReturnThree128 (by simp) hstored.bound hf hcredit hpending hfee rd5
        exact hr.reEquivExecution hcode hd hdec
          (positionViewBodyReturns evm m id user hu hwv (by change I.calldata.size < 2^255 + 4; omega) hsafe)
          (returnEquiv.returned rfl (threeUint128ReturnEncoding _ _ _ hcredit hpending hfee))
  · have rd1 := midnightBlocks.midnight_block_2568_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (updatePositionViewTransition.params.map Param.name)
        (transitionSignature updatePositionViewTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
