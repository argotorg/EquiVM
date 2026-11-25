import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.SettlementTrace
import Benchmarks.Midnight.SettlementCall

variable {fork : Ethereum.Fork}

/-!
# Midnight `settlementFee(bytes32,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3730; reach lemma `midnightReachSettlementFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem settlementFeeTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {aw : UInt256}
    {id time : UInt256}
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) ⟨21835⟩
      [id, time, ⟨3755⟩, ⟨32⟩, solcSelectorWord I] midnightEntryMemory aw
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (settlementFeeValue (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) time).toByteArray := by
  obtain ⟨aw1, k1, C1, rd1⟩ := settlementInternalTrace (by simp)
    (by rw [midnightEntryMemory_size]; decide) (by jump_dest) hspace rd
  have hr := midnightBlocks.midnight_block_3755 (by simp) rd1
  simp only [mappingMemory_fold, mappingMemory_freePtr] at hr
  exact (writeWord_sparse_read_back (mappingMemory id ⟨1⟩) 832 _) ▸ hr

/-- `settlementFee(bytes32,uint256)`: the theorem `Correct.lean` routes selector 35 to. -/
theorem midnightSettlementFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 35)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 35) rfl hsel
  have hd : dispatchMsg contract I.calldata = some settlementFeeTransition := by
    apply midnightDispatch_settlementFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSettlementFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_3730_fallthrough (by simp) hwv rd
    have rd2 := midnightBlocks.midnight_block_3736 (by simp) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_3736_stack] at rd2
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd3 := midnightBlocks.midnight_block_18819_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd2
        simp only [midnightBlocks.midnight_block_18819_fallthrough_stack] at rd3
        have rd4 := midnightBlocks.midnight_block_18832 (by simp) (by jump_dest) rd3
        simp only [midnightBlocks.midnight_block_18832_stack] at rd4
        have rd5 := midnightBlocks.midnight_block_3749 (by simp) (by jump_dest) rd4
        simp only [midnightBlocks.midnight_block_3749_stack] at rd5
        have hdec := midnightDecodePair_ok "id" "timeToMaturity"
          (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
          (decodeBytes32Word (off := 4) (by omega)) (decodeUint256Word (off := 36) h68)
        by_cases hspace : marketTickSpacing
            (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I) = ⟨0⟩
        · have hr := settlementInternalTraceRevert (by simp)
            (by change 64 ≤ midnightEntryMemory.size; rw [midnightEntryMemory_size]; decide) hspace rd5
          exact hr.reEquivExecutionRevert hcode hd hdec (settlementFeeBodyReverts
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hspace)
        · have hr := settlementFeeTraceReturn hspace rd5
          have hbody := settlementFeeBodyReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hspace
          exact hr.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode (uint256ReturnEncoding _))
      · have rd3 := midnightBlocks.midnight_block_18819_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd2
        have hr := midnightBlocks.midnight_block_6350 (by simp
          [midnightBlocks.midnight_block_18819_taken_stack]) rd3
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "id" "timeToMaturity" (.bytes abiBytes32Width)
            (.int (.uint ⟨256, by decide⟩)) hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd3 := midnightBlocks.midnight_block_18819_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd2
      have hr := midnightBlocks.midnight_block_6350 (by simp
        [midnightBlocks.midnight_block_18819_taken_stack]) rd3
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "id" "timeToMaturity" (.bytes abiBytes32Width)
          (.int (.uint ⟨256, by decide⟩)) (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_3730_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (settlementFeeTransition.params.map Param.name)
        (transitionSignature settlementFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
