import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.HealthInternal
import Benchmarks.Midnight.IsHealthySource
import Benchmarks.Midnight.MarketAccountEntry

variable {fork : Ethereum.Fork}

/-!
# Midnight `isHealthy((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15446; reach lemma `midnightReachIsHealthyBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `isHealthy((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bytes32,address)`: the theorem `Correct.lean` routes selector 15 to. -/
theorem midnightIsHealthyBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 15)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 15) rfl hsel
  have hd : dispatchMsg contract I.calldata = some isHealthyTransition := by
    apply midnightDispatch_isHealthy <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachIsHealthyBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨15446⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15446_fallthrough (by simp) hwv rd
    have rd2 := midnightBlocks.midnight_block_15452 (by simp) (by jump_dest) rd1
    have ha2 := memoryAccountingAt rd2 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightMarketIdAccountDecoder_accounted "borrower" (by decide) (by decide)
        (by simp only [List.length_cons, List.length_nil]; omega) hsz hsize hselector
        midnightEntryMemory_freePtr ha2 (by jump_dest) rd2 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h100, hhi, hu, mem', root, aw3, k3, C3,
        hroot, hm, hfree, hmem, ha3, rd3⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · rcases memoryAccounting_headroom rd3 ha3 hgas with hoog | hcapacity
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · have hlimit : I.calldata.size < calldataLimit := by
          change I.calldata.size < 2^255 + 4
          omega
        have rd4 := midnightBlocks.midnight_block_15465
          (by simp only [List.length_cons, List.length_nil]; omega) (by jump_dest) rd3
        rcases midnightHealthInternal (imms := ∅) (g := Sat256.ofUInt256 g)
            (by simp only [List.length_cons, List.length_nil]; omega) hfork hu (by omega)
            (by omega) hfree hm SourceState.init (by jump_dest) rd4 with
          ⟨hbody, hrev⟩ | ⟨evm', σ', frame', mem'', out, root', aw4, k4, C4, value,
            hbody, hs, hm', hfree', hheap', hroot', rd5⟩
        · exact hrev.reEquivExecutionRevert hcode hd hdec
            (isHealthyBodyReverts hwv hlimit hbody)
        · have hr := midnightBlocks.midnight_block_15471 (by simp) rd5
          change RDret fork midnightBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ'
            ((writeWord mem'' (memLoad (UInt256.ofNat 64) mem'').toNat
              (UInt256.isZero (UInt256.isZero (if value then ⟨1⟩ else ⟨0⟩)))).readWithPadding
              (memLoad (UInt256.ofNat 64) mem'').toNat 32) at hr
          rw [writeWord_sparse_read_back] at hr
          have hsource := isHealthyBodyReturns hwv hlimit hbody
          cases value with
          | false =>
            exact hr.reEquivExecutionGen hcode hd hdec hsource hs.accounts
              (returnEquiv_of_encode boolFalseReturnEncoding)
          | true =>
            exact hr.reEquivExecutionGen hcode hd hdec hsource hs.accounts
              (returnEquiv_of_encode boolTrueReturnEncoding)
  · have rd1 := midnightBlocks.midnight_block_15446_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (isHealthyTransition.params.map Param.name)
        (transitionSignature isHealthyTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
