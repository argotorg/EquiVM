import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.TouchMarketEntryAccounting
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.TouchMarketSource
import Benchmarks.Midnight.RuntimeBlocks_017

variable {fork : Ethereum.Fork}

/-!
# Midnight `touchMarket((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4303; reach lemma `midnightReachTouchMarketBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `touchMarket((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address))`: the theorem `Correct.lean` routes selector 33 to. -/
theorem midnightTouchMarketBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 33)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 33) rfl hsel
  have hd : dispatchMsg contract I.calldata = some touchMarketTransition := by
    apply midnightDispatch_touchMarket <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachTouchMarketBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨4303⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_4303_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightTouchMarketEntry_accounted (by simp) hsz hsize hselector
        midnightEntryMemory_freePtr ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h36, hhi, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hmem, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      rcases midnightTouchMarketInternal_bounded (evm := evm) (g := Sat256.ofUInt256 g)
          (imms := ∅) m
          (by simp) hm hmem hgas ha2 hfree rfl (by jump_dest) rd2 with
        hoog | ⟨hr, hs⟩ | ⟨hr, hs⟩ |
          ⟨frame', evm', σ', out, mem'', free, aw3, k3, C3, hs, hbody,
            _, _, _, _, hfree', rd3⟩
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · exact hr.reEquivExecutionRevert hcode hd hdec
          (touchMarketBodyReverts hwv (by change I.calldata.size < 2^255 + 4; omega) hs)
      · exact hr.reEquivStaticHalt hcode hd hdec
          (touchMarketBodyStatic hwv (by change I.calldata.size < 2^255 + 4; omega) hs)
      · have hr := midnightBlocks.midnight_block_3755 (by simp) rd3
        rw [hfree'] at hr
        change RDret fork midnightBytecode (Sat256.ofUInt256 g) evm σ'
          ((writeWord mem'' free.toNat m.id).readWithPadding free.toNat 32) at hr
        rw [writeWord_sparse_read_back] at hr
        exact hr.reEquivExecutionGen hcode hd hdec
          (touchMarketBodyReturns hwv (by change I.calldata.size < 2^255 + 4; omega) hbody)
          hs.accounts (returnEquiv_of_encode (bytes32ReturnEncoding m.id))
  · have rd1 := midnightBlocks.midnight_block_4303_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (touchMarketTransition.params.map Param.name)
        (transitionSignature touchMarketTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
