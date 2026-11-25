import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ClaimFeeEntryPreserved
import Benchmarks.Midnight.ClaimFeeCore
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.TouchMarketLargeFunding

variable {fork : Ethereum.Fork}

/-!
# Midnight `claimContinuousFee((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15481; reach lemma `midnightReachClaimContinuousFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `claimContinuousFee((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address)`: the theorem `Correct.lean` routes selector 14 to. -/
theorem midnightClaimContinuousFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 14)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 14) rfl hsel
  have hd : dispatchMsg contract I.calldata = some claimContinuousFeeTransition := by
    apply midnightDispatch_claimContinuousFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachClaimContinuousFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨15481⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  have hk : MemoryWords midnightEntryMemory 96 [⟨0⟩] := by
    refine ⟨by decide, by rw [midnightEntryMemory_size]; decide, ?_⟩
    intro i
    fin_cases i
    native_decide
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15481_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightClaimFeeEntry_preserved (by simp) hsz hsize hselector
        midnightEntryMemory_freePtr hk (by decide) (by decide) ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h100, hhi, hu, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hmem, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hzero : memLoad ⟨96⟩ mem' = ⟨0⟩ := hk2.load ⟨0, by decide⟩
      have h128 : 128 ≤ mem'.size := by omega
      have rejectTouch (hr : RDrev fork midnightBytecode (Sat256.ofUInt256 g) evm)
          (hs : ExecFuncBody fork config (touchMarketCallFrame ∅ m) evm touchMarketFunction.body .reverted) :
          runtimeRefinementFor fork config contract σ σ₀ g A I := by
        apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        exact ExecBlock.consRevert (internalCallFunctionRevert
          (evalClaimFeeTouchArgs evm m _ _) rfl rfl hs)
      by_cases hsmall : m.collaterals.length ≤ 128
      · rcases midnightTouchMarketInternal_bounded (evm := evm) (g := Sat256.ofUInt256 g)
            (imms := ∅) m (by simp) hm hmem hgas ha2 hfree rfl (by jump_dest) rd2 with
          hoog | ⟨hr, hs⟩ | ⟨hr, hs⟩ |
            ⟨frame', evm', σ', out, mem'', free, aw3, k3, C3, hs, htouch,
              hp, hfreeLo, hfreeHi, hfreeBound, hfree', rd3⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact rejectTouch hr hs
        · apply hr.reEquivStaticHalt hcode hd hdec
          apply ExecFuncBody.execBlockStatic
          apply guardedBodyBlock hwv hlimit
          apply ExecBlock.consStatic
          exact ExecStmt.internalCallStatic (evalClaimFeeTouchArgs evm m _ _) rfl rfl hs
        · have hm' := hm.preserve hp
          have hmSize : 1088 ≤ mem''.size := hm'.words.size
          have hz : memLoad ⟨96⟩ mem'' = ⟨0⟩ := by
            rw [hp.load ⟨96⟩ (by decide) (by change 128 ≤ root.toNat; omega) h128, hzero]
          have hmax : free.toNat ≤ 90000 := by
            dsimp only [MarketData.encodingSize] at hfreeBound
            omega
          rw [hs.accounts] at rd3
          exact claimFeeBodyCore (credit := 0) hcode hwv hlimit hgas hfork hd hdec hs.env hs.world
            htouch (by simp) hu (by omega) (by omega) hfree' hz hm'.loanToken
            (Or.inl (by omega)) (by change 4 * ((free.toNat + 128 + 31) / 32) ≤ 999921; omega) rd3
      · rcases midnightTouchMarketLarge_funded (evm := evm) (g := Sat256.ofUInt256 g)
            (imms := ∅) m (by simp) hm (by omega) hmem hgas ha2 hfree (by jump_dest) rd2 with
          hoog | ⟨hr, hs⟩ | ⟨hb, htouch, aw3, k3, C3, hfund, rd3⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact rejectTouch hr hs
        · have hp := touchMarketHashMemory_prefix mem' m (by omega) hb
          have hm' := hm.preserve hp
          have hmSize : 1088 ≤ (touchMarketHashMemory mem' root m).size := hm'.words.size
          let free := touchMarketHashFree root m
          have hfn : free.toNat = root.toNat + 2 * m.encodingSize + 288 := by
            rw [show free = marketIdPreimagePtr root m + UInt256.ofNat 128 from rfl,
              uadd_word_ofNat_toNat _ _ (by rw [(marketIdPointers m hb).2.2]; change _ < 2^256; omega),
              (marketIdPointers m hb).2.2]
          have hn : free.toNat = 2048 + 416 * m.collaterals.length := by
            rw [hfn, hroot, MarketData.encodingSize]; omega
          have hz : memLoad ⟨96⟩ (touchMarketHashMemory mem' root m) = ⟨0⟩ := by
            rw [hp.load ⟨96⟩ (by decide) (by change 128 ≤ root.toNat; omega) h128, hzero]
          exact claimFeeBodyCore (credit := 128 * m.collaterals.length) hcode hwv hlimit hgas hfork
            hd hdec rfl rfl htouch (by simp) hu (by omega) (by rw [hn]; omega)
            (touchMarketHashMemory_free mem' root m) hz hm'.loanToken
            (Or.inr ⟨by rw [hn]; omega, hfund⟩)
            (by change 4 * ((free.toNat + 128 + 31) / 32) ≤ _; rw [hn]; omega) rd3
  · have rd1 := midnightBlocks.midnight_block_15481_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (claimContinuousFeeTransition.params.map Param.name)
        (transitionSignature claimContinuousFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
