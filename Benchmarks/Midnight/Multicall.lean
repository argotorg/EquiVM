import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.MulticallEntry
import Benchmarks.Midnight.MulticallInvalidLoop
import Benchmarks.Midnight.MulticallLoop
import Benchmarks.Midnight.MarketEntryDecode

variable {fork : Ethereum.Fork}

/-!
# Midnight `multicall(bytes[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3542; reach lemma `midnightReachMulticallBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `multicall(bytes[])`: the theorem `Correct.lean` routes selector 36 to. -/
theorem midnightMulticallBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 36)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 36) rfl hsel
  have hd : dispatchMsg contract I.calldata = some multicallTransition := by
    apply midnightDispatch_multicall <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachMulticallBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨3542⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_3542_fallthrough (by simp) hwv rd
    have hselector : (bytesToWord (I.calldata.toList.take 4)).toNat = 0xac9650d8 := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightMulticallEntry (by simp) hsz hsize hselector rd1 with
      ⟨hdec, hr⟩ | ⟨hv, hdecode, k2, C2, hc2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let base := calldataArgumentPointer I.calldata 4
    let count := calldataArgumentLength I.calldata 4
    have hn : count.toNat < 2^64 := hv.bounds.1
    have hspan : base.toNat + 32 * count.toNat ≤ I.calldata.size := hv.bounds.2
    have hhi : I.calldata.size < 2^255 := hv.2.1
    have hlimit : I.calldata.size < calldataLimit := by
      change I.calldata.size < 2^255 + 4
      omega
    have hm : 832 ≤ midnightEntryMemory.size := by rw [midnightEntryMemory_size]
    have hz : memLoad (UInt256.ofNat 800) midnightEntryMemory = ⟨0⟩ := by native_decide
    have rd3 := midnightBlocks.midnight_block_3590 (by simp) rd2
    have ha2 := memoryAccountingAt rd2 ⟨ha.paid.mono (by omega), ha.covered⟩
    have ha3 := memoryAccountingAt rd3 (by memory_account ha2)
    simp only [midnightBlocks.midnight_block_3590_stack, hz, wordAddLnot30] at rd3
    change RD fork midnightBytecode I (Sat256.ofUInt256 g) origin ⟨3605⟩
      (⟨0⟩ :: base :: multicallTailBound I.calldata base :: count :: [solcSelectorWord I])
      midnightEntryMemory _ ByteArray.empty σ _ _ at rd3
    have hh : TransferHeap midnightEntryMemory
        (M (UInt256.ofNat 26) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 832)
        (C2 + (33 + memExpansionCost (UInt256.ofNat 26) (UInt256.ofNat 800) ⟨32⟩)) := by
      refine ⟨by omega, by decide, midnightEntryMemory_freePtr, ?_, by decide, by decide, ?_⟩
      · native_decide
      · exact MemoryFunding.of_accounting ha3
    by_cases hvalid : MulticallTailsValid I.calldata base 0 count.toNat
    · let calls := multicallBytesList I.calldata base 0 count.toNat
      let frame := calldataFrame contract (multicallArguments calls) ∅ origin
      have hdec : config.externalABI.decodeCalldata? (multicallTransition.params.map Param.name)
          (transitionSignature multicallTransition).paramTypes I.calldata =
          some (multicallArguments calls) := by
        change config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] I.calldata = _
        rw [hdecode]
        change MulticallTailsValid I.calldata (calldataArgumentPointer I.calldata 4) 0
          (calldataArgumentLength I.calldata 4).toNat at hvalid
        simp only [decodeMulticallArguments, if_pos hv, decodeMulticallTails, if_pos hvalid,
          Option.map_some]
        rfl
      have hf : (flashLoanSetIndex frame 0).locals.get? "calls" =
          some (.array (calls.map Value.bytes)) := by
        change (((multicallArguments calls).insert "__calldata" (.bytes I.calldata)).insert
          "i" (.int 0)).get? "calls" = _
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
        exact store_get_self _ _ _
      have sourcePrefix {result : ExecResult}
          (hbody : ExecBlock fork config frame origin (multicallTransition.body.drop 3) result) :
          ExecBlock fork config
            { contract := contract, locals := multicallArguments calls, immutables := ∅ }
            origin multicallTransition.body result :=
        guardedBodyBlock hwv hlimit hbody
      rcases midnightMulticallLoop count.toNat (index := ⟨0⟩) (by simp)
          (by change count.toNat = 0 + count.toNat; omega) hn hhi hspan hvalid hf
          (flashLoanSetIndex_get frame 0) hm (by decide) hz hh hgas hfork
          (by exact ⟨rfl, rfl, rfl⟩) rd3 with
        hoog | ⟨hloop, hr⟩ | ⟨frame', evm', σ', hloop, hs', hr⟩
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply sourcePrefix
        rw [multicallLoop_shape]
        exact .consRevert (multicallLoopStatement hloop)
      · rw [hs'.accounts] at hr
        have hb : ExecBlock fork config frame origin (multicallTransition.body.drop 3)
            (.ok frame' evm') := by
          rw [multicallLoop_shape]
          exact .consNormal (multicallLoopStatement hloop) .nil
        exact hr.reEquivExecutionGen hcode hd hdec
          (.execBlockOK (sourcePrefix hb)) rfl voidReturnEquiv
    · have hdec : config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes]
          I.calldata = none := by
        rw [hdecode]
        change ¬ MulticallTailsValid I.calldata (calldataArgumentPointer I.calldata 4) 0
          (calldataArgumentLength I.calldata 4).toNat at hvalid
        simp only [decodeMulticallArguments, if_pos hv, decodeMulticallTails,
          if_neg hvalid, Option.map_none]
      rcases midnightMulticallInvalidLoop count.toNat (index := ⟨0⟩) (by simp)
          (by change count.toNat = 0 + count.toNat; omega) hn hhi hspan hvalid
          hm (by decide) hz hh hgas hfork (by exact ⟨rfl, rfl, rfl⟩) rd3 with hoog | hr
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · exact hr.reEquivDecodingFailed hcode hd hdec
  · have rd1 := midnightBlocks.midnight_block_3542_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (multicallTransition.params.map Param.name)
        (transitionSignature multicallTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
