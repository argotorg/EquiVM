import Benchmarks.Midnight.OfferDecoder
import Benchmarks.Midnight.TakeInputMemory
import Benchmarks.Midnight.Entry
import Benchmarks.Midnight.ScalarDecode

variable {fork : Ethereum.Fork}

/-! The complete take ABI decoder and its materialized input heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeEntryMemory (mem bytes : ByteArray) : ByteArray :=
  takeScalarsMemory (offerPrepareMemory mem) bytes

theorem midnightTakeEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hmem : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10413⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? takeNames takeTypes I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ offer ratifierData data,
      config.externalABI.decodeCalldata? takeNames takeTypes I.calldata =
        some (takeArguments offer ratifierData (calldataWord I.calldata 68)
          (AccountAddress.ofNat (calldataWord I.calldata 100).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 132).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 164).toNat) data) ∧
      decodeCalldataOffer I.calldata 4 = some offer ∧
      decodeCalldataBytes I.calldata 36 = some ratifierData ∧
      decodeCalldataBytes I.calldata 196 = some data ∧ TakeScalarsValid I.calldata ∧
      228 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧
      ∃ mem' callbackPtr ratifierPtr takerPtr root aw' k' C',
        callbackPtr.toNat = 1600 + 160 * offer.market.collaterals.length ∧
        ratifierPtr.toNat = 1632 + 160 * offer.market.collaterals.length +
          paddedSize offer.callbackData.size ∧
        takerPtr.toNat = 1664 + 160 * offer.market.collaterals.length +
          paddedSize offer.callbackData.size + paddedSize ratifierData.size ∧
        root.toNat = takeInputSize offer ratifierData data ∧
        TakeInputStored mem' callbackPtr ratifierPtr takerPtr root offer ratifierData data ∧
        memLoad (UInt256.ofNat 64) mem' = root ∧ root.toNat ≤ mem'.size ∧
        MemoryWords mem' 96 (memoryWordSnapshot (takeEntryMemory mem I.calldata) 96 23) ∧
        MemoryFunding (3 * ((offer.callbackData.size + 31) / 32) +
          3 * ((ratifierData.size + 31) / 32) + 3 * ((data.size + 31) / 32)) mem' aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10925⟩ (takerPtr :: ratifierPtr :: R)
          mem' aw' rdata σ k' C') := by
  have reject (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
      ⟨224⟩ = ⟨1⟩) :
      config.externalABI.decodeCalldata? takeNames takeTypes I.calldata = none ∧
        RDrev fork midnightBytecode g s0 := by
    refine ⟨midnightDecodeTake_none_check h4 (solcSLT_sub4_of_check (bit := true) hc), ?_⟩
    have rr := midnightBlocks.midnight_block_10413_taken (by omega)
      (by change UInt256.slt (UInt256.lnot ⟨3⟩ + _) ⟨224⟩ ≠ ⟨0⟩
          rw [hc]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_6350 (by omega) rr
  by_cases hshort : I.calldata.size < 228
  · exact Or.inl (reject (entrySizeCheck_short h4 hshort (by decide) hsize))
  by_cases hhuge : 2^255 + 4 ≤ I.calldata.size
  · exact Or.inl (reject (entrySizeCheck_huge hhuge hsize (by decide)))
  have h228 : 228 ≤ I.calldata.size := by omega
  have hcheck : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨224⟩ = ⟨0⟩ :=
    entrySizeCheck_ok h228 (by omega) hsize
  have hdecode := midnightDecodeTake h228 hsize hselector
    (solcSLT_sub4_of_check (bit := false) hcheck)
  have rd1 := midnightBlocks.midnight_block_10413_fallthrough (by omega) hcheck rd
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  rcases midnightOfferDecoder hstack hsize hmem hfree ha1 rd1 with
    ⟨hbad, hr⟩ | ⟨offer, hoffer, hsmall, hroff, mem2, callbackPtr, ratifierPtr,
      aw2, k2, C2, hcallbackPtr, hratifierPtr, hstored, hf2, hm2, hk2, ha2, rd2⟩
  · refine Or.inl ⟨hdecode.trans ?_, hr⟩
    apply decodeTakeArguments_none_of_invalid
    intro offer ratifierData data ho hr _ _ hfit
    rcases hbad offer ho with hb | hb
    · unfold takeInputSize at hfit
      omega
    · rw [hb] at hr
      cases hr
  · rcases midnightTakeTailDecoder (by omega) hsize hoffer hroff hratifierPtr hstored.bound
        hf2 ha2 rd2 with
      ⟨hnone, hr⟩ | ⟨ratifierData, data, hrat, hv, hdata, hratFit, hdataFit, hfit,
        aw3, k3, C3, ha3, rd3⟩
    · exact Or.inl ⟨hdecode.trans hnone, hr⟩
    · let takerPtr := returnDataPtr ratifierPtr ratifierData.size
      let root := returnDataPtr takerPtr data.size
      have ht : takerPtr.toNat = 1664 + 160 * offer.market.collaterals.length +
          paddedSize offer.callbackData.size + paddedSize ratifierData.size := by
        rw [returnDataPtr_toNat hratFit, hratifierPtr, returnDataAllocation_eq]
        omega
      have hr : root.toNat = takeInputSize offer ratifierData data := by
        rw [returnDataPtr_toNat hdataFit]
        change takerPtr.toNat + returnDataAllocation data.size = _
        rw [ht, returnDataAllocation_eq]
        unfold takeInputSize
        omega
      exact Or.inr ⟨offer, ratifierData, data,
        hdecode.trans (decodeTakeArguments_some hoffer hrat hv hdata hfit),
        hoffer, hrat, hdata, hv, h228, hsmall, _, callbackPtr, ratifierPtr, takerPtr, root,
        aw3, k3, C3, hcallbackPtr, hratifierPtr, ht, hr,
        takeTailMemory_stored hstored hrat hdata hratFit hdataFit,
        takeTailMemory_free (by omega) hdata hratFit, takeTailMemory_size hdata hdataFit,
        takeTailMemory_low hk2 (by rw [offerPrepareMemory_size hmem]; exact hmem)
          (by omega) hrat hdata hratFit, ha3, rd3⟩

end Benchmarks.Midnight
