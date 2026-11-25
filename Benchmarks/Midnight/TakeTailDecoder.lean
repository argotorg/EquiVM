import Benchmarks.Midnight.TakeScalarsMemory
import Benchmarks.Midnight.BytesArgumentDecoder
import Benchmarks.Midnight.TakeDecodeFacts

variable {fork : Ethereum.Fork}

/-! The ratifier data, scalar arguments, and taker callback data following the decoded offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeTailMemory (mem bytes : ByteArray) (ratifierPtr takerPtr : UInt256) : ByteArray :=
  bytesCalldataMemory
    (takeScalarsMemory
      (bytesCalldataMemory mem bytes ratifierPtr (4 + (calldataWord bytes 36).toNat)) bytes)
    bytes takerPtr (4 + (calldataWord bytes 196).toNat)

theorem midnightTakeTailDecoder {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ratifierPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {offer : OfferData} (hstack : R.length + 16 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size)
    (hoffer : decodeCalldataOffer I.calldata 4 = some offer)
    (hoff : (calldataWord I.calldata 36).toNat < 2^64)
    (hptr : ratifierPtr.toNat = 1632 + 160 * offer.market.collaterals.length +
      paddedSize offer.callbackData.size) (hcap : ratifierPtr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ratifierPtr)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10833⟩ (calldataWord I.calldata 36 :: R)
      mem aw rdata σ k C) :
    (decodeTakeArguments I.calldata = none ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ ratifierData data,
      decodeCalldataBytes I.calldata 36 = some ratifierData ∧ TakeScalarsValid I.calldata ∧
      decodeCalldataBytes I.calldata 196 = some data ∧
      ratifierPtr.toNat + returnDataAllocation ratifierData.size < 2^64 ∧
      (returnDataPtr ratifierPtr ratifierData.size).toNat + returnDataAllocation data.size <
        2^64 ∧ takeInputSize offer ratifierData data < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 3 * ((ratifierData.size + 31) / 32) +
          3 * ((data.size + 31) / 32))
          (takeTailMemory mem I.calldata ratifierPtr (returnDataPtr ratifierPtr ratifierData.size))
          aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10925⟩
          (returnDataPtr ratifierPtr ratifierData.size :: ratifierPtr :: R)
          (takeTailMemory mem I.calldata ratifierPtr (returnDataPtr ratifierPtr ratifierData.size))
          aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_10833 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  rcases midnightBytesArgumentDecoder (by omega) hoff hcap hsize hfree (by jump_dest)
      ha1 rd1 with
    ⟨hbad, hr⟩ | ⟨ratifierData, hrat, hratFit, aw2, k2, C2, ha2, rd2⟩
  · refine Or.inl ⟨?_, hr⟩
    apply decodeTakeArguments_none_of_invalid
    intro o r d ho hr _ _ hfit
    have he : o = offer := Option.some.inj (ho.symm.trans hoffer)
    subst o
    have hb := hbad r hr
    rw [returnDataAllocation_eq, hptr] at hb
    unfold takeInputSize at hfit
    omega
  · rcases midnightTakeScalars (by simp only [List.length_cons]; omega) ha2 rd2 with
      ⟨hbad, hr⟩ | ⟨hv, htOff, aw3, k3, C3, ha3, rd3⟩
    · refine Or.inl ⟨?_, hr⟩
      exact hbad.elim decodeTakeArguments_none_scalars decodeTakeArguments_none_data
    · let m2 := bytesCalldataMemory mem I.calldata ratifierPtr
        (4 + (calldataWord I.calldata 36).toNat)
      let takerPtr := returnDataPtr ratifierPtr ratifierData.size
      have hdRat : decodeBytesAt I.calldata (4 + (calldataWord I.calldata 36).toNat) =
          some ratifierData := by rwa [decodeCalldataBytes_eq_at hoff] at hrat
      have ht : takerPtr.toNat = ratifierPtr.toNat + returnDataAllocation ratifierData.size :=
        returnDataPtr_toNat hratFit
      have hm2 : ratifierPtr.toNat + returnDataAllocation ratifierData.size ≤ m2.size :=
        bytesCalldataMemory_size hdRat
      have hf3 : memLoad (UInt256.ofNat 64) (takeScalarsMemory m2 I.calldata) = takerPtr := by
        rw [takeScalarsMemory_free (by omega)]
        exact bytesCalldataMemory_free hdRat (by omega)
      have rd4 := midnightBlocks.midnight_block_10911
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      have ha4 := memoryFundingAt (credit := credit + 3 * ((ratifierData.size + 31) / 32))
        rd4 (by memory_fund ha3)
      rcases midnightBytesArgumentDecoder (by simp only [List.length_cons]; omega)
          htOff (by rw [ht]; exact hratFit) hsize hf3 (by jump_dest) ha4 rd4 with
        ⟨hbad, hr⟩ | ⟨data, hdata, hdataFit, aw5, k5, C5, ha5, rd5⟩
      · refine Or.inl ⟨?_, hr⟩
        apply decodeTakeArguments_none_of_invalid
        intro o r d ho hr _ hd hfit
        have heo : o = offer := Option.some.inj (ho.symm.trans hoffer)
        have her : r = ratifierData := Option.some.inj (hr.symm.trans hrat)
        subst o r
        have hb := hbad d hd
        rw [ht, hptr, returnDataAllocation_eq, returnDataAllocation_eq] at hb
        unfold takeInputSize at hfit
        omega
      · have hfit : takeInputSize offer ratifierData data < 2^64 := by
          rw [ht, hptr, returnDataAllocation_eq, returnDataAllocation_eq] at hdataFit
          unfold takeInputSize
          omega
        exact Or.inr ⟨ratifierData, data, hrat, hv, hdata, hratFit, hdataFit, hfit,
          aw5, k5, C5, ha5, rd5⟩

end Benchmarks.Midnight
