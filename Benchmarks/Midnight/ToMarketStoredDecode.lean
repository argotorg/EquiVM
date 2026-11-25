import Benchmarks.Midnight.ToMarketDecodeHeader
import Benchmarks.Midnight.ToMarketDecoder
import Benchmarks.Midnight.ToMarketDataSource

variable {fork : Ethereum.Fork}

/-! Stored-market execution using the source decoder and its exact allocation bound. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketStoredDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 25 ≤ 1024)
    (hsmall : (extCodeSizeWord σ id).toNat ≤ 18446744073709550464)
    (rd : RD fork midnightBytecode I g s0 ⟨900⟩ (⟨1088⟩ :: ⟨1120⟩ :: R)
      (toMarketCodeMemory σ id) aw rdata σ k C) :
    ((∀ m, decodeStoredMarketData (externalCodePrefix σ id) = some m →
        ¬ toMarketDataFits (extCodeSizeWord σ id).toNat m) ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ m, decodeStoredMarketData (externalCodePrefix σ id) = some m ∧
      toMarketDataFits (extCodeSizeWord σ id).toNat m ∧
      RDret fork midnightBytecode g s0 σ (wordArrayBytes m.encodedWords)) := by
  have hs : (extCodeSizeWord σ id).toNat < 2^64 := by omega
  have hsize := externalCodePrefix_size σ id
  rcases midnightToMarketDecodeHeader (by omega) hs rd with
    ⟨hnone, hr⟩ | ⟨h32, hroot, hhead, aw1, k1, C1, rd1⟩
  · left
    refine ⟨?_, hr⟩
    intro m hm
    rw [decodeStoredMarketData_eq (by rw [hsize]; omega), hm] at hnone
    cases hnone
  have hdecode := decodeStoredMarketData_root (by rw [hsize]; exact h32) hroot
  have he : (⟨1088⟩ + extCodeSizeWord σ id).toNat = 1088 + (extCodeSizeWord σ id).toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change 1088 + _ < 2^256; omega)
  have he32 : ((⟨1088⟩ + extCodeSizeWord σ id) + ⟨32⟩).toNat =
      1120 + (extCodeSizeWord σ id).toNat := by
    rw [uadd_toNat, he]
    change (1088 + (extCodeSizeWord σ id).toNat + 32) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    omega
  have ho : (⟨1088⟩ + calldataWord (externalCodePrefix σ id) 0).toNat =
      1088 + (calldataWord (externalCodePrefix σ id) 0).toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change 1088 + _ < 2^256; omega)
  have hptr := toMarketCodeFreePtr_toNat hs
  have hptrsmall : (toMarketCodeFreePtr (extCodeSizeWord σ id)).toNat < 2^64 := by
    rw [hptr]
    dsimp only [returnDataAllocation]
    omega
  have hbelow : 1120 + (externalCodePrefix σ id).size ≤
      (toMarketCodeFreePtr (extCodeSizeWord σ id)).toNat := by
    rw [hptr, hsize]
    dsimp only [returnDataAllocation]
    omega
  have hfit (m : MarketData) :
      (toMarketCodeFreePtr (extCodeSizeWord σ id)).toNat + 288 + 160 * m.collaterals.length < 2^64 ↔
        toMarketDataFits (extCodeSizeWord σ id).toNat m := by
    rw [hptr]
    dsimp only [returnDataAllocation, toMarketDataFits]
    omega
  rcases midnightToMarketDecoder hstack (toMarketCodeMemory_bytes σ id hs) (by decide)
      (by rw [hsize]; exact hhead) (by rw [ho]; omega) hbelow hptrsmall
      (toMarketCodeMemory_properties σ id).2.1 (by rw [he, he32]; omega)
      (by rw [he32, hsize]) (by rw [hsize]; omega) rd1 with
    ⟨hbad, hr⟩ | ⟨m, hm, hfits, hr⟩
  · left
    refine ⟨?_, hr⟩
    intro m hm
    rw [hdecode] at hm
    exact fun hf ↦ hbad m hm ((hfit m).mpr hf)
  · exact Or.inr ⟨m, hdecode.trans hm, (hfit m).mp hfits, hr⟩

end Benchmarks.Midnight
