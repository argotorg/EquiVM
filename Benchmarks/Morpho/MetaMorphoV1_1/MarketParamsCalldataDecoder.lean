import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldataFields
import Benchmarks.Morpho.MetaMorphoV1_1.StructAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded

/-! Full calldata struct decoding, including signed length checks and allocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def marketParamsCalldataMemory (mem : ByteArray) (ptr : UInt256) (cd : ByteArray) : ByteArray :=
  marketParamsCopyMem (writeWord mem 64 (nextCursor ptr ⟨160⟩)) ptr.toNat (marketParamsArgs cd)

theorem marketParamsCalldataDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (h4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : allocationFits ptr ⟨160⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11362⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ MarketParamsCalldataChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketParamsCalldataChecks I.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (ptr :: R)
        (marketParamsCalldataMemory mem ptr I.calldata) aw' rdata σ k' C') := by
  have hbad
      (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
        ⟨160⟩ ≠ ⟨0⟩) : RDrev (deployedRuntime v) g s0 := by
    have h := metaMorphoV1_1_block_11362_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_11362_taken_stack, List.length_cons]; omega) h
  by_cases hlo : 164 ≤ I.calldata.size
  case neg =>
    refine .inl ⟨?_, hbad ?_⟩
    · intro hc
      have hs := hc.2.1
      rw [marketParamsArgs_size] at hs
      omega
    · rw [calldataNot3_eq_sub h4 hsize]
      have hone : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ =
          ⟨1⟩ := solcCalldataStaticLenCheckShort (words := 5) h4 (by omega) hsize (by decide)
      rw [hone]
      decide
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    refine .inl ⟨fun hc ↦ hhi hc.1, hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize]
    have hone : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨160⟩ =
        ⟨1⟩ := solcCalldataStaticLenCheckHuge (words := 5) (by omega) hsize (by decide)
    rw [hone]
    decide
  have hlen : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨160⟩ =
      ⟨0⟩ := by
    rw [calldataNot3_eq_sub h4 hsize]
    exact solcCalldataStaticLenCheckOk (words := 5) hlo hhi hsize
  have r1 := metaMorphoV1_1_block_11362_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hlen rd
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_11375_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_11375_stack, hf] at r2
  obtain ⟨aw3, k3, C3, r3⟩ := allocateStruct160Return v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2
  have hptr : ptr.toNat + 160 < UInt256.size := lt_trans
    ((allocationFits_aligned ptr ⟨160⟩ (by decide +kernel)).mp hfit) (by decide)
  rcases marketParamsCalldataFields v (by omega) hlo hptr hret r3 with
    ⟨hc, hrev⟩ | ⟨hc, aw4, k4, C4, r4⟩
  · exact .inl ⟨fun h ↦ hc h.2, hrev⟩
  · exact .inr ⟨⟨hhi, hc⟩, aw4, k4, C4, r4⟩

theorem marketParamsCalldataMemory_bytes (mem : ByteArray) (ptr : UInt256) (cd : ByteArray)
    (hc : MarketParamsCalldataChecks cd) :
    (marketParamsCalldataMemory mem ptr cd).readWithPadding ptr.toNat 160 =
      (marketParamsData (marketParamsArgs cd)).bytes := by
  rw [MarketParamsData.bytes, marketParamsData_words hc.2]
  exact wordSequenceMemory_read (writeWord mem 64 (nextCursor ptr ⟨160⟩)) ptr.toNat
    [calldataWord (marketParamsArgs cd) 0, calldataWord (marketParamsArgs cd) 32,
      calldataWord (marketParamsArgs cd) 64, calldataWord (marketParamsArgs cd) 96,
      calldataWord (marketParamsArgs cd) 128]

theorem marketParamsCalldataMemory_hash (mem : ByteArray) (ptr : UInt256) (cd : ByteArray)
    (hc : MarketParamsCalldataChecks cd) :
    keccakWord ptr ⟨160⟩ (marketParamsCalldataMemory mem ptr cd) =
      (marketParamsData (marketParamsArgs cd)).id := by
  unfold keccakWord
  change UInt256.ofNat (fromByteArrayBigEndian
    (KEC ((marketParamsCalldataMemory mem ptr cd).readWithPadding ptr.toNat 160))) = _
  rw [marketParamsCalldataMemory_bytes mem ptr cd hc]
  exact keccakSlot_eq _

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
