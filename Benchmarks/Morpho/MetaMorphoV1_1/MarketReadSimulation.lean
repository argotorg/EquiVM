import Benchmarks.Morpho.MetaMorphoV1_1.MarketDecodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesAllocationSource

/-! Source/bytecode correspondence through the market reader and its decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketReadSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hparams : mem.readWithPadding params.toNat 160 = p.bytes)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16911⟩ (morpho :: params :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config
        (allocatedMarketBalancesFrame (immStore v) (AccountAddress.ofNat morpho.toNat) p ptr)
        evm allocatedMarketBalancesFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofNat morpho.toNat) "market" 0
        [wordBytes32Value p.id] (true, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks out ∧ out.size < 2 ^ 255 ∧
      allocationFits ptr ⟨384⟩ ∧
      memLoad ⟨64⟩ (marketReadMemory mem ptr p.id out) = nextCursor ptr ⟨384⟩ ∧
      (nextCursor ptr ⟨384⟩).toNat ≤ (marketReadMemory mem ptr p.id out).size ∧
      (∀ i, i < 6 → memLoad (nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i))
        (marketReadMemory mem ptr p.id out) = calldataWord out (32 * i)) ∧
      MemoryPrefix mem (marketReadMemory mem ptr p.id out) ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨16966⟩ (⟨0⟩ :: params :: nextCursor ptr ⟨192⟩ :: R)
        (marketReadMemory mem ptr p.id out) aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, h1⟩ := marketReachStaticcall v p (by omega)
    hfree hptr hparams rd
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    marketStaticcall v (by omega) hs h1
  have hhi : out.size < 2 ^ 255 := lt_trans (marketReturnSize hcall) (by decide)
  cases ok with
  | false =>
      exact .inl ⟨allocatedMarketBalancesBodyCallReverts hcall,
        marketCallFailure v (by omega) hout h2⟩
  | true =>
      rcases marketReturnAllocation v hstack hout h2 with
        ⟨hbad, hrev⟩ | ⟨hlong, hfit, aw3, k3, C3, h3⟩
      · refine .inl ⟨?_, hrev⟩
        by_cases hc : MarketChecks out
        · exact allocatedMarketBalancesBodyAllocationReverts hcall
            (by rw [marketDecode hhi, if_pos hc]) (fun hf ↦ hbad ⟨hc.1, hf⟩)
        · exact allocatedMarketBalancesBodyDecodeReverts hcall
            (by rw [marketDecode hhi, if_neg hc])
      · have hbound : ptr.toNat + 384 < 2 ^ 64 :=
          (allocationFits_aligned ptr ⟨384⟩ (by decide +kernel)).mp hfit
        have hdst : (nextCursor ptr ⟨192⟩).toNat = ptr.toNat + 192 :=
          uadd_word_ofNat_toNat ptr 192 (by change _ < 2 ^ 256; omega)
        have hcursor : (nextCursor ptr ⟨384⟩).toNat = ptr.toNat + 384 :=
          uadd_word_ofNat_toNat ptr 384 (lt_trans hbound (by decide))
        have hinput : ptr.toNat ≤ (marketCallMem mem ptr.toNat p.id).size := by
          rw [marketCallMem_size]; omega
        have hcopied := marketOutputMem_size hinput hlong hout
        have hspan : ptr.toNat + 192 ≤
            (marketOutputMem (marketCallMem mem ptr.toNat p.id) ptr out).size := by
          rw [hcopied]; omega
        have hptrBound : ptr.toNat + 192 < UInt256.size := by change _ < 2 ^ 256; omega
        have hread (off : Nat) (hoff : off + 32 ≤ 192) := marketReservedMem_load hlo
          hspan hptrBound hoff (marketOutputMem_load hinput hlong hout hptrBound hoff)
        rcases marketDecodeFields v (by simp only [List.length_cons]; omega) hlong
            (by rw [marketReservedMem_size]; omega) (by rw [hdst])
            (by rw [hdst]; change _ < 2 ^ 256; omega) hread
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
          ⟨hbad, hrev⟩ | ⟨hc, aw4, k4, C4, h4⟩
        · exact .inl ⟨allocatedMarketBalancesBodyDecodeReverts hcall
            (by rw [marketDecode hhi, if_neg hbad]), hrev⟩
        · obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_17648_packed
            (immWords := wordsOf (immStore v)) (by omega)
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
          refine .inr ⟨evm', out, aw5, k5, C5, hcall, hs', hc, hhi, hfit, ?_, ?_, ?_,
            marketReadMemory_prefix mem ptr p.id out hfit hlong hout, h5⟩
          · rw [marketReadMemory, marketCopyMem_free
              (by rw [marketReservedMem_size]; omega) (by rw [hdst]; omega),
              marketReservedMem_free, nextCursor_192_twice]
          · rw [hcursor, marketReadMemory, marketCopyMem_size, hdst]; omega
          · intro i hi
            have he : nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i) =
                UInt256.ofNat ((nextCursor ptr ⟨192⟩).toNat + 32 * i) := by
              apply u256_inj
              rw [uadd_word_ofNat_toNat _ _ (by rw [hdst]; change _ < 2 ^ 256; omega),
                UInt256.toNat_ofNat_of_lt (by rw [hdst]; change _ < 2 ^ 256; omega)]
            rw [he]
            exact marketCopyMem_field _ _ out i hi
              (by rw [hdst]; change _ < 2 ^ 256; omega)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
