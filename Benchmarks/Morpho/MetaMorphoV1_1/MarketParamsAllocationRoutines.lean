import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecodeRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationSource

/-! Complete source/bytecode simulation of the market-parameter reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem nextCursor_160_twice (ptr : UInt256) :
    nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩ = nextCursor ptr ⟨320⟩ := by
  change (ptr + (⟨160⟩ : UInt256)) + (⟨160⟩ : UInt256) = ptr + (⟨320⟩ : UInt256)
  rw [u256_add_assoc]
  rfl

theorem marketParamsAllocationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩ (id :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
        allocatedMarketParamsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (out mem' : ByteArray) (dst cursor aw' : UInt256)
      (k' C' : Nat),
      ExecFuncBody config (allocatedMarketParamsFrame v id ptr) evm
        allocatedMarketParamsFunction.body
        (.returned frame' evm' (some [marketParamsValue out, uint256Value cursor])) ∧
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧ MarketParamsChecks out ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧
      96 ≤ dst.toNat ∧ dst.toNat + 160 ≤ cursor.toNat ∧
      (∀ i, i < 5 → memLoad (dst + UInt256.ofNat (32 * i)) mem' =
        calldataWord out (32 * i)) ∧
      RD (deployedRuntime v) I g s0 ret (dst :: R) mem' aw' out evm'.accountMap k' C' := by
  by_cases hfit : allocationFits ptr ⟨160⟩
  · have hfirst : (nextCursor ptr ⟨160⟩).toNat = ptr.toNat + 160 :=
      uadd_word_ofNat_toNat ptr 160 (lt_trans
        ((allocationFits_aligned ptr ⟨160⟩ (by decide +kernel)).mp hfit) (by decide))
    obtain ⟨gasArg, aw1, k1, C1, h1⟩ := marketParamsReachStaticcall v
      (by simp only [List.length_cons]; omega) hfree hlo hfit rd
    obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
      marketParamsStaticcall v (by simp only [List.length_cons]; omega) hs h1
    have hhi : out.size < 2 ^ 255 := lt_trans (marketParamsReturnSize hcall) (by decide)
    cases ok with
    | false =>
        exact .inl ⟨allocatedMarketParamsBodyCallReverts v evm evm' id ptr out hfit hcall,
          marketParamsCallFailure v (by simp only [List.length_cons]; omega) hout h2⟩
    | true =>
        rcases marketParamsReturnAllocation v (by simp only [List.length_cons]; omega)
            hout h2 with ⟨hbad, hrev⟩ | ⟨hlong, hpost, aw3, k3, C3, h3⟩
        · refine .inl ⟨?_, hrev⟩
          by_cases hc : MarketParamsChecks out
          · exact allocatedMarketParamsBodyAllocationReverts hfit hcall
              (by rw [marketParamsDecode hhi, if_pos hc]) (fun hf ↦ hbad ⟨hc.1, hf⟩)
          · exact allocatedMarketParamsBodyDecodeReverts v evm evm' id ptr out hfit hcall
              (by rw [marketParamsDecode hhi, if_neg hc])
        · have hpostBound : (nextCursor ptr ⟨160⟩).toNat + 320 < 2 ^ 64 :=
            (allocationFits_aligned _ ⟨320⟩ (by decide +kernel)).mp hpost
          have hdst : (nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩).toNat =
              (nextCursor ptr ⟨160⟩).toNat + 160 :=
            uadd_word_ofNat_toNat _ 160 (by change _ < 2 ^ 256; omega)
          have hcursor : (marketParamsFinalCursor ptr).toNat =
              (nextCursor ptr ⟨160⟩).toNat + 320 :=
            uadd_word_ofNat_toNat _ 320 (lt_trans hpostBound (by decide))
          have hinput : (nextCursor ptr ⟨160⟩).toNat ≤
              (marketParamsCallMem (marketParamsInitialMem mem ptr)
                (nextCursor ptr ⟨160⟩).toNat id).size := by
            rw [marketParamsCallMem_size]; omega
          have hcopied := marketParamsOutputMem_size hinput hlong hout
          have hspan : (nextCursor ptr ⟨160⟩).toNat + 160 ≤
              (marketParamsOutputMem
                (marketParamsCallMem (marketParamsInitialMem mem ptr)
                  (nextCursor ptr ⟨160⟩).toNat id) (nextCursor ptr ⟨160⟩) out).size := by
            rw [hcopied]; omega
          have hptrBound : (nextCursor ptr ⟨160⟩).toNat + 160 < UInt256.size := by
            change _ < 2 ^ 256; omega
          have hread (off : Nat) (hoff : off + 32 ≤ 160) := marketParamsReservedMem_load
            (by rw [hfirst]; omega) hspan hptrBound hoff
            (marketParamsOutputMem_load hinput hlong hout hptrBound hoff)
          rcases marketParamsDecodeFields v (by omega) hlong
              (by rw [marketParamsReservedMem_size]; omega) (by rw [hdst])
              (by rw [hdst]; change _ < 2 ^ 256; omega) hread hret h3 with
            ⟨hbad, hrev⟩ | ⟨hc, aw4, k4, C4, h4⟩
          · exact .inl ⟨allocatedMarketParamsBodyDecodeReverts v evm evm' id ptr out hfit hcall
              (by rw [marketParamsDecode hhi, if_neg hbad]), hrev⟩
          · refine .inr ⟨evm', _, out, _, _, marketParamsFinalCursor ptr, aw4, k4, C4,
              allocatedMarketParamsBodyReturns hfit hcall
                (by rw [marketParamsDecode hhi, if_pos hc]) hpost, hs',
              typedCallViaEVM_static_accountStorageStateEq hcall, hc,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, h4⟩
            · rw [marketParamsCopyMem_free
                (by rw [marketParamsReservedMem_size]; omega)
                (by rw [hdst, hfirst]; omega), marketParamsReservedMem_free,
                nextCursor_160_twice]
              rfl
            · rw [hcursor, hfirst]; omega
            · rw [hcursor]; exact hpostBound
            · rw [hcursor, marketParamsCopyMem_size, hdst]; omega
            · rw [hdst, hfirst]; omega
            · rw [hdst, hcursor]
            · intro i hi
              have he : nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩ + UInt256.ofNat (32 * i) =
                  UInt256.ofNat
                    ((nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩).toNat + 32 * i) := by
                apply u256_inj
                rw [uadd_word_ofNat_toNat _ _ (by rw [hdst]; change _ < 2 ^ 256; omega),
                  UInt256.toNat_ofNat_of_lt (by rw [hdst]; change _ < 2 ^ 256; omega)]
              rw [he]
              exact marketParamsCopyMem_field _ _ out i hi
                (by rw [hdst]; change _ < 2 ^ 256; omega)
  · exact .inl ⟨allocatedMarketParamsBodyPrefixReverts v evm id ptr hfit,
      marketParamsPrefixRevert v (by simp only [List.length_cons]; omega) hfree hfit rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
