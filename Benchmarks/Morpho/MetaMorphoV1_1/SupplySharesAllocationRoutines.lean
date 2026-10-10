import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationSetup
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsValueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesMemoryPrefix

/-! Complete source/bytecode simulation for the supply-share reader with cursor passing. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem supplySharesAllocationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho id user ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (hstack : R.length + 15 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩ (morpho :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config
        (allocatedSupplySharesFrame imms (AccountAddress.ofNat morpho.toNat)
          (AccountAddress.ofNat user.toNat) id ptr) evm
        allocatedSupplySharesFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (frame' : Frame) (value cursor : UInt256) (mem' : ByteArray)
        (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
        ExecFuncBody config
          (allocatedSupplySharesFrame imms (AccountAddress.ofNat morpho.toNat)
            (AccountAddress.ofNat user.toNat) id ptr) evm allocatedSupplySharesFunction.body
          (.returned frame' evm' (some [uint256Value value, uint256Value cursor])) ∧
        SourceState s0 I evm'.accountMap evm' ∧
        accountStorageStateEq evm.accountMap evm'.accountMap ∧
        memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
        cursor.toNat ≤ mem'.size ∧
        MemoryPrefix mem mem' ptr.toNat ∧ ptr.toNat ≤ cursor.toNat ∧
        RD (deployedRuntime v) I g s0 ret (value :: R) mem' aw' out evm'.accountMap k' C' := by
  by_cases hfit : allocationFits ptr ⟨256⟩
  · have hb : ptr.toNat + 256 < 2 ^ 64 :=
      (allocationFits_aligned ptr ⟨256⟩ (by decide +kernel)).mp hfit
    have hptr : (nextCursor ptr ⟨256⟩).toNat = ptr.toNat + 256 :=
      uadd_word_ofNat_toNat ptr 256 (lt_trans hb (by decide))
    obtain ⟨gasArg, aw1, k1, C1, h1⟩ := supplySharesReachStaticcall v
      (by simp only [List.length_cons]; omega) hcalldata hfree hlo hfit rd
    obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', _, h2⟩ :=
      extSloadsStaticcall v (by simp only [List.length_cons]; omega) hs h1
    rcases extSloadsPostCallSimulation
        (frame := allocatedSupplySharesCallFrame imms (AccountAddress.ofNat morpho.toNat)
          (AccountAddress.ofNat user.toNat) id ptr) v
        (by simp only [List.length_cons]; omega) (by rw [hptr]; omega)
        (by rw [extSloadsCallMem_size]; omega) allocateFunction_lookup hcall h2 with
      ⟨hsource, hrev⟩ | ⟨_, hc, hraw, ha, hsource, aw3, k3, C3, h3⟩
    · exact .inl ⟨allocatedSupplySharesBodyCallReverts evm imms _ _ id ptr hfit hsource, hrev⟩
    · rcases extSloadsValueReturn v (by omega) hc ha hret h3 with
        ⟨hzero, hrev⟩ | ⟨hn, aw4, k4, C4, h4⟩
      · have hempty : extSloadsReturnValues out = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [extSloadsReturnValues_length, hzero]
        rw [hempty] at hsource
        exact .inl ⟨allocatedSupplySharesBodyEmpty hfit hsource, hrev⟩
      · obtain ⟨values, hvalues⟩ := extSloadsReturnValues_cons hn
        have hbody := hsource
        rw [hvalues] at hbody
        have hsupply := allocatedSupplySharesBodyReturns hfit hbody
        rw [← hvalues] at hsupply
        have harrayLo : 96 ≤
            (nextCursor (nextCursor ptr ⟨256⟩) (UInt256.ofNat out.size)).toNat := by
          have hmono := hraw.2
          omega
        have harrayBound := extSloadsArrayBound hc.length ha
        have hcursorNat :
            (nextCursor (nextCursor (nextCursor ptr ⟨256⟩) (UInt256.ofNat out.size))
              (extSloadsArraySize out)).toNat =
            (nextCursor (nextCursor ptr ⟨256⟩) (UInt256.ofNat out.size)).toNat +
              32 + 32 * extSloadsReturnCount out := by
          rw [nextCursor, uadd_toNat, extSloadsArraySize_rounded hc.length,
            Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
          omega
        refine .inr ⟨evm', _, _, _, _, aw4, out, k4, C4, hsupply, hs',
          typedCallViaEVM_static_accountStorageStateEq hcall, ?_, ?_, ?_, ?_, ?_, ?_, h4⟩
        · simpa only [extSloadsFinalCursor, decodedArraySize_canonical] using
            extSloadsDecodedMem_cursor _ _ out harrayLo
        · simp only [extSloadsFinalCursor, decodedArraySize_canonical]
          exact le_trans harrayLo ha.2
        · simpa only [extSloadsFinalCursor, decodedArraySize_canonical] using ha.1
        · simp only [extSloadsFinalCursor, decodedArraySize_canonical,
            hcursorNat, extSloadsDecodedMem_size]
          omega
        · exact supplySharesReadMemory_prefix mem I.calldata out ptr id user hb hraw.2
        · simp only [extSloadsFinalCursor, decodedArraySize_canonical, hcursorNat]
          have hmono := hraw.2
          omega
  · exact .inl ⟨allocatedSupplySharesBodyPrefixReverts evm imms _ _ id ptr hfit,
      supplySharesPrefixAllocationRevert v (by simp only [List.length_cons]; omega) hfree hlo
        (by rwa [allocationFits_aligned _ _ (by decide +kernel)] at hfit) rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
