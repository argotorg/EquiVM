import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateCallRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateMemory
import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdatePostCall
import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateValueRuntime

/-! Complete simulation of cap submission's allocated last-update reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

open Immutables

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem lastUpdateSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr cap params id tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨160⟩) (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8980⟩ (cap :: params :: id :: tag :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (lastUpdateFrame (immStore v) v.MORPHO id ptr) evm
      allocatedLastUpdateFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (value cursor first : UInt256) (mem' out : ByteArray),
      ExecFuncBody config (lastUpdateFrame (immStore v) v.MORPHO id ptr) evm
        allocatedLastUpdateFunction.body
        (.returned final evm' (some [uint256Value value, uint256Value cursor])) ∧
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧ MemoryPrefix mem mem' ptr.toNat ∧ ptr.toNat ≤ cursor.toNat ∧
      lastUpdateValue (memLoad first mem') = value ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨9144⟩
        ([first, UInt256.ofNat (2 ^ 128 - 1), cap, params, id, tag] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  have hb : ptr.toNat + 160 < 2 ^ 64 :=
    (allocationFits_aligned ptr ⟨160⟩ (by decide +kernel)).mp hfit
  obtain ⟨aw1, k1, C1, r1⟩ := lastUpdateReachHash v
    (by simp only [List.length_cons]; omega) hfree (by omega) rd
  rcases lastUpdateHashOffset v (by simp only [List.length_cons]; omega) hlo
      (lt_trans (by omega : ptr.toNat + 64 < 2 ^ 64) (by decide)) r1 with
    ⟨hbad, hrev⟩ | ⟨hslot, aw2, k2, C2, r2⟩
  · exact .inl ⟨lastUpdateBodySlotReverts evm (immStore v) v.MORPHO id ptr hfit hbad, hrev⟩
  obtain ⟨aw3, k3, C3, r3⟩ := lastUpdateReachArray v
    (by simp only [List.length_cons]; omega) hcalldata hb r2
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96
      (lt_trans (by omega : ptr.toNat + 96 < 2 ^ 64) (by decide))
  have h160 : (nextCursor ptr ⟨160⟩).toNat = ptr.toNat + 160 :=
    uadd_word_ofNat_toNat ptr 160 (lt_trans hb (by decide))
  obtain ⟨hin, hlen, hslotRead, hcursor⟩ := lastUpdateArrayMem_view mem I.calldata ptr id hlo hb
  obtain ⟨gasArg, aw4, k4, C4, r4⟩ := lastUpdateEncodeCall v
    (by simp only [List.length_cons]; omega) hin (by rw [h96, h160])
    (by rw [h160]; change _ < 2 ^ 256; omega) hcursor hlen hslotRead r3
  obtain ⟨evm', ok, out, aw5, k5, C5, hcall, hs', _, r5⟩ :=
    lastUpdateStaticcall v (by simp only [List.length_cons]; omega) hs r4
  rcases lastUpdatePostCall (frame := lastUpdateCallFrame (immStore v) v.MORPHO id ptr)
      v (by simp only [List.length_cons]; omega) (by rw [h160]; omega)
      (by rw [extSloadsCallMem_size]; omega) allocateFunction_lookup hcall r5 with
    ⟨hsource, hrev⟩ | ⟨_, hc, hraw, ha, hsource, aw6, k6, C6, r6⟩
  · exact .inl ⟨lastUpdateBodyCallReverts hfit hslot hsource, hrev⟩
  rcases lastUpdateFirstValue v (by omega) hc ha r6 with
    ⟨hzero, hrev⟩ | ⟨hn, aw7, k7, C7, r7⟩
  · have hempty : extSloadsReturnValues out = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [extSloadsReturnValues_length, hzero]
    rw [hempty] at hsource
    exact .inl ⟨lastUpdateBodyEmpty hfit hslot hsource, hrev⟩
  obtain ⟨values, hvalues⟩ := extSloadsReturnValues_cons hn
  have hbody := hsource
  rw [hvalues] at hbody
  have hreturn := lastUpdateBodyReturns hfit hslot hbody
  rw [← hvalues] at hreturn
  have harrayLo : 96 ≤
      (nextCursor (nextCursor ptr ⟨160⟩) (UInt256.ofNat out.size)).toNat := by
    have hmono := hraw.2
    rw [h160] at hmono
    omega
  have harrayBound := extSloadsArrayBound hc.length ha
  have hcursorNat :
      (nextCursor (nextCursor (nextCursor ptr ⟨160⟩) (UInt256.ofNat out.size))
        (extSloadsArraySize out)).toNat =
      (nextCursor (nextCursor ptr ⟨160⟩) (UInt256.ofNat out.size)).toNat +
        32 + 32 * extSloadsReturnCount out := by
    rw [nextCursor, uadd_toNat, extSloadsArraySize_rounded hc.length,
      Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  refine .inr ⟨evm', _, _, _, _, _, out, hreturn, hs',
    typedCallViaEVM_static_accountStorageStateEq hcall, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    aw7, k7, C7, r7⟩
  · simpa only [extSloadsFinalCursor, decodedArraySize_canonical] using
      extSloadsDecodedMem_cursor _ _ out harrayLo
  · simp only [extSloadsFinalCursor, decodedArraySize_canonical]
    exact le_trans harrayLo ha.2
  · simpa only [extSloadsFinalCursor, decodedArraySize_canonical] using ha.1
  · simp only [extSloadsFinalCursor, decodedArraySize_canonical,
      hcursorNat, extSloadsDecodedMem_size]
    omega
  · exact lastUpdateReadMemory_prefix mem I.calldata out ptr id hb hraw.2
  · simp only [extSloadsFinalCursor, decodedArraySize_canonical, hcursorNat]
    have hmono := hraw.2
    rw [h160] at hmono
    omega
  · rw [extSloadsDecodedMem_first _ _ _ hn (by change _ < 2 ^ 256; omega)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
