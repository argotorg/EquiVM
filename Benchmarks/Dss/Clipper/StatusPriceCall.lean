import Benchmarks.Dss.Clipper.GetFeedPrice
import Benchmarks.Dss.Clipper.GetStatusEVMReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables


namespace Benchmarks.Dss.Clipper


-- GENERALIZES `RD.clipperStatusPricePostStaticcall`: callers enter the shared `status`
-- routine after a lock-store, so the immutable RD start state still mentions the
-- pre-lock account map while the current account map is the locked one.
set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusPricePostStaticcallFromCurrent {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State}
    {σ σ₀ A I} {g age top calcAddr tic ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code I (Sat256.ofUInt256 g) s0 ⟨8549⟩
      (calcAddr :: calcAddr :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨196⟩ ::
        clipperStatusPriceSelectorWord :: calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) rdata σ k C)
    (hs0Sigma0 : s0.σ₀ = σ₀)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hmem : mem.size = 96)
    (hov : R.length + 100 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I (Sat256.ofUInt256 g) s0 ⟨8565⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: clipperStatusPriceSelectorWord ::
          calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
        (clipperStatusPricePostCallMem top age mem o)
        (UInt256.ofNat 7) o σ' k' C'
    ∧ typedCallViaEVM (config v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofUInt256 calcAddr)) "price" 0
        [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)]
        (z, { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd8564⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8549⟩) (okPc := ⟨8561⟩)
      h hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperJumpDest8561 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨σ', z, o, A_in, callGas, k8565, C8565, hΘpack, rd8565raw, hosz⟩ :=
    RD.solcStaticcall rd8564 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, o, A', k8565, C8565, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
          UInt256.ofNat 7 := by
      native_decide
    simpa [clipperStatusPricePostCallMem] using haw ▸ rd8565raw
  · refine callCoincides (cfg := config v)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (name := "price")
      (args := [.int (Int.ofNat top.toNat), .int (Int.ofNat age.toNat)])
      (tgt := EVM.address (AccountAddress.ofUInt256 calcAddr)) (targetWord := calcAddr)
      (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := clipperStatusPriceCalldataMem top age mem)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := false)
      (fun hdepthEq =>
        absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from hdepthEq]; decide))
      ?_ ?_ ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨68⟩ : UInt256).toNat = 68 from by decide] using
        clipperStatusPriceEncode_eq v top age hmem
    · simpa [initState, hs0Sigma0] using hΘ

-- GENERALIZES `RD.clipperStatusPriceCallDepthLimit` for the same lock-store reason.
set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusPriceCallDepthLimitFromCurrent {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State}
    {σ : AccountMap}
    {I} {g age top calcAddr tic ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code I (Sat256.ofUInt256 g) s0 ⟨8549⟩
      (calcAddr :: calcAddr :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨196⟩ ::
        clipperStatusPriceSelectorWord :: calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) rdata σ k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code I (Sat256.ofUInt256 g) s0 ⟨8565⟩
      (⟨0⟩ :: ⟨196⟩ :: clipperStatusPriceSelectorWord ::
        calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) ByteArray.empty
      σ k' C' := by
  obtain ⟨gasWord, _, _, rd8564⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8549⟩) (okPc := ⟨8561⟩)
      h hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperJumpDest8561 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨k8565, C8565, rd8565raw⟩ :=
    RD.solcStaticcallDepthLimit rd8564 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  refine ⟨k8565, C8565, ?_⟩
  have hmin :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have hmem :
      ByteArray.empty.write 0 (clipperStatusPriceCalldataMem top age mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat =
        clipperStatusPriceCalldataMem top age mem := by
    rw [hmin, byteArray_write_len_zero]
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
        UInt256.ofNat 7 := by
    native_decide
  simpa [hmem, haw] using rd8565raw

end Benchmarks.Dss.Clipper
