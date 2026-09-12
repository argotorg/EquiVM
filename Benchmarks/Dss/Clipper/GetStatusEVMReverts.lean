import Benchmarks.Dss.Clipper.GetStatusEVM
import Benchmarks.Dss.Clipper.Invalid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper
namespace Reasoning.Reach

set_option linter.unusedTactic false

set_option maxHeartbeats 2000000 in
theorem RD.clipperStatusAgeForPriceRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {top tic ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨8460⟩ (top :: tic :: ret :: R) mem aw rdata (cA, σ) k C)
    (hlt : (UInt256.ofNat ee.header.timestamp).toNat <
      (UInt256.land tic clipperSalesUint96Mask).toNat)
    (hov : R.length + 80 ≤ 1024) :
    RDrev code g s0 := by
  have rd8463pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8464⟩ := rd8463pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre := evm_run rd8464 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperStatusPriceSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8502⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 := rd9274pre.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch)
    (by evm_ov)
  exact RD.clipperSubRoutineRevert v hpatch rd9274 hlt
    (by simp only [List.length_cons]; omega)

theorem RD.clipperStatusPriceNoCode {code : ByteArray} (v : ClipperImmutables)
    (_hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {calcAddr : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨8549⟩ (calcAddr :: calcAddr :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ calcAddr = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨8549⟩) (okPc := ⟨8561⟩)
    h hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    hov

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusPriceCallDepthLimit {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g age top calcAddr tic ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8549⟩
      (calcAddr :: calcAddr :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨196⟩ ::
        clipperStatusPriceSelectorWord :: calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) rdata
      (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8565⟩
      (⟨0⟩ :: ⟨196⟩ :: clipperStatusPriceSelectorWord ::
        calcAddr :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: ret :: R)
      (clipperStatusPriceCalldataMem top age mem) (UInt256.ofNat 7) ByteArray.empty
      (cA, σ) k' C' := by
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

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusAgeForDoneRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price d0 d1 top tic ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8606 : RD code ee g s0 ⟨8606⟩ (price :: d0 :: d1 :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hltDone :
      (UInt256.ofNat ee.header.timestamp).toNat <
        (UInt256.land tic clipperSalesUint96Mask).toNat)
    (hov : R.length + 80 ≤ 1024) :
    RDrev code g s0 := by
  have rd9274pre := evm_run rd8606 with [
    raw push1 ⟨6⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8608⟩ := rd9274pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre' := evm_run rd8608 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8630⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 :=
    rd9274pre'.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch) (by evm_ov)
  exact RD.clipperSubRoutineRevert v hpatch rd9274 hltDone
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusAfterPriceRdivMulRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price d0 d1 top tic ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8606 : RD code ee g s0 ⟨8606⟩ (price :: d0 :: d1 :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hleDone :
      (UInt256.land tic clipperSalesUint96Mask).toNat ≤
        (UInt256.ofNat ee.header.timestamp).toNat)
    (htail :
      (UInt256.sub (UInt256.ofNat ee.header.timestamp)
          (UInt256.land tic clipperSalesUint96Mask)).toNat ≤
        (solcSlotWord σ ee ⟨6⟩).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat)
    (hov : R.length + 100 ≤ 1024) :
    RDrev code g s0 := by
  let ageForDone : UInt256 :=
    UInt256.sub (UInt256.ofNat ee.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
  let tail : UInt256 := solcSlotWord σ ee ⟨6⟩
  have rd9274pre := evm_run rd8606 with [
    raw push1 ⟨6⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8608⟩ := rd9274pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre' := evm_run rd8608 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8630⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 :=
    rd9274pre'.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch) (by evm_ov)
  obtain ⟨_, _, rd8630⟩ :=
    RD.clipperSubRoutine v hpatch rd9274 hleDone (clipperJumpDest8630 v hpatch)
      (by simp only [List.length_cons]; omega)
  have hgtTailZero : UInt256.gt ageForDone tail = ⟨0⟩ := by
    exact ugt_zero (by simpa [ageForDone, tail] using htail)
  have rd8637 := evm_run rd8630 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8652⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by simpa [ageForDone, tail] using hgtTailZero)
      (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨7⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8640⟩ := rd8637.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9290 := evm_run rd8640 with [
    raw push2 ⟨8650⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9290⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest9290 v hpatch) (by evm_ov)]
  exact RD.clipperRdivRoutineRevertMul v hpatch rd9290 hover
    (by simp only [List.length_cons]; omega)

theorem RD.clipperRdivRoutineInvalidDivZero {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9290⟩ (y :: x :: ret :: keep :: R) mem aw rdata acc k C)
    (hmul : x.toNat * clipperRayWord.toNat < UInt256.size)
    (hy : y = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    RDinvalid code g s0 := by
  have rd9293 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov)]
  have rd9311 := RD.pushConst rd9293 clipperRayWord
    (width := 12) (op := .PUSH12) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd9311 with [
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  have hmul' : clipperRayWord.toNat * x.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hmul
  obtain ⟨_, _, rd8259⟩ :=
    RD.clipperCheckedMul v hpatch rd8686 hmul' (clipperJumpDest8259 v hpatch) (by evm_ov)
  have rd8265 := evm_run rd8259 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8266⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by simpa [hy]) (by evm_ov)]
  exact RD.invalidHalt rd8265 (by clipper_runtime_decode)

set_option maxHeartbeats 1000000 in
theorem RD.clipperStatusAfterPriceRdivDivZeroInvalid {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price d0 d1 top tic ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd8606 : RD code ee g s0 ⟨8606⟩ (price :: d0 :: d1 :: top :: tic :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hleDone :
      (UInt256.land tic clipperSalesUint96Mask).toNat ≤
        (UInt256.ofNat ee.header.timestamp).toNat)
    (htail :
      (UInt256.sub (UInt256.ofNat ee.header.timestamp)
          (UInt256.land tic clipperSalesUint96Mask)).toNat ≤
        (solcSlotWord σ ee ⟨6⟩).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : top = ⟨0⟩)
    (hov : R.length + 100 ≤ 1024) :
    RDinvalid code g s0 := by
  let ageForDone : UInt256 :=
    UInt256.sub (UInt256.ofNat ee.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
  let tail : UInt256 := solcSlotWord σ ee ⟨6⟩
  have rd9274pre := evm_run rd8606 with [
    raw push1 ⟨6⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8608⟩ := rd9274pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9274pre' := evm_run rd8608 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8630⟩ (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9274⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9274 :=
    rd9274pre'.jump (by clipper_runtime_decode) (clipperJumpDest9274 v hpatch) (by evm_ov)
  obtain ⟨_, _, rd8630⟩ :=
    RD.clipperSubRoutine v hpatch rd9274 hleDone (clipperJumpDest8630 v hpatch)
      (by simp only [List.length_cons]; omega)
  have hgtTailZero : UInt256.gt ageForDone tail = ⟨0⟩ := by
    exact ugt_zero (by simpa [ageForDone, tail] using htail)
  have rd8637 := evm_run rd8630 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8652⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by simpa [ageForDone, tail] using hgtTailZero)
      (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨7⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd8640⟩ := rd8637.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9290 := evm_run rd8640 with [
    raw push2 ⟨8650⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9290⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest9290 v hpatch) (by evm_ov)]
  exact RD.clipperRdivRoutineInvalidDivZero v hpatch rd9290 hmul htop
    (by simp only [List.length_cons]; omega)

end Reasoning.Reach
end Benchmarks.Dss.Clipper
