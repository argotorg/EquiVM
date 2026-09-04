import Benchmarks.Dss.Clipper.GetFeedPriceSuccess
import Benchmarks.Dss.Clipper.GetStatusEVMReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperSpotterParSelectorWord : UInt256 := ⟨1230844619⟩

abbrev clipperSpotterParSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperSpotterParSelectorWord ⟨224⟩

noncomputable def clipperSpotterParSelectorMem (mem : ByteArray) : ByteArray :=
  clipperSpotterParSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperSpotterParPostCallMem (mem out : ByteArray) : ByteArray :=
  out.write 0 mem 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

private theorem clipperGetFeedPriceSuccessJumpDest
    (pc : Nat) (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hpc : pc ∈ [9096, 9176, 9196, 9218, 9225]) :
    (D_J code 0).contains (UInt256.ofNat pc) = true := by
  simp at hpc
  rcases hpc with hpc | hpc | hpc | hpc | hpc <;> subst pc <;>
    apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch <;>
    unfold patches patchesFrom offsets immValues <;>
    simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons] <;>
    cases hIlk : wordBytes? v.ilk <;> simp [hIlk] <;> native_decide

theorem clipperGetFeedPriceJumpDest9096 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9096⟩ : UInt256) = true := by
  exact clipperGetFeedPriceSuccessJumpDest 9096 v hpatch (by simp)

theorem clipperGetFeedPriceJumpDest9176 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9176⟩ : UInt256) = true := by
  exact clipperGetFeedPriceSuccessJumpDest 9176 v hpatch (by simp)

theorem clipperGetFeedPriceJumpDest9196 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9196⟩ : UInt256) = true := by
  exact clipperGetFeedPriceSuccessJumpDest 9196 v hpatch (by simp)

theorem clipperGetFeedPriceJumpDest9218 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9218⟩ : UInt256) = true := by
  exact clipperGetFeedPriceSuccessJumpDest 9218 v hpatch (by simp)

theorem clipperGetFeedPriceJumpDest9225 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9225⟩ : UInt256) = true := by
  exact clipperGetFeedPriceSuccessJumpDest 9225 v hpatch (by simp)

theorem clipperSpotterParSelectorPrefix :
    clipperSpotterParSelectorShifted.toByteArray.extract 0 4 = spotterParSelector := by
  native_decide

theorem clipperSpotterParSelectorMem_size {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperSpotterParSelectorMem mem).size = 196 := by
  unfold clipperSpotterParSelectorMem
  rw [toByteArray_write32_size_of_le mem clipperSpotterParSelectorShifted 128
    196 196 hmem (by omega) (by simp)]

theorem clipperSpotterParSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperSpotterParSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterParSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperSpotterParSelectorShifted mem 128 64
    (by omega) (by omega) (by exact lt_usize _ (by omega)), hread64]

theorem clipperSpotterParSelectorMem_mload64 {mem : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterParSelectorMem mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperSpotterParSelectorMem mem).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperSpotterParSelectorMem_size hmem]; omega)
    (by decide) (clipperSpotterParSelectorMem_read64 hmem hread64)

theorem clipperSpotterParSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 196) :
    (clipperSpotterParSelectorMem mem).readWithPadding 128 4 = spotterParSelector := by
  unfold clipperSpotterParSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperSpotterParSelectorShifted mem
    128 0 4 (by norm_num) (by norm_num) (by norm_num)
    (by exact lt_usize _ (by omega))]
  exact clipperSpotterParSelectorPrefix

theorem clipperSpotterParEncode_eq (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (config v).externalABI.encode? "par" [] =
      some ((clipperSpotterParSelectorMem mem).readWithPadding 128 4) := by
  rw [clipperSpotterParSelectorMem_read128_4 hmem]
  simp [config, externalABI]

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPricePipPeekHasTrueToValBln
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = o.extract 0 32)
    (hread160 : mem.readWithPadding 160 32 = o.extract 32 64)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hhas : clipperPipPeekHasWord o ≠ ⟨0⟩)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9079⟩
      (clipperPipPeekHasWord o :: clipperPipPeekValueWord o :: pipWord ::
        ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem, hread64]
    native_decide
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding 128 32))) =
        clipperPipPeekValueWord o := by
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, hmem]
    rw [if_neg (by native_decide)]
    rw [hread128]
  have hmload160 :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding 160 32))) =
        clipperPipPeekHasWord o := by
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hmem]
    rw [if_neg (by native_decide)]
    rw [hread160]
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8991 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8991 v hpatch) (by evm_ov)
  have rdHasCheck := evm_run rd8991 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekValueWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekHasWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9079⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rdHasCheck.jumpiT (by clipper_runtime_decode) hhas
    (clipperGetFeedPriceJumpDest9079 v hpatch) (by evm_ov)⟩

theorem RD.clipperGetFeedPriceValBlnOverflowReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9079⟩
      (has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k C)
    (hover : UInt256.size ≤ val.toNat * (⟨1000000000⟩ : UInt256).toNat)
    (hov : R.length + 30 ≤ 1024) :
    RDrev code g s0 := by
  have rd8686 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9096⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨1000000000⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMulRevert
      v hpatch rd8686 (by simpa [Nat.mul_comm] using hover)
      (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceValBlnToParExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9079⟩
      (has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C)
    (hmul : val.toNat * (⟨1000000000⟩ : UInt256).toNat < UInt256.size)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9164⟩
      (clipperSpotterTarget σ ee :: clipperSpotterTarget σ ee :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: clipperSpotterParSelectorWord ::
        clipperSpotterTarget σ ee :: UInt256.mul val ⟨1000000000⟩ :: ⟨9225⟩ ::
        has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterParSelectorMem mem) (UInt256.ofNat 7) o (cA, σ) k' C' := by
  have rd8686 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9096⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨1000000000⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  obtain ⟨_, _, rd9096⟩ :=
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMul v hpatch rd8686
    (by simpa [Nat.mul_comm] using hmul) (clipperGetFeedPriceJumpDest9096 v hpatch)
    (by evm_ov)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem, hread64]
    native_decide
  have hmload64Selector := clipperSpotterParSelectorMem_mload64 hmem hread64
  obtain ⟨_, _, rdSpotter⟩ := (evm_run rd9096 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]).sload
      (by clipper_runtime_decode) (by evm_ov)
  have hpc9103 :
      (⟨9096⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩ = ⟨9103⟩ := by
    native_decide
  obtain ⟨_, _, rd9103⟩ : ∃ k C, RD code ee g s0 ⟨9103⟩
      (solcSlotWord σ ee ⟨3⟩ :: ⟨0⟩ :: UInt256.mul val ⟨1000000000⟩ ::
        ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hpc9103, u256_mul_comm] using rdSpotter⟩
  have rd9110Raw := evm_run rd9103 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨256⟩ (by clipper_runtime_decode) (by evm_ov),
    raw exp (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov)]
  have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hdiv : UInt256.div (solcSlotWord σ ee ⟨3⟩) ⟨1⟩ =
      solcSlotWord σ ee ⟨3⟩ := by
    apply u256_inj
    rw [udiv_toNat]
    exact Nat.div_one _
  have hpc9110 :
      (⟨9103⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨9110⟩ := by
    native_decide
  obtain ⟨_, _, rd9110⟩ : ∃ k C, RD code ee g s0 ⟨9110⟩
      (solcSlotWord σ ee ⟨3⟩ :: UInt256.mul val ⟨1000000000⟩ ::
        ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by simpa [hexp, hdiv, hpc9110] using rd9110Raw⟩
  have rd9119Raw := evm_run rd9110 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hpc9119 :
      (⟨9110⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨9119⟩ := by
    native_decide
  obtain ⟨_, _, rd9119⟩ : ∃ k C, RD code ee g s0 ⟨9119⟩
      (clipperSpotterTarget σ ee :: UInt256.mul val ⟨1000000000⟩ ::
        ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [clipperSpotterTarget, haddrMask, hpc9119, u256_land_comm] using rd9119Raw⟩
  have rd9128Raw := evm_run rd9119 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  have hpc9128 :
      (⟨9119⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨9128⟩ := by
    native_decide
  have hmaskTarget :
      UInt256.land (clipperSpotterTarget σ ee) solcAddrMask =
        clipperSpotterTarget σ ee := by
    exact solcAddrMask_clean (by
      simpa [clipperSpotterTarget, u256_land_comm] using
        solcAddrMask_result_canonical (solcSlotWord σ ee ⟨3⟩))
  have hmaskTargetLeft :
      UInt256.land solcAddrMask (clipperSpotterTarget σ ee) =
        clipperSpotterTarget σ ee := by
    rw [u256_land_comm]
    exact hmaskTarget
  obtain ⟨_, _, rd9128⟩ : ∃ k C, RD code ee g s0 ⟨9128⟩
      (clipperSpotterTarget σ ee :: UInt256.mul val ⟨1000000000⟩ ::
        ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [haddrMask, hpc9128, hmaskTargetLeft] using rd9128Raw⟩
  have rd9148Raw := evm_run rd9128 with [
    raw push4 clipperSpotterParSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (clipperSpotterParSelectorMem mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov)]
  have hselectorMask :
      UInt256.land clipperSpotterParSelectorWord ⟨4294967295⟩ =
        clipperSpotterParSelectorWord := by
    native_decide
  have hpc9148 :
      (⟨9128⟩ : UInt256) + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨9148⟩ := by
    native_decide
  obtain ⟨_, _, rd9148⟩ : ∃ k C, RD code ee g s0 ⟨9148⟩
      (⟨128⟩ :: clipperSpotterParSelectorWord :: clipperSpotterTarget σ ee ::
        UInt256.mul val ⟨1000000000⟩ :: ⟨9225⟩ :: has :: val :: pipWord :: ret ::
        scratch :: lot :: tab :: R)
      (clipperSpotterParSelectorMem mem) (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [hselectorMask, clipperSpotterParSelectorShifted,
        clipperSpotterParSelectorMem, hpc9148] using rd9148Raw⟩
  have rd9165Raw := evm_run rd9148 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64Selector (by decide) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have hpc9164 :
      (⟨9148⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨9164⟩ := by
    native_decide
  exact ⟨_, _, by
    simpa [hpc9164,
      show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide,
      show UInt256.sub ((⟨4⟩ : UInt256) + ⟨128⟩) ⟨128⟩ = ⟨4⟩ from by native_decide,
      u256_mul_comm] using rd9165Raw⟩

theorem clipperSpotterParPostCallMem_size {mem out : ByteArray}
    (hmem : mem.size = 196) (hout : out.size < UInt256.size) :
    (clipperSpotterParPostCallMem mem out).size = 196 := by
  unfold clipperSpotterParPostCallMem
  by_cases hshort : out.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hmem]
    · rw [write_eq_gen out mem 128 out.size hzero le_rfl (by rw [hmem]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hmem]
      omega
  · have hlo : 32 ≤ out.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_eq_gen out mem 128 32 (by omega) (by omega) (by rw [hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem]
    omega

theorem clipperSpotterParPostCallMem_read64 {mem out : ByteArray}
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperSpotterParPostCallMem mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterParPostCallMem
  by_cases hshort : out.size < 32
  · have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hread64
    · rw [write_read_below_gen_extend out mem 128 out.size 64 hzero le_rfl
        (by rw [hmem]; omega) (by omega)]
      exact hread64
  · have hlo : 32 ≤ out.size := by omega
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_read_below_gen_extend out mem 128 32 64 (by omega) (by omega)
      (by rw [hmem]; omega) (by omega)]
    exact hread64

theorem clipperSpotterParPostCallMem_read128_long {mem out : ByteArray}
    (hmem : mem.size = 196) (hlo : 32 ≤ out.size)
    (hout : out.size < UInt256.size) :
    (clipperSpotterParPostCallMem mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperSpotterParPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact byteArray_write_read_first_word_back out mem 128 32
    (by omega) (by omega) (by omega) (by rw [hmem]; omega)

theorem RD.clipperGetFeedPriceParNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {target : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : ℕ}
    (rd : RD code ee g s0 ⟨9164⟩ (target :: target :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : extCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨9164⟩) (okPc := ⟨9176⟩)
    rd hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) hov

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceParPostCall {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State} {cA σ I} {g : UInt256}
    {target valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD code I (Sat256.ofUInt256 g) s0 ⟨9164⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: clipperSpotterParSelectorWord :: target :: valBln :: ⟨9225⟩ ::
        has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcodeSize : extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hcalldata :
      (config v).externalABI.encode? "par" [] = some (mem.readWithPadding 128 4))
    (htarget : target = clipperSpotterTarget σ I)
    (hov : R.length + 100 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I (Sat256.ofUInt256 g) s0 ⟨9180⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: clipperSpotterParSelectorWord ::
          target :: valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch ::
          lot :: tab :: R)
        (clipperSpotterParPostCallMem mem o) (UInt256.ofNat 7) o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v)
        {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}
        (EVM.address (clipperGetFeedPriceSpotterAddress
          {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}))
        "par" 0 []
        (z, { {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I} with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd9179⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨9164⟩) (okPc := ⟨9176⟩)
      rd hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest9176 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k9180, C9180, hΘpack, rd9180raw, hosz⟩ :=
    RD.call rd9179 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k9180, C9180, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨4⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
          UInt256.ofNat 7 := by
      native_decide
    simpa [clipperSpotterParPostCallMem] using haw ▸ rd9180raw
  · refine callCoincides (cfg := config v)
      (evm := {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I})
      (name := "par") (args := [])
      (tgt := EVM.address (clipperGetFeedPriceSpotterAddress
        {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}))
      (targetWord := target)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas) (mem := mem)
      (inOff := ⟨128⟩) (inSize := ⟨4⟩) (callPerm := true)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (by simpa using hcalldata) ?_
    · apply Fin.ext
      simp [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget, htarget,
        EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [hperm] using hΘ

theorem RD.clipperGetFeedPriceParCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨9180⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨9180⟩) (okPc := ⟨9196⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperGetFeedPriceParCallSuccessToDecode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target valBln has val pipWord ret scratch lot tab : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨9180⟩
      (⟨1⟩ :: ⟨132⟩ :: clipperSpotterParSelectorWord :: target :: valBln ::
        ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9201⟩
      (valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd9197⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨9180⟩) (okPc := ⟨9196⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperGetFeedPriceJumpDest9196 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode) (by evm_ov)
  have rd9201 := evm_run rd9197 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by simpa using rd9201⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceParDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9201⟩
      (valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : o.size < 32) (hout : o.size < UInt256.size)
    (hov : R.length + 30 ≤ 1024) :
    RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) =
        ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem, hread64]
    native_decide
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ulit_toNat' o.size hout]
    exact hshort
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9218⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := rdGuardPre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.clipperGetFeedPriceParDecodeOkToRdiv
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9201⟩
      (valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = o.extract 0 32)
    (hlo : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9290⟩
      (clipperSpotterParWord o :: valBln :: ⟨9225⟩ :: has :: val :: pipWord ::
        ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 7) o acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) =
        ⟨128⟩ := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hmem, hread64]
    native_decide
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 128 32))) =
        clipperSpotterParWord o := by
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, hmem]
    rw [if_neg (by native_decide), hread128]
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjump :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9218⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9218 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjump
    (clipperGetFeedPriceJumpDest9218 v hpatch) (by evm_ov)
  have rd9290 := evm_run rd9218 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperSpotterParWord o) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov),
    raw push2 ⟨9290⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest9290 v hpatch) (by evm_ov)]
  exact ⟨_, _, by simpa using rd9290⟩

theorem RD.clipperGetFeedPriceRdivOverflowReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {par valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9290⟩
      (par :: valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch ::
        lot :: tab :: R)
      mem aw o acc k C)
    (hover : UInt256.size ≤ valBln.toNat * clipperRayWord.toNat)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g s0 := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRdivRoutineRevertMul
      v hpatch rd hover (by simp only [List.length_cons]; omega)

theorem RD.clipperGetFeedPriceRdivZeroInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {par valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9290⟩
      (par :: valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch ::
        lot :: tab :: R)
      mem aw o acc k C)
    (hmul : valBln.toNat * clipperRayWord.toNat < UInt256.size)
    (hpar : par = ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    RDinvalid code g s0 := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRdivRoutineInvalidDivZero
      v hpatch rd hmul hpar (by simp only [List.length_cons]; omega)

/-- Successful `getFeedPrice` cleanup.  At this point `ret` is the decoder's
    unused second return slot, while `scratch` is the caller's return PC.  Keeping
    those roles explicit avoids mistaking the compiler's final `SWAP4` for a
    return-address mismatch. -/
theorem RD.clipperGetFeedPriceRdivSuccess
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {par valBln has val pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9290⟩
      (par :: valBln :: ⟨9225⟩ :: has :: val :: pipWord :: ret :: scratch ::
        lot :: tab :: R)
      mem aw o acc k C)
    (hmul : valBln.toNat * clipperRayWord.toNat < UInt256.size)
    (hpar : par ≠ ⟨0⟩)
    (hret : (D_J code 0).contains scratch = true)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 scratch
      (UInt256.div (UInt256.mul valBln clipperRayWord) par :: lot :: tab :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd9225⟩ :=
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRdivRoutine
      v hpatch rd hmul hpar (clipperGetFeedPriceJumpDest9225 v hpatch)
      (by simp only [List.length_cons]; omega)
  have rdRet := evm_run rd9225 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov)]
  exact ⟨_, _, by simpa using rdRet⟩

end Benchmarks.Dss.Clipper
