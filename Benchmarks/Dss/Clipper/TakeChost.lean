import Benchmarks.Dss.Clipper.TakePostStatus

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeJumpDest4203 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4203⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4217 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4217⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTakeJumpDest4221 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4221⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 5000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem RD.clipperTakeOweLtTabSliceLtLotChostGeToJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceLt : slice.toNat < lot.toNat)
    (hchostLe : (solcSlotWord σ ee ⟨9⟩).toNat ≤
      (UInt256.sub tab (UInt256.mul price slice)).toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4223⟩
      (slice :: UInt256.mul price slice :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨0⟩ :=
    ugt_zero hle
  have hltWord : UInt256.lt (UInt256.mul price slice) tab = ⟨1⟩ :=
    ult_one hlt
  have hsliceLtWord : UInt256.lt slice lot = ⟨1⟩ :=
    ult_one hsliceLt
  have hchostGtWord :
      UInt256.gt (solcSlotWord σ ee ⟨9⟩)
        (UInt256.sub tab (UInt256.mul price slice)) = ⟨0⟩ :=
    ugt_zero hchostLe
  have hcond4067 :
      UInt256.isZero (UInt256.gt (UInt256.mul price slice) tab) ≠ ⟨0⟩ := by
    rw [hgtWord]
    native_decide
  have hcond4096 :
      UInt256.isZero (UInt256.lt (UInt256.mul price slice) tab) = ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have hcondSlice : UInt256.isZero (UInt256.lt slice lot) = ⟨0⟩ := by
    rw [hsliceLtWord]
    native_decide
  have hcondChost :
      UInt256.isZero
          (UInt256.gt (solcSlotWord σ ee ⟨9⟩)
            (UInt256.sub tab (UInt256.mul price slice))) ≠ ⟨0⟩ := by
    rw [hchostGtWord]
    native_decide
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4087 := rd4067pre.jumpiT (by clipper_runtime_decode) hcond4067
    (clipperTakeJumpDest4087 v hpatch) (by evm_ov)
  have rd4096pre := evm_run rd4087 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4101⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4097 := rd4096pre.jumpiNT (by clipper_runtime_decode) hcond4096 (by evm_ov)
  have rd4101 := evm_run rd4097 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov)]
  have rd4106pre := evm_run rd4101 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4107 := rd4106pre.jumpiNT (by clipper_runtime_decode) hcondSlice (by evm_ov)
  have rd4109pre := evm_run rd4107 with [
    raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4110raw⟩ := rd4109pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd4119pre := evm_run rd4110raw with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4221⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4221 := rd4119pre.jumpiT (by clipper_runtime_decode) hcondChost
    (clipperTakeJumpDest4221 v hpatch) (by evm_ov)
  have rd4223 := evm_run rd4221 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4223⟩

theorem RD.clipperTakeOweLtTabSliceLtLotChostAdjustToJoin {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceLt : slice.toNat < lot.toNat)
    (hchostGt : (UInt256.sub tab (UInt256.mul price slice)).toNat <
      (solcSlotWord σ ee ⟨9⟩).toNat)
    (htabChost : (solcSlotWord σ ee ⟨9⟩).toNat < tab.toNat)
    (hprice : price ≠ ⟨0⟩)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4223⟩
      (UInt256.div (UInt256.sub tab (solcSlotWord σ ee ⟨9⟩)) price ::
        UInt256.sub tab (solcSlotWord σ ee ⟨9⟩) :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨0⟩ :=
    ugt_zero hle
  have hltWord : UInt256.lt (UInt256.mul price slice) tab = ⟨1⟩ :=
    ult_one hlt
  have hsliceLtWord : UInt256.lt slice lot = ⟨1⟩ :=
    ult_one hsliceLt
  have hchostGtWord :
      UInt256.gt (solcSlotWord σ ee ⟨9⟩)
        (UInt256.sub tab (UInt256.mul price slice)) = ⟨1⟩ :=
    ugt_one hchostGt
  have htabChostWord : UInt256.gt tab (solcSlotWord σ ee ⟨9⟩) = ⟨1⟩ :=
    ugt_one htabChost
  have hcond4067 :
      UInt256.isZero (UInt256.gt (UInt256.mul price slice) tab) ≠ ⟨0⟩ := by
    rw [hgtWord]
    native_decide
  have hcond4096 :
      UInt256.isZero (UInt256.lt (UInt256.mul price slice) tab) = ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have hcondSlice : UInt256.isZero (UInt256.lt slice lot) = ⟨0⟩ := by
    rw [hsliceLtWord]
    native_decide
  have hcondChost :
      UInt256.isZero
          (UInt256.gt (solcSlotWord σ ee ⟨9⟩)
            (UInt256.sub tab (UInt256.mul price slice))) = ⟨0⟩ := by
    rw [hchostGtWord]
    native_decide
  have hcondTabChost : UInt256.gt tab (solcSlotWord σ ee ⟨9⟩) ≠ ⟨0⟩ := by
    rw [htabChostWord]
    native_decide
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4087 := rd4067pre.jumpiT (by clipper_runtime_decode) hcond4067
    (clipperTakeJumpDest4087 v hpatch) (by evm_ov)
  have rd4096pre := evm_run rd4087 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4101⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4097 := rd4096pre.jumpiNT (by clipper_runtime_decode) hcond4096 (by evm_ov)
  have rd4101 := evm_run rd4097 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov)]
  have rd4106pre := evm_run rd4101 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4107 := rd4106pre.jumpiNT (by clipper_runtime_decode) hcondSlice (by evm_ov)
  have rd4109pre := evm_run rd4107 with [
    raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4110raw⟩ := rd4109pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd4119pre := evm_run rd4110raw with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4221⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4120 := rd4119pre.jumpiNT (by clipper_runtime_decode) hcondChost (by evm_ov)
  have rd4126pre := evm_run rd4120 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4203⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4203 := rd4126pre.jumpiT (by clipper_runtime_decode) hcondTabChost
    (clipperTakeJumpDest4203 v hpatch) (by evm_ov)
  have rd4215pre := evm_run rd4203 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4217⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4217 := rd4215pre.jumpiT (by clipper_runtime_decode) hprice
    (clipperTakeJumpDest4217 v hpatch) (by evm_ov)
  have rd4223 := evm_run rd4217 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4223⟩

end Benchmarks.Dss.Clipper
