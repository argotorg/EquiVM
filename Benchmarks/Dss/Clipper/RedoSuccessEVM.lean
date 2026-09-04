import Benchmarks.Dss.Clipper.GetFeedPriceSuccessEVM
import Benchmarks.Dss.Clipper.Redo

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

private theorem clipperRedoSuccessJumpDest
    (pc : Nat) (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hpc : pc ∈ [6235, 7733, 7813, 7880, 7910, 7913, 7932, 8091, 8111, 8116, 8118,
      8238, 9258]) :
    (D_J code 0).contains (UInt256.ofNat pc) = true := by
  simp at hpc
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc |
      hpc | hpc <;>
    subst pc <;>
    apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch <;>
    unfold patches patchesFrom offsets immValues <;>
    simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons] <;>
    cases hIlk : wordBytes? v.ilk <;> simp [hIlk] <;> native_decide

theorem clipperRedoJumpDest6235 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6235⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 6235 v hpatch (by simp)

theorem clipperRedoJumpDest8238 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8238⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 8238 v hpatch (by simp)

theorem clipperRedoJumpDest9258 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨9258⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 9258 v hpatch (by simp)

theorem clipperRedoJumpDest7733 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7733⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7733 v hpatch (by simp)

theorem clipperRedoJumpDest7813 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7813⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7813 v hpatch (by simp)

theorem clipperRedoJumpDest7880 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7880⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7880 v hpatch (by simp)

theorem clipperRedoJumpDest7910 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7910⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7910 v hpatch (by simp)

theorem clipperRedoJumpDest7913 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7913⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7913 v hpatch (by simp)

theorem clipperRedoJumpDest7932 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7932⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 7932 v hpatch (by simp)

theorem clipperRedoJumpDest8091 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8091⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 8091 v hpatch (by simp)

theorem clipperRedoJumpDest8111 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8111⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 8111 v hpatch (by simp)

theorem clipperRedoJumpDest8116 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8116⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 8116 v hpatch (by simp)

theorem clipperRedoJumpDest8118 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8118⟩ : UInt256) = true :=
  clipperRedoSuccessJumpDest 8118 v hpatch (by simp)

theorem RD.clipperRedoFeedPriceToRmul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {feedPrice discard lot tab done top tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7719⟩
      (feedPrice :: discard :: lot :: tab :: done :: top :: tic :: usr :: two ::
        kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9233⟩
      (solcSlotWord acc.2 ee ⟨5⟩ :: feedPrice :: ⟨7733⟩ :: feedPrice :: lot ::
        tab :: done :: top :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have rdSload := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7733⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨5⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdBuf⟩ := rdSload.sload (by clipper_runtime_decode) (by evm_ov)
  have rd9233 := evm_run rdBuf with [
    raw push2 ⟨9233⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode)
      (by
        apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch
        unfold patches patchesFrom offsets immValues
        simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
        cases hIlk : wordBytes? v.ilk <;> simp [hIlk] <;> native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [solcSlotWord] using rd9233⟩

theorem RD.clipperRedoRmulOverflowReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {buf feedPrice keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9233⟩
      (buf :: feedPrice :: ⟨7733⟩ :: keep :: R) mem aw o acc k C)
    (hover : UInt256.size ≤ buf.toNat * feedPrice.toNat)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRmulRoutineRevert
      v hpatch rd hover (by omega)

theorem RD.clipperRedoRmulSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {buf feedPrice keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9233⟩
      (buf :: feedPrice :: ⟨7733⟩ :: keep :: R) mem aw o acc k C)
    (hmul : buf.toNat * feedPrice.toNat < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7733⟩
      (UInt256.div (UInt256.mul buf feedPrice) clipperRayWord :: keep :: R)
      mem aw o acc k' C' := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRmulRoutine
      v hpatch rd hmul (clipperRedoJumpDest7733 v hpatch) (by omega)

abbrev clipperRedoTopSlotWord (id : UInt256) : UInt256 :=
  solcMappingSlot ⟨12⟩ id + ⟨4⟩

abbrev clipperRedoTipWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (solcSlotWord σ ee ⟨8⟩)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)

abbrev clipperRedoChipWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ ee ⟨8⟩) ⟨18446744073709551615⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoTopPositiveToIncentiveValues {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {topNew feedPrice lot tab done tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7733⟩
      (topNew :: feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two ::
        kpr :: id :: ret :: sel :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C)
    (htop : 0 < topNew.toNat)
    (hmem : mem.size = 196)
    (hov : R.length + 40 ≤ 1024)
    (hperm : ee.perm = true) :
    let topSlot := clipperRedoTopSlotWord id
    let σTop := sstoreAccountMap ee.codeOwner σ topSlot topNew
    ∃ k' C', RD code ee g s0 ⟨7867⟩
      (⟨0⟩ :: clipperRedoChipWord σTop ee :: clipperRedoTipWord σTop ee ::
        feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two :: kpr :: id ::
        ret :: sel :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) o (cA, σTop) k' C' := by
  intro topSlot σTop
  have hgt : UInt256.gt topNew ⟨0⟩ = ⟨1⟩ :=
    ugt_one (by simpa using htop)
  have rdGuard := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7813⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rdGuard
  have rd7813 := rdGuard.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest7813 v hpatch)
    (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ id := by
    exact twoWordHashMem_solcMappingSlot_of_ge (⟨12⟩ : UInt256) id (by omega)
  have rdHash := evm_run rd7813 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨12⟩ id) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost hslot (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdHash.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rdPacked := evm_run rdStore with [
    raw push1 ⟨8⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdPackedLoad⟩ := rdPacked.sload (by clipper_runtime_decode) (by evm_ov)
  have rdTipConstPre := evm_run rdPackedLoad with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨192⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTipConst := RD.pushConst rdTipConstPre ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd7867 := evm_run rdTipConst with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [topSlot, σTop, clipperRedoTopSlotWord, clipperRedoTipWord,
      clipperRedoChipWord, solcSlotWord, u256_add_comm] using rd7867⟩

theorem RD.clipperRedoIncentiveInactive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7867⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8118⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have rd7880Pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7880⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov)]
  have hgt0 : UInt256.gt (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by native_decide
  rw [hgt0] at rd7880Pre
  have rd8118Pre := evm_run rd7880Pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8118⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd8118Pre.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest8118 v hpatch)
    (by evm_ov)⟩

theorem RD.clipperRedoIncentiveActiveOfTip {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7867⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (htip : tip ≠ ⟨0⟩)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7886⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have hcond : UInt256.isZero (UInt256.isZero tip) = ⟨1⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne htip]
    decide
  have rd7880Pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7880⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hcond] at rd7880Pre
  have rd7880 := rd7880Pre.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest7880 v hpatch)
    (by evm_ov)
  have rd7886Pre := evm_run rd7880 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8118⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by simpa using
    rd7886Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)⟩

theorem RD.clipperRedoIncentiveActiveOfChip {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {coin chip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7867⟩
      (coin :: chip :: ⟨0⟩ :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hchip : chip ≠ ⟨0⟩)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7886⟩
      (coin :: chip :: ⟨0⟩ :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have hchipPos : 0 < chip.toNat :=
    Nat.pos_of_ne_zero (fun h => hchip (uint256_toNat_eq_zero h))
  have hgt : UInt256.gt chip ⟨0⟩ = ⟨1⟩ := ugt_one (by simpa using hchipPos)
  have rd7880Pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7880⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rd7880Pre
  have rd7886Pre := evm_run rd7880Pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8118⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by simpa using
    rd7886Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)⟩

abbrev clipperRedoChostWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  solcSlotWord σ ee ⟨9⟩

theorem RD.clipperRedoTabBelowChostSkipsIncentive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7886⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o (cA, σ) k C)
    (htab : tab.toNat < (clipperRedoChostWord σ ee).toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8118⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o (cA, σ) k' C' := by
  have rdSlot := evm_run rd with [
    raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdChost⟩ := rdSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have hlt : UInt256.lt tab (clipperRedoChostWord σ ee) = ⟨1⟩ := ult_one htab
  have rd7913Pre := evm_run rdChost with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7913⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hlt] at rd7913Pre
  have rd7913 := rd7913Pre.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest7913 v hpatch)
    (by evm_ov)
  have rd8116Pre := evm_run rd7913 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8116⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8116 := rd8116Pre.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest8116 v hpatch)
    (by evm_ov)
  exact ⟨_, _, evm_run rd8116 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]⟩

theorem RD.clipperRedoToLotFeedCheckedMul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7886⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o (cA, σ) k C)
    (htab : (clipperRedoChostWord σ ee).toNat ≤ tab.toNat)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8686⟩
      (feedPrice :: lot :: ⟨7910⟩ :: clipperRedoChostWord σ ee ::
        clipperRedoChostWord σ ee :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o (cA, σ) k' C' := by
  have rdSlot := evm_run rd with [
    raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdChost⟩ := rdSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have hlt : UInt256.lt tab (clipperRedoChostWord σ ee) = ⟨0⟩ := ult_zero htab
  have rd7899Pre := evm_run rdChost with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7913⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hlt] at rd7899Pre
  have rd8686 := evm_run
      (rd7899Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)) with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7910⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  exact ⟨_, _, by simpa [clipperRedoChostWord, solcSlotWord] using rd8686⟩

theorem RD.clipperRedoLotFeedOverflowReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {feedPrice lot chost coin chip tip tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8686⟩
      (feedPrice :: lot :: ⟨7910⟩ :: chost :: chost :: coin :: chip :: tip ::
        feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two :: kpr :: id ::
        ret :: sel :: R)
      mem aw o acc k C)
    (hover : UInt256.size ≤ lot.toNat * feedPrice.toNat)
    (hov : R.length + 35 ≤ 1024) :
    RDrev code g s0 := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMulRevert
      v hpatch rd (by simpa [Nat.mul_comm] using hover)
      (by simp only [List.length_cons]; omega)

theorem RD.clipperRedoLotFeedMulSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {feedPrice lot chost coin chip tip tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8686⟩
      (feedPrice :: lot :: ⟨7910⟩ :: chost :: chost :: coin :: chip :: tip ::
        feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two :: kpr :: id ::
        ret :: sel :: R)
      mem aw o acc k C)
    (hmul : lot.toNat * feedPrice.toNat < UInt256.size)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7910⟩
      (UInt256.mul lot feedPrice :: chost :: chost :: coin :: chip :: tip ::
        feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two :: kpr :: id ::
        ret :: sel :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd7910⟩ :=
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperCheckedMul
      v hpatch rd (by simpa [Nat.mul_comm] using hmul)
      (clipperRedoJumpDest7910 v hpatch) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [u256_mul_comm] using rd7910⟩

theorem RD.clipperRedoLotFeedBelowChostSkipsIncentive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {lotFeed chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7910⟩
      (lotFeed :: chost :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hlt : lotFeed.toNat < chost.toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8118⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic :: usr ::
        two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have hltWord : UInt256.lt lotFeed chost = ⟨1⟩ := ult_one hlt
  have rd7913 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov)]
  rw [hltWord] at rd7913
  have rd8116Pre := evm_run rd7913 with [
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8116⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8116 := rd8116Pre.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (clipperRedoJumpDest8116 v hpatch)
    (by evm_ov)
  exact ⟨_, _, evm_run rd8116 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]⟩

theorem RD.clipperRedoLotFeedAtLeastChostToPayout {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {lotFeed chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7910⟩
      (lotFeed :: chost :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hle : chost.toNat ≤ lotFeed.toNat)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7919⟩
      (chost :: coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k' C' := by
  have hltWord : UInt256.lt lotFeed chost = ⟨0⟩ := ult_zero hle
  have rd7913 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov)]
  rw [hltWord] at rd7913
  have rd7919Pre := evm_run rd7913 with [
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8116⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by simpa using
    rd7919Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)⟩

theorem RD.clipperRedoPayoutToWmul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7919⟩
      (chost :: coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8238⟩
      (chip :: tab :: ⟨6235⟩ :: tip :: ⟨7932⟩ :: chost :: coin :: chip :: tip ::
        feedPrice :: lot :: tab :: done :: topNew :: tic :: usr :: two :: kpr :: id :: ret ::
        sel :: R)
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw push2 ⟨7932⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6235⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8238⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperRedoJumpDest8238 v hpatch) (by evm_ov)]⟩

theorem RD.clipperRedoPayoutWmulOverflowReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chip tab tip : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8238⟩
      (chip :: tab :: ⟨6235⟩ :: tip :: R) mem aw o acc k C)
    (hover : UInt256.size ≤ chip.toNat * tab.toNat)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  exact
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperWmulRoutineRevert
      v hpatch rd hover (by omega)

theorem RD.clipperRedoPayoutWmulToCheckedAdd {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chip tab tip keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8238⟩
      (chip :: tab :: ⟨6235⟩ :: tip :: ⟨7932⟩ :: keep :: R) mem aw o acc k C)
    (hmul : chip.toNat * tab.toNat < UInt256.size)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9258⟩
      (UInt256.div (UInt256.mul chip tab) ⟨1000000000000000000⟩ :: tip ::
        ⟨7932⟩ :: keep :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd6235⟩ :=
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperWmulRoutine
      v hpatch rd hmul (clipperRedoJumpDest6235 v hpatch)
        (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd6235 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9258⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperRedoJumpDest9258 v hpatch) (by evm_ov)]⟩

theorem RD.clipperRedoPayoutAddOverflowReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chipCoin tip ret : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9258⟩ (chipCoin :: tip :: ret :: R) mem aw o acc k C)
    (hover : UInt256.size ≤ tip.toNat + chipCoin.toNat)
    (hov : R.length + 15 ≤ 1024) :
    RDrev code g s0 := by
  have haddNat : (tip + chipCoin).toNat = tip.toNat + chipCoin.toNat - UInt256.size := by
    rw [uadd_toNat, Nat.mod_eq_sub_mod hover]
    have hlt : tip.toNat + chipCoin.toNat < UInt256.size + UInt256.size := by
      have htip : tip.toNat < UInt256.size := tip.val.isLt
      have hchip : chipCoin.toNat < UInt256.size := chipCoin.val.isLt
      omega
    rw [Nat.mod_eq_of_lt]
    omega
  have hlt : UInt256.lt (tip + chipCoin) tip = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hchip : chipCoin.toNat < UInt256.size := chipCoin.val.isLt
    omega
  have rd9270 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov)]
  rw [hlt] at rd9270
  have rd9274 := evm_run rd9270 with [
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8722⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rd9274
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by evm_ov)

theorem RD.clipperRedoPayoutAddSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chipCoin tip keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9258⟩
      (chipCoin :: tip :: ⟨7932⟩ :: keep :: R) mem aw o acc k C)
    (hfit : tip.toNat + chipCoin.toNat < UInt256.size)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨7932⟩ ((tip + chipCoin) :: keep :: R) mem aw o acc k' C' := by
  exact RD.solcCheckedAddSuccess rd
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | clipper_runtime_decode)
    hfit (clipperRedoJumpDest7932 v hpatch) (clipperJumpDest8722 v hpatch)
      (by simp only [List.length_cons]; omega)

end Benchmarks.Dss.Clipper
