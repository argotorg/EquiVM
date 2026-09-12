import Benchmarks.Dss.Clipper.KickFeedPricePar
import Benchmarks.Dss.Clipper.RedoSuckEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

private theorem clipperKickTailJumpDest
    (pc : Nat) (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hpc : pc ∈ [6061, 6069, 6149, 6216, 6235, 6240, 6369, 6389, 6394]) :
    (D_J code 0).contains (UInt256.ofNat pc) = true := by
  simp at hpc
  rcases hpc with hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc | hpc <;>
    subst pc <;>
    apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch <;>
    unfold patches patchesFrom offsets immValues <;>
    simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons] <;>
    cases hIlk : wordBytes? v.ilk <;> simp [hIlk] <;> native_decide

theorem clipperKickJumpDest6061 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6061⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6061 v hpatch (by simp)

theorem clipperKickJumpDest6069 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6069⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6069 v hpatch (by simp)

theorem clipperKickJumpDest6149 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6149⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6149 v hpatch (by simp)

theorem clipperKickJumpDest6216 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6216⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6216 v hpatch (by simp)

theorem clipperKickJumpDest6235 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6235⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6235 v hpatch (by simp)

theorem clipperKickJumpDest6240 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6240⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6240 v hpatch (by simp)

theorem clipperKickJumpDest6369 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6369⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6369 v hpatch (by simp)

theorem clipperKickJumpDest6389 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6389⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6389 v hpatch (by simp)

theorem clipperKickJumpDest6394 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6394⟩ : UInt256) = true :=
  clipperKickTailJumpDest 6394 v hpatch (by simp)

abbrev clipperKickTopSlot (id : UInt256) : UInt256 :=
  solcMappingSlot ⟨12⟩ id + ⟨4⟩

abbrev clipperKickTopMap (σ : AccountMap) (ee : ExecutionEnv)
    (id top : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (clipperKickTopSlot id) top

abbrev clipperKickTipWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (solcSlotWord σ ee ⟨8⟩)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)

abbrev clipperKickChipWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ ee ⟨8⟩) ⟨18446744073709551615⟩

theorem RD.clipperKickGetFeedPriceToRmul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {feedPrice id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6061⟩
      (feedPrice :: ⟨6069⟩ :: ⟨0⟩ :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9233⟩
      (solcSlotWord acc.2 ee ⟨5⟩ :: feedPrice :: ⟨6069⟩ :: ⟨0⟩ :: ⟨1⟩ ::
        id :: kpr :: usr :: lot :: tab :: ⟨476⟩ :: sel :: R)
      mem aw o acc k' C' := by
  have rdBufPre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨5⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdBuf⟩ := rdBufPre.sload (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, by simpa [solcSlotWord] using evm_run rdBuf with [
    raw push2 ⟨9233⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode)
      (by
        apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9400) hpatch
        unfold patches patchesFrom offsets immValues
        simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
        cases hIlk : wordBytes? v.ilk <;> simp [hIlk] <;> native_decide)
      (by evm_ov)]⟩

theorem RD.clipperKickRmulOverflowReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {buf feedPrice keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9233⟩
      (buf :: feedPrice :: ⟨6069⟩ :: keep :: R) mem aw o acc k C)
    (hover : UInt256.size ≤ buf.toNat * feedPrice.toNat)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 :=
  _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRmulRoutineRevert
    v hpatch rd hover (by omega)

theorem RD.clipperKickRmulSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {buf feedPrice keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9233⟩
      (buf :: feedPrice :: ⟨6069⟩ :: keep :: R) mem aw o acc k C)
    (hmul : buf.toNat * feedPrice.toNat < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6069⟩
      (UInt256.div (UInt256.mul buf feedPrice) clipperRayWord :: keep :: R)
      mem aw o acc k' C' :=
  _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperRmulRoutine
    v hpatch rd hmul (clipperKickJumpDest6069 v hpatch) (by omega)

theorem RD.clipperKickTopZeroReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {top id kpr usr lot tab sel : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6069⟩
      (top :: ⟨0⟩ :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 6) o acc k C)
    (hzero : top = ⟨0⟩)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 30 ≤ 1024) : RDrev code g s0 := by
  have hgt : UInt256.gt top ⟨0⟩ = ⟨0⟩ := by subst top; native_decide
  have rdGuard := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6149⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rdGuard
  have rdFallthrough := rdGuard.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  have hmload64 := mloadFreePtrValue
    (mem := mem) (aw := UInt256.ofNat 6) (by rw [hmem]; omega) (by decide) hread64
  have rdMload := evm_run rdFallthrough with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rdSelector := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rdPrefix := evm_run rdSelector with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨22⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨22⟩ mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov)]
  let rawWord : UInt256 :=
    ⟨25226120211836879428703562217324731842797597832602469⟩
  have rdRaw := rdPrefix.pushConst rawWord (width := 22) (op := .PUSH22)
    (by decide) (by simpa [rawWord] using
      (show decode code ⟨6107⟩ = some (.PUSH22, some (rawWord, 22)) by
        clipper_runtime_decode)) (by evm_ov)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨80⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨22⟩ (UInt256.shiftLeft rawWord ⟨80⟩) mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (clipperKickErrorStringMem3_mload64 ⟨22⟩
        (UInt256.shiftLeft rawWord ⟨80⟩) hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1500000 in
theorem RD.clipperKickTopPositiveToIncentive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {top id kpr usr lot tab sel : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6069⟩
      (top :: ⟨0⟩ :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 6) o (cA, σ) k C)
    (htop : 0 < top.toNat) (hperm : ee.perm = true)
    (hmem : mem.size = 192) (hov : R.length + 50 ≤ 1024) :
    let σTop := clipperKickTopMap σ ee id top
    ∃ k' C', RD code ee g s0 ⟨6203⟩
      (⟨0⟩ :: clipperKickChipWord σTop ee :: clipperKickTipWord σTop ee :: top ::
        ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ :: sel :: R)
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 6) o (cA, σTop) k' C' := by
  intro σTop
  have hgt : UInt256.gt top ⟨0⟩ = ⟨1⟩ := ugt_one (by simpa using htop)
  have rdGuard := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6149⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rdGuard
  have rd6149 := rdGuard.jumpiT (by clipper_runtime_decode) (by decide)
    (clipperKickJumpDest6149 v hpatch) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ id :=
    twoWordHashMem_solcMappingSlot_of_ge (⟨12⟩ : UInt256) id (by rw [hmem]; omega)
  have rdHash := evm_run rd6149 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨12⟩ id) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hslot (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdTop⟩ := rdHash.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rdPackedPre := evm_run rdTop with [
    raw push1 ⟨8⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdPacked⟩ := rdPackedPre.sload (by clipper_runtime_decode) (by evm_ov)
  have rdTip := evm_run rdPacked with [
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
  have rdMask := rdTip.pushConst ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd6203 := evm_run rdMask with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σTop, clipperKickTopMap, clipperKickTopSlot, clipperKickTipWord,
      clipperKickChipWord, solcSlotWord, u256_add_comm] using rd6203⟩

end Benchmarks.Dss.Clipper
