import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatioFull

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolInitializePatchDisjointTimestamp {v : PoolImmutables}
    {pc : UInt256} (hlo : 11291 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolInitializePatchPreservesJumpDest10809 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10809⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11303 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11303⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest17514 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨17514⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest10817 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10817⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest857 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨857⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolInitializePatchDisjointObservationStore {v : PoolImmutables}
    {pc : UInt256} (hlo : 17514 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolJumpDestPatched10809 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10809⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest10809

theorem uniswapV3PoolJumpDestPatched11303 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11303⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11303

theorem uniswapV3PoolJumpDestPatched17514 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨17514⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest17514

theorem uniswapV3PoolJumpDestPatched10817 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10817⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest10817

theorem uniswapV3PoolInitializeJumpDestPatched857 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨857⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest857

def initializeObservationTimestampWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨4294967295⟩ (UInt256.ofNat ee.header.timestamp)

def initializeObservationSstoreWord (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨1⟩ ⟨248⟩)
    (UInt256.land ⟨4294967295⟩
      (UInt256.lor (initializeObservationTimestampWord ee)
        (UInt256.land (UInt256.lnot ⟨4294967295⟩) (codeOwnerStorageWord ee σ ⟨8⟩))))

noncomputable def initializeObservationStoreMem0 : ByteArray :=
  writeWord solcFreePtrMem 64 (UInt256.ofNat 256)

noncomputable def initializeObservationStoreMem1 (ee : ExecutionEnv) : ByteArray :=
  writeWord initializeObservationStoreMem0 128 (initializeObservationTimestampWord ee)

noncomputable def initializeObservationStoreMem2 (ee : ExecutionEnv) : ByteArray :=
  writeWord (initializeObservationStoreMem1 ee) 160 ⟨0⟩

noncomputable def initializeObservationStoreMem3 (ee : ExecutionEnv) : ByteArray :=
  writeWord (initializeObservationStoreMem2 ee) 192 ⟨0⟩

noncomputable def initializeObservationStoreMem (ee : ExecutionEnv) : ByteArray :=
  writeWord (initializeObservationStoreMem3 ee) 224 ⟨1⟩

theorem initializeObservationStoreMem_size (ee : ExecutionEnv) :
    (initializeObservationStoreMem ee).size = 256 := by
  unfold initializeObservationStoreMem initializeObservationStoreMem3 initializeObservationStoreMem2
    initializeObservationStoreMem1 initializeObservationStoreMem0
  change (writeCascade solcFreePtrMem
    [(64, UInt256.ofNat 256), (128, initializeObservationTimestampWord ee),
      (160, (⟨0⟩ : UInt256)), (192, (⟨0⟩ : UInt256)), (224, (⟨1⟩ : UInt256))]).size =
    256
  exact writeCascade_size_of_base solcFreePtrMem _ solcFreePtrMem_size
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem initializeObservationStoreMem_read64 (ee : ExecutionEnv) :
    (initializeObservationStoreMem ee).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 256) := by
  unfold initializeObservationStoreMem initializeObservationStoreMem3 initializeObservationStoreMem2
    initializeObservationStoreMem1 initializeObservationStoreMem0
  change ((writeCascade solcFreePtrMem
    [(64, UInt256.ofNat 256), (128, initializeObservationTimestampWord ee),
      (160, (⟨0⟩ : UInt256)), (192, (⟨0⟩ : UInt256)), (224, (⟨1⟩ : UInt256))]).readWithPadding
        64 32 = UInt256.toByteArray (UInt256.ofNat 256))
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem (base := 96) (off := 64)
    (UInt256.ofNat 256)
    [(128, initializeObservationTimestampWord ee), (160, (⟨0⟩ : UInt256)),
      (192, (⟨0⟩ : UInt256)), (224, (⟨1⟩ : UInt256))]
    solcFreePtrMem_size (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)

theorem initializeObservationStoreMem_mload64 (ee : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (initializeObservationStoreMem ee).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((initializeObservationStoreMem ee).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.ofNat 256 := by
  exact mloadWordValue_of_readWithPadding
    (by rw [initializeObservationStoreMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using initializeObservationStoreMem_read64 ee)

def initializeSlot0SqrtEventWord (sqrt : UInt256) : UInt256 :=
  UInt256.land sqrt (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩)

def initializeSlot0TickEventWord (tick : UInt256) : UInt256 :=
  UInt256.signextend ⟨2⟩ tick

def initializeSlot0ObservationCardinalityEventWord : UInt256 :=
  UInt256.land ⟨65535⟩ ⟨1⟩

def initializeSlot0ObservationCardinalityNextEventWord : UInt256 :=
  UInt256.land ⟨1⟩ ⟨65535⟩

abbrev initializeSlot0TickClearMask : UInt256 :=
  ⟨115792089237210883131926947750643844047320047785756073890994934722613756297215⟩

abbrev initializeSlot0UnlockedClearMask : UInt256 :=
  ⟨115339783290479275825761448283253582990243601239149377756565007982906442776575⟩

abbrev initializeSlot0EventTopic : UInt256 :=
  ⟨68927134888976591364352437975413714156611039632452992126063371163455731879061⟩

abbrev initializeSlot0SstoreWord
    (σ : AccountMap) (ee : ExecutionEnv) (sqrt tick : UInt256) : UInt256 :=
  let slotWithSqrt :=
    UInt256.lor
      (initializeSlot0SqrtEventWord sqrt)
      (UInt256.land (codeOwnerStorageWord ee σ ⟨0⟩) (UInt256.lnot solcAddrMask))
  let tickShifted :=
    UInt256.mul
      (UInt256.land (UInt256.signextend ⟨2⟩ (initializeSlot0TickEventWord tick))
        ⟨16777215⟩)
      (UInt256.shiftLeft ⟨1⟩ ⟨160⟩)
  let slotWithTick :=
    UInt256.lor
      tickShifted
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨16777215⟩ ⟨160⟩))
        slotWithSqrt)
  let slotWithCardinality :=
    UInt256.lor
      (UInt256.mul
        initializeSlot0ObservationCardinalityEventWord
        (UInt256.shiftLeft ⟨1⟩ ⟨200⟩))
      (UInt256.land initializeSlot0TickClearMask slotWithTick)
  let slotWithCardinalityNext :=
    UInt256.lor
      (UInt256.mul
        initializeSlot0ObservationCardinalityNextEventWord
        (UInt256.shiftLeft ⟨1⟩ ⟨216⟩))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ ⟨216⟩))
        slotWithCardinality)
  UInt256.lor
    (UInt256.land initializeSlot0UnlockedClearMask slotWithCardinalityNext)
    (UInt256.shiftLeft ⟨1⟩ ⟨240⟩)

noncomputable def initializeSlot0EventMem0 (ee : ExecutionEnv) : ByteArray :=
  writeWord (initializeObservationStoreMem ee) 64 (UInt256.ofNat 480)

noncomputable def initializeSlot0EventMem1 (ee : ExecutionEnv) (sqrt : UInt256) :
    ByteArray :=
  writeWord (initializeSlot0EventMem0 ee) 256 (initializeSlot0SqrtEventWord sqrt)

noncomputable def initializeSlot0EventMem2
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem1 ee sqrt) 288 (initializeSlot0TickEventWord tick)

noncomputable def initializeSlot0EventMem3
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem2 ee sqrt tick) 320 ⟨0⟩

noncomputable def initializeSlot0EventMem4
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem3 ee sqrt tick) 352
    initializeSlot0ObservationCardinalityEventWord

noncomputable def initializeSlot0EventMem5
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem4 ee sqrt tick) 384
    initializeSlot0ObservationCardinalityNextEventWord

noncomputable def initializeSlot0EventMem6
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem5 ee sqrt tick) 416 ⟨0⟩

noncomputable def initializeSlot0EventMem
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem6 ee sqrt tick) 448 ⟨1⟩

noncomputable def initializeSlot0LogMem0
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0EventMem ee sqrt tick) 480 (initializeSlot0SqrtEventWord sqrt)

noncomputable def initializeSlot0LogMem
    (ee : ExecutionEnv) (sqrt tick : UInt256) : ByteArray :=
  writeWord (initializeSlot0LogMem0 ee sqrt tick) 512 (initializeSlot0TickEventWord tick)

theorem initializeSlot0EventMem_size (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (initializeSlot0EventMem ee sqrt tick).size = 480 := by
  unfold initializeSlot0EventMem initializeSlot0EventMem6 initializeSlot0EventMem5
    initializeSlot0EventMem4 initializeSlot0EventMem3 initializeSlot0EventMem2
    initializeSlot0EventMem1 initializeSlot0EventMem0
  change (writeCascade (initializeObservationStoreMem ee)
    [(64, UInt256.ofNat 480), (256, initializeSlot0SqrtEventWord sqrt),
      (288, initializeSlot0TickEventWord tick), (320, (⟨0⟩ : UInt256)),
      (352, initializeSlot0ObservationCardinalityEventWord),
      (384, initializeSlot0ObservationCardinalityNextEventWord), (416, (⟨0⟩ : UInt256)),
      (448, (⟨1⟩ : UInt256))]).size = 480
  exact writeCascade_size_of_base (initializeObservationStoreMem ee) _
    (initializeObservationStoreMem_size ee)
    (by
      norm_num [WriteGapsOk])
    (by norm_num [writeCascadeSize])

theorem initializeSlot0EventMem_read64 (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (initializeSlot0EventMem ee sqrt tick).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 480) := by
  unfold initializeSlot0EventMem initializeSlot0EventMem6 initializeSlot0EventMem5
    initializeSlot0EventMem4 initializeSlot0EventMem3 initializeSlot0EventMem2
    initializeSlot0EventMem1 initializeSlot0EventMem0
  change ((writeCascade (initializeObservationStoreMem ee)
    [(64, UInt256.ofNat 480), (256, initializeSlot0SqrtEventWord sqrt),
      (288, initializeSlot0TickEventWord tick), (320, (⟨0⟩ : UInt256)),
      (352, initializeSlot0ObservationCardinalityEventWord),
      (384, initializeSlot0ObservationCardinalityNextEventWord), (416, (⟨0⟩ : UInt256)),
      (448, (⟨1⟩ : UInt256))]).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat 480))
  exact writeCascade_read_word_of_head_of_base (initializeObservationStoreMem ee)
    (base := 256) (off := 64) (UInt256.ofNat 480)
    [(256, initializeSlot0SqrtEventWord sqrt), (288, initializeSlot0TickEventWord tick),
      (320, (⟨0⟩ : UInt256)), (352, initializeSlot0ObservationCardinalityEventWord),
      (384, initializeSlot0ObservationCardinalityNextEventWord), (416, (⟨0⟩ : UInt256)),
      (448, (⟨1⟩ : UInt256))]
    (initializeObservationStoreMem_size ee) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem initializeSlot0EventMem_mload64 (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (initializeSlot0EventMem ee sqrt tick).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((initializeSlot0EventMem ee sqrt tick).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.ofNat 480 := by
  exact mloadWordValue_of_readWithPadding
    (by rw [initializeSlot0EventMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using initializeSlot0EventMem_read64 ee sqrt tick)

theorem initializeSlot0LogMem_size (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (initializeSlot0LogMem ee sqrt tick).size = 544 := by
  unfold initializeSlot0LogMem initializeSlot0LogMem0
  change (writeCascade (initializeSlot0EventMem ee sqrt tick)
    [(480, initializeSlot0SqrtEventWord sqrt),
      (512, initializeSlot0TickEventWord tick)]).size = 544
  exact writeCascade_size_of_base (initializeSlot0EventMem ee sqrt tick) _
    (initializeSlot0EventMem_size ee sqrt tick)
    (by
      norm_num [WriteGapsOk])
    (by norm_num [writeCascadeSize])

theorem initializeSlot0LogMem_read64 (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (initializeSlot0LogMem ee sqrt tick).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 480) := by
  unfold initializeSlot0LogMem initializeSlot0LogMem0
  change ((writeCascade (initializeSlot0EventMem ee sqrt tick)
    [(480, initializeSlot0SqrtEventWord sqrt),
      (512, initializeSlot0TickEventWord tick)]).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat 480))
  rw [writeCascade_read_preserved_of_base (initializeSlot0EventMem ee sqrt tick)
    [(480, initializeSlot0SqrtEventWord sqrt), (512, initializeSlot0TickEventWord tick)]
    (base := 480) (read := 64) (initializeSlot0EventMem_size ee sqrt tick)]
  · exact initializeSlot0EventMem_read64 ee sqrt tick
  · norm_num [WindowDisjointFromWrites]

theorem initializeSlot0LogMem_mload64 (ee : ExecutionEnv) (sqrt tick : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (initializeSlot0LogMem ee sqrt tick).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((initializeSlot0LogMem ee sqrt tick).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.ofNat 480 := by
  exact mloadWordValue_of_readWithPadding
    (by rw [initializeSlot0LogMem_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using initializeSlot0LogMem_read64 ee sqrt tick)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeReachObservationStore {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick sqrt ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10793⟩ (tick :: ⟨0⟩ :: sqrt :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨17514⟩
      (UInt256.ofNat ee.header.timestamp :: ⟨8⟩ :: ⟨10817⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        tick :: sqrt :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecodeBody {pc : UInt256} (hlo : 10597 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hdecodeTimestamp {pc : UInt256} (hlo : 11291 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointTimestamp hlo hhi)]
  have hd10793 : decode code ⟨10793⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10794 : decode code ⟨10794⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10795 : decode code ⟨10795⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10796 : decode code ⟨10796⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10798 : decode code ⟨10798⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10799 : decode code ⟨10799⟩ = some (.Push .PUSH2, some (⟨10817⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10802 : decode code ⟨10802⟩ = some (.Push .PUSH2, some (⟨10809⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10805 : decode code ⟨10805⟩ = some (.Push .PUSH2, some (⟨11303⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10808 : decode code ⟨10808⟩ = some (.JUMP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10809 : decode code ⟨10809⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10810 : decode code ⟨10810⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10812 : decode code ⟨10812⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10813 : decode code ⟨10813⟩ = some (.Push .PUSH2, some (⟨17514⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd10816 : decode code ⟨10816⟩ = some (.JUMP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd11303 : decode code ⟨11303⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeTimestamp (by native_decide) (by native_decide)]
    native_decide
  have hd11304 : decode code ⟨11304⟩ = some (.TIMESTAMP, .none) := by
    rw [hdecodeTimestamp (by native_decide) (by native_decide)]
    native_decide
  have hd11305 : decode code ⟨11305⟩ = some (.SWAP1, .none) := by
    rw [hdecodeTimestamp (by native_decide) (by native_decide)]
    native_decide
  have hd11306 : decode code ⟨11306⟩ = some (.JUMP, .none) := by
    rw [hdecodeTimestamp (by native_decide) (by native_decide)]
    native_decide
  have rd10808 := evm_run h with [
    raw jumpdest hd10793 (by evm_ov),
    raw swap1 hd10794 (by evm_ov),
    raw pop hd10795 (by evm_ov),
    raw push1 ⟨0⟩ hd10796 (by evm_ov),
    raw dup1 hd10798 (by evm_ov),
    raw push2 ⟨10817⟩ hd10799 (by evm_ov),
    raw push2 ⟨10809⟩ hd10802 (by evm_ov),
    raw push2 ⟨11303⟩ hd10805 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd11303 := rd10808.jump hd10808 (uniswapV3PoolJumpDestPatched11303 hpatch)
    (by evm_ov)
  have rd11306 := evm_run rd11303 with [
    raw jumpdest hd11303 (by evm_ov),
    raw timestamp hd11304 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd11305 (by evm_ov)]
  have rd10809 := rd11306.jump hd11306 (uniswapV3PoolJumpDestPatched10809 hpatch)
    (by evm_ov)
  have rd10816 := evm_run rd10809 with [
    raw jumpdest hd10809 (by evm_ov),
    raw push1 ⟨8⟩ hd10810 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd10812 (by evm_ov),
    raw push2 ⟨17514⟩ hd10813 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  exact ⟨_, _, rd10816.jump hd10816 (uniswapV3PoolJumpDestPatched17514 hpatch) (by evm_ov)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeObservationStore {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick sqrt ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨17514⟩
      (UInt256.ofNat ee.header.timestamp :: ⟨8⟩ :: ⟨10817⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        tick :: sqrt :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10817⟩
      (⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ret :: R)
      (initializeObservationStoreMem ee) (UInt256.ofNat 8) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨8⟩ (initializeObservationSstoreWord σ ee))
      k' C' := by
  have hdecode {pc : UInt256} (hlo : 17514 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointObservationStore hlo hhi)]
  have hd17514 : decode code ⟨17514⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17515 : decode code ⟨17515⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17517 : decode code ⟨17517⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17518 : decode code ⟨17518⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17519 : decode code ⟨17519⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17521 : decode code ⟨17521⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17522 : decode code ⟨17522⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17523 : decode code ⟨17523⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17524 : decode code ⟨17524⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17525 : decode code ⟨17525⟩ =
      some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17530 : decode code ⟨17530⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17531 : decode code ⟨17531⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17532 : decode code ⟨17532⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17533 : decode code ⟨17533⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17534 : decode code ⟨17534⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17535 : decode code ⟨17535⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17536 : decode code ⟨17536⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17538 : decode code ⟨17538⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17540 : decode code ⟨17540⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17541 : decode code ⟨17541⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17542 : decode code ⟨17542⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17543 : decode code ⟨17543⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17544 : decode code ⟨17544⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17545 : decode code ⟨17545⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17546 : decode code ⟨17546⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17547 : decode code ⟨17547⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17548 : decode code ⟨17548⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17549 : decode code ⟨17549⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17550 : decode code ⟨17550⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17551 : decode code ⟨17551⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17552 : decode code ⟨17552⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17554 : decode code ⟨17554⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17556 : decode code ⟨17556⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17557 : decode code ⟨17557⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17558 : decode code ⟨17558⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17559 : decode code ⟨17559⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17560 : decode code ⟨17560⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17561 : decode code ⟨17561⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17562 : decode code ⟨17562⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17563 : decode code ⟨17563⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17564 : decode code ⟨17564⟩ =
      some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17569 : decode code ⟨17569⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17570 : decode code ⟨17570⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17571 : decode code ⟨17571⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17572 : decode code ⟨17572⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17573 : decode code ⟨17573⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17574 : decode code ⟨17574⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17575 : decode code ⟨17575⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17576 : decode code ⟨17576⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17577 : decode code ⟨17577⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17579 : decode code ⟨17579⟩ = some (.Push .PUSH1, some (⟨248⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17581 : decode code ⟨17581⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17582 : decode code ⟨17582⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17583 : decode code ⟨17583⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17584 : decode code ⟨17584⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17585 : decode code ⟨17585⟩ = some (.SSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17586 : decode code ⟨17586⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17587 : decode code ⟨17587⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17588 : decode code ⟨17588⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd17589 : decode code ⟨17589⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd17518 := evm_run h with [
    raw jumpdest hd17514 (by evm_ov),
    raw push1 ⟨64⟩ hd17515 (by evm_ov),
    raw dup1 hd17517 (by evm_ov)]
  have rd17519 := evm_run rd17518 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd17518 mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov)]
  have rd17525 := evm_run rd17519 with [
    raw push1 ⟨128⟩ hd17519 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd17521 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw add hd17522 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup3 hd17523 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mstore 0 initializeObservationStoreMem0 (UInt256.ofNat 3)
      hd17524 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd17535 := evm_run rd17525 with [
    raw push4 ⟨4294967295⟩ hd17525 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd17530 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup4 hd17531 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd17532 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd17533 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup3 hd17534 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd17536 := evm_run rd17535 with [
    raw mstore 6 (initializeObservationStoreMem1 ee) (UInt256.ofNat 5)
      hd17535 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd17545 := evm_run rd17536 with [
    raw push1 ⟨0⟩ hd17536 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨32⟩ hd17538 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup4 hd17540 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw add hd17541 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd17542 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd17543 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mstore 3 (initializeObservationStoreMem2 ee) (UInt256.ofNat 6)
      hd17544 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd17552 := evm_run rd17545 with [
    raw swap3 hd17545 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup3 hd17546 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw add hd17547 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd17548 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd17549 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd17550 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mstore 3 (initializeObservationStoreMem3 ee) (UInt256.ofNat 7)
      hd17551 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd17562 := evm_run rd17552 with [
    raw push1 ⟨1⟩ hd17552 (by evm_ov),
    raw push1 ⟨96⟩ hd17554 (by evm_ov),
    raw swap1 hd17556 (by evm_ov),
    raw swap2 hd17557 (by evm_ov),
    raw add hd17558 (by evm_ov),
    raw dup2 hd17559 (by evm_ov),
    raw swap1 hd17560 (by evm_ov),
    raw mstore 3 (initializeObservationStoreMem ee) (UInt256.ofNat 8)
      hd17561 mem_cost rfl (by native_decide) (by evm_ov),
    raw dup4 hd17562 (by evm_ov)]
  obtain ⟨_, _, rd17564⟩ := rd17562.sload hd17563 (by evm_ov)
  have rd17585 := evm_run rd17564 with [
    raw push4 ⟨4294967295⟩ hd17564 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd17569 (by evm_ov),
    raw and hd17570 (by evm_ov),
    raw swap1 hd17571 (by evm_ov),
    raw swap2 hd17572 (by evm_ov),
    raw lor hd17573 (by evm_ov),
    raw swap1 hd17574 (by evm_ov),
    raw swap2 hd17575 (by evm_ov),
    raw and hd17576 (by evm_ov),
    raw push1 ⟨1⟩ hd17577 (by evm_ov),
    raw push1 ⟨248⟩ hd17579 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd17581 (by evm_ov),
    raw lor hd17582 (by evm_ov),
    raw swap1 hd17583 (by evm_ov),
    raw swap2 hd17584 (by evm_ov)]
  obtain ⟨_, _, rd17586⟩ := rd17585.sstore hperm hd17585 (by evm_ov)
  have rd17589 := evm_run rd17586 with [
    raw swap1 hd17586 (by evm_ov),
    raw dup2 hd17587 (by evm_ov),
    raw swap1 hd17588 (by evm_ov)]
  have rd10817 := rd17589.jump hd17589 (uniswapV3PoolJumpDestPatched10817 hpatch)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [initializeObservationSstoreWord, initializeObservationTimestampWord,
      codeOwnerStorageWord] using rd10817⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeSlot0EventSetup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick sqrt ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10817⟩
      (⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ret :: R)
      (initializeObservationStoreMem ee) (UInt256.ofNat 8) rdata acc k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10904⟩
      (⟨0⟩ :: initializeSlot0ObservationCardinalityEventWord :: ⟨0⟩ :: ⟨32⟩ ::
        initializeSlot0TickEventWord tick :: ⟨2⟩ :: initializeSlot0SqrtEventWord sqrt ::
          initializeSlot0ObservationCardinalityNextEventWord :: ⟨64⟩ :: ⟨1⟩ :: ⟨1⟩ ::
            ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ret :: R)
      (initializeSlot0EventMem ee sqrt tick) (UInt256.ofNat 15) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hd10817 : decode code ⟨10817⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10818 : decode code ⟨10818⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10820 : decode code ⟨10820⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10821 : decode code ⟨10821⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10822 : decode code ⟨10822⟩ = some (.Push .PUSH1, some (⟨224⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10824 : decode code ⟨10824⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10825 : decode code ⟨10825⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10826 : decode code ⟨10826⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10827 : decode code ⟨10827⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10828 : decode code ⟨10828⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10830 : decode code ⟨10830⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10832 : decode code ⟨10832⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10834 : decode code ⟨10834⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10835 : decode code ⟨10835⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10836 : decode code ⟨10836⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10837 : decode code ⟨10837⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10838 : decode code ⟨10838⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10839 : decode code ⟨10839⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10840 : decode code ⟨10840⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10841 : decode code ⟨10841⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10843 : decode code ⟨10843⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10844 : decode code ⟨10844⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10845 : decode code ⟨10845⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10846 : decode code ⟨10846⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10848 : decode code ⟨10848⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10849 : decode code ⟨10849⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10850 : decode code ⟨10850⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10851 : decode code ⟨10851⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10852 : decode code ⟨10852⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10853 : decode code ⟨10853⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10854 : decode code ⟨10854⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10856 : decode code ⟨10856⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10857 : decode code ⟨10857⟩ = some (.DUP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10858 : decode code ⟨10858⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10859 : decode code ⟨10859⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10860 : decode code ⟨10860⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10861 : decode code ⟨10861⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10862 : decode code ⟨10862⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10865 : decode code ⟨10865⟩ = some (.DUP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10866 : decode code ⟨10866⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10867 : decode code ⟨10867⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10868 : decode code ⟨10868⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10870 : decode code ⟨10870⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10871 : decode code ⟨10871⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10872 : decode code ⟨10872⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10873 : decode code ⟨10873⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10874 : decode code ⟨10874⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10875 : decode code ⟨10875⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10876 : decode code ⟨10876⟩ = some (.DUP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10877 : decode code ⟨10877⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10878 : decode code ⟨10878⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10880 : decode code ⟨10880⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10881 : decode code ⟨10881⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10882 : decode code ⟨10882⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10883 : decode code ⟨10883⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10884 : decode code ⟨10884⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10885 : decode code ⟨10885⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10887 : decode code ⟨10887⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10888 : decode code ⟨10888⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10889 : decode code ⟨10889⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10890 : decode code ⟨10890⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10891 : decode code ⟨10891⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10892 : decode code ⟨10892⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10894 : decode code ⟨10894⟩ = some (.Push .PUSH1, some (⟨192⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10896 : decode code ⟨10896⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10897 : decode code ⟨10897⟩ = some (.SWAP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10898 : decode code ⟨10898⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10899 : decode code ⟨10899⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10900 : decode code ⟨10900⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10901 : decode code ⟨10901⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10902 : decode code ⟨10902⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10903 : decode code ⟨10903⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have rd10821 := evm_run h with [
    raw jumpdest hd10817 (by evm_ov),
    raw push1 ⟨64⟩ hd10818 (by evm_ov),
    raw dup1 hd10820 (by evm_ov)]
  have rd10822 := evm_run rd10821 with [
    raw mload 0 (UInt256.ofNat 256) (UInt256.ofNat 8) hd10821 mem_cost
      (initializeObservationStoreMem_mload64 ee)
      (by native_decide) (by evm_ov)]
  have rd10828 := evm_run rd10822 with [
    raw push1 ⟨224⟩ hd10822 (by evm_ov),
    raw dup2 hd10824 (by evm_ov),
    raw add hd10825 (by evm_ov),
    raw dup3 hd10826 (by evm_ov),
    raw mstore 0 (initializeSlot0EventMem0 ee) (UInt256.ofNat 8)
      hd10827 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10840 := evm_run rd10828 with [
    raw push1 ⟨1⟩ hd10828 (by evm_ov),
    raw push1 ⟨1⟩ hd10830 (by evm_ov),
    raw push1 ⟨160⟩ hd10832 (by evm_ov),
    raw shl hd10834 (by evm_ov),
    raw sub hd10835 (by evm_ov),
    raw dup9 hd10836 (by evm_ov),
    raw and hd10837 (by evm_ov),
    raw dup1 hd10838 (by evm_ov),
    raw dup3 hd10839 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem1 ee sqrt) (UInt256.ofNat 9)
      hd10840 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10845 := evm_run rd10840 with [
    raw push1 ⟨2⟩ hd10841 (by evm_ov),
    raw dup9 hd10843 (by evm_ov),
    raw dup2 hd10844 (by evm_ov)]
  have rd10846 := RD.signextend rd10845 hd10845 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd10853 := evm_run rd10846 with [
    raw push1 ⟨32⟩ hd10846 (by evm_ov),
    raw dup1 hd10848 (by evm_ov),
    raw dup6 hd10849 (by evm_ov),
    raw add hd10850 (by evm_ov),
    raw dup3 hd10851 (by evm_ov),
    raw swap1 hd10852 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem2 ee sqrt tick) (UInt256.ofNat 10)
      hd10853 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10861 := evm_run rd10853 with [
    raw push1 ⟨0⟩ hd10854 (by evm_ov),
    raw dup6 hd10856 (by evm_ov),
    raw dup8 hd10857 (by evm_ov),
    raw add hd10858 (by evm_ov),
    raw dup2 hd10859 (by evm_ov),
    raw swap1 hd10860 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem3 ee sqrt tick) (UInt256.ofNat 11)
      hd10861 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10874 := evm_run rd10861 with [
    raw push2 ⟨65535⟩ hd10862 (by evm_ov),
    raw dup10 hd10865 (by evm_ov),
    raw dup2 hd10866 (by evm_ov),
    raw and hd10867 (by evm_ov),
    raw push1 ⟨96⟩ hd10868 (by evm_ov),
    raw dup9 hd10870 (by evm_ov),
    raw add hd10871 (by evm_ov),
    raw dup2 hd10872 (by evm_ov),
    raw swap1 hd10873 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem4 ee sqrt tick) (UInt256.ofNat 12)
      hd10874 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10884 := evm_run rd10874 with [
    raw swap1 hd10875 (by evm_ov),
    raw dup10 hd10876 (by evm_ov),
    raw and hd10877 (by evm_ov),
    raw push1 ⟨128⟩ hd10878 (by evm_ov),
    raw dup9 hd10880 (by evm_ov),
    raw add hd10881 (by evm_ov),
    raw dup2 hd10882 (by evm_ov),
    raw swap1 hd10883 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem5 ee sqrt tick) (UInt256.ofNat 13)
      hd10884 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10891 := evm_run rd10884 with [
    raw push1 ⟨160⟩ hd10885 (by evm_ov),
    raw dup9 hd10887 (by evm_ov),
    raw add hd10888 (by evm_ov),
    raw dup4 hd10889 (by evm_ov),
    raw swap1 hd10890 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem6 ee sqrt tick) (UInt256.ofNat 14)
      hd10891 mem_cost rfl (by native_decide) (by evm_ov)]
  have rd10898 := evm_run rd10891 with [
    raw push1 ⟨1⟩ hd10892 (by evm_ov),
    raw push1 ⟨192⟩ hd10894 (by evm_ov),
    raw swap1 hd10896 (by evm_ov)]
  have rd10899 := RD.swap9 rd10898 hd10897 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd10904 := evm_run rd10899 with [
    raw add hd10898 (by evm_ov),
    raw swap8 hd10899 (by evm_ov),
    raw swap1 hd10900 (by evm_ov),
    raw swap8 hd10901 (by evm_ov),
    raw mstore 3 (initializeSlot0EventMem ee sqrt tick) (UInt256.ofNat 15)
      hd10902 mem_cost rfl (by native_decide) (by evm_ov),
    raw dup2 hd10903 (by evm_ov)]
  exact ⟨_, _, by
    simpa [initializeSlot0SqrtEventWord, initializeSlot0TickEventWord,
      initializeSlot0ObservationCardinalityEventWord,
      initializeSlot0ObservationCardinalityNextEventWord] using rd10904⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeSlot0Store {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick sqrt ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10904⟩
      (⟨0⟩ :: initializeSlot0ObservationCardinalityEventWord :: ⟨0⟩ :: ⟨32⟩ ::
        initializeSlot0TickEventWord tick :: ⟨2⟩ :: initializeSlot0SqrtEventWord sqrt ::
          initializeSlot0ObservationCardinalityNextEventWord :: ⟨64⟩ :: ⟨1⟩ :: ⟨1⟩ ::
            ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ret :: R)
      (initializeSlot0EventMem ee sqrt tick) (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11075⟩
      (⟨32⟩ :: initializeSlot0SqrtEventWord sqrt :: initializeSlot0TickEventWord tick ::
        ⟨64⟩ :: ⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ret :: R)
      (initializeSlot0EventMem ee sqrt tick) (UInt256.ofNat 15) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩ (initializeSlot0SstoreWord σ ee sqrt tick))
      k' C' := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hd10904 : decode code ⟨10904⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10905 : decode code ⟨10905⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10907 : decode code ⟨10907⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10909 : decode code ⟨10909⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10910 : decode code ⟨10910⟩ = some (.Push .PUSH20, some (solcAddrMask, 20)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10931 : decode code ⟨10931⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10932 : decode code ⟨10932⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10933 : decode code ⟨10933⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10934 : decode code ⟨10934⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10935 : decode code ⟨10935⟩ = some (.DUP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10936 : decode code ⟨10936⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10937 : decode code ⟨10937⟩ = some (.Push .PUSH3, some (⟨16777215⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10941 : decode code ⟨10941⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10943 : decode code ⟨10943⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10944 : decode code ⟨10944⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10945 : decode code ⟨10945⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10946 : decode code ⟨10946⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10948 : decode code ⟨10948⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10950 : decode code ⟨10950⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10951 : decode code ⟨10951⟩ = some (.Push .PUSH3, some (⟨16777215⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10955 : decode code ⟨10955⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10956 : decode code ⟨10956⟩ = some (.DUP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10957 : decode code ⟨10957⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10958 : decode code ⟨10958⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10959 : decode code ⟨10959⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10960 : decode code ⟨10960⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10961 : decode code ⟨10961⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10962 : decode code ⟨10962⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10963 : decode code ⟨10963⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10964 : decode code ⟨10964⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10965 : decode code ⟨10965⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10966 : decode code ⟨10966⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10967 : decode code ⟨10967⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10968 : decode code ⟨10968⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10969 : decode code ⟨10969⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10970 : decode code ⟨10970⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd10971 :
      decode code ⟨10971⟩ =
        some (.Push .PUSH32, some (initializeSlot0TickClearMask, 32)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11004 : decode code ⟨11004⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11005 : decode code ⟨11005⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11007 : decode code ⟨11007⟩ = some (.Push .PUSH1, some (⟨200⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11009 : decode code ⟨11009⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11010 : decode code ⟨11010⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11011 : decode code ⟨11011⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11012 : decode code ⟨11012⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11013 : decode code ⟨11013⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11014 : decode code ⟨11014⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11017 : decode code ⟨11017⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11019 : decode code ⟨11019⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11020 : decode code ⟨11020⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11021 : decode code ⟨11021⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11022 : decode code ⟨11022⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11024 : decode code ⟨11024⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11026 : decode code ⟨11026⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11027 : decode code ⟨11027⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11028 : decode code ⟨11028⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11029 : decode code ⟨11029⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11030 : decode code ⟨11030⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11031 : decode code ⟨11031⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11032 : decode code ⟨11032⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11033 : decode code ⟨11033⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11034 :
      decode code ⟨11034⟩ =
        some (.Push .PUSH32, some (initializeSlot0UnlockedClearMask, 32)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11067 : decode code ⟨11067⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11068 : decode code ⟨11068⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11069 : decode code ⟨11069⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11070 : decode code ⟨11070⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11071 : decode code ⟨11071⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11072 : decode code ⟨11072⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11073 : decode code ⟨11073⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11074 : decode code ⟨11074⟩ = some (.SSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  obtain ⟨_, _, rd10905₀⟩ := h.sload hd10904 (by evm_ov)
  have rd10958 := evm_run rd10905₀ with [
    raw push1 ⟨1⟩ hd10905 (by evm_ov),
    raw push1 ⟨240⟩ hd10907 (by evm_ov),
    raw shl hd10909 (by evm_ov),
    raw pushConst solcAddrMask
      (show Operation.POp.PUSH20 ≠ Operation.POp.PUSH0 by native_decide)
      hd10910
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw not hd10931 (by evm_ov),
    raw swap1 hd10932 (by evm_ov),
    raw swap2 hd10933 (by evm_ov),
    raw and hd10934 (by evm_ov),
    raw dup8 hd10935 (by evm_ov),
    raw lor hd10936 (by evm_ov),
    raw pushConst ⟨16777215⟩
      (show Operation.POp.PUSH3 ≠ Operation.POp.PUSH0 by native_decide)
      hd10937
      (by evm_ov),
    raw push1 ⟨160⟩ hd10941 (by evm_ov),
    raw shl hd10943 (by evm_ov),
    raw not hd10944 (by evm_ov),
    raw and hd10945 (by evm_ov),
    raw push1 ⟨1⟩ hd10946 (by evm_ov),
    raw push1 ⟨160⟩ hd10948 (by evm_ov),
    raw shl hd10950 (by evm_ov),
    raw pushConst ⟨16777215⟩
      (show Operation.POp.PUSH3 ≠ Operation.POp.PUSH0 by native_decide)
      hd10951
      (by evm_ov),
    raw swap8 hd10955 (by evm_ov),
    raw dup8 hd10956 (by evm_ov),
    raw swap1 hd10957 (by evm_ov)]
  have rd10959 := RD.signextend rd10958 hd10958 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd11074 := evm_run rd10959 with [
    raw swap8 hd10959 (by evm_ov),
    raw swap1 hd10960 (by evm_ov),
    raw swap8 hd10961 (by evm_ov),
    raw and hd10962 (by evm_ov),
    raw swap7 hd10963 (by evm_ov),
    raw swap1 hd10964 (by evm_ov),
    raw swap7 hd10965 (by evm_ov),
    raw mul hd10966 (by evm_ov),
    raw swap6 hd10967 (by evm_ov),
    raw swap1 hd10968 (by evm_ov),
    raw swap6 hd10969 (by evm_ov),
    raw lor hd10970 (by evm_ov),
    raw pushConst initializeSlot0TickClearMask
      (show Operation.POp.PUSH32 ≠ Operation.POp.PUSH0 by native_decide)
      hd10971
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw and hd11004 (by evm_ov),
    raw push1 ⟨1⟩ hd11005 (by evm_ov),
    raw push1 ⟨200⟩ hd11007 (by evm_ov),
    raw shl hd11009 (by evm_ov),
    raw swap1 hd11010 (by evm_ov),
    raw swap2 hd11011 (by evm_ov),
    raw mul hd11012 (by evm_ov),
    raw lor hd11013 (by evm_ov),
    raw push2 ⟨65535⟩ hd11014 (by evm_ov),
    raw push1 ⟨216⟩ hd11017 (by evm_ov),
    raw shl hd11019 (by evm_ov),
    raw not hd11020 (by evm_ov),
    raw and hd11021 (by evm_ov),
    raw push1 ⟨1⟩ hd11022 (by evm_ov),
    raw push1 ⟨216⟩ hd11024 (by evm_ov),
    raw shl hd11026 (by evm_ov),
    raw swap1 hd11027 (by evm_ov),
    raw swap7 hd11028 (by evm_ov),
    raw mul hd11029 (by evm_ov),
    raw swap6 hd11030 (by evm_ov),
    raw swap1 hd11031 (by evm_ov),
    raw swap6 hd11032 (by evm_ov),
    raw lor hd11033 (by evm_ov),
    raw pushConst initializeSlot0UnlockedClearMask
      (show Operation.POp.PUSH32 ≠ Operation.POp.PUSH0 by native_decide)
      hd11034
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw and hd11067 (by evm_ov),
    raw swap3 hd11068 (by evm_ov),
    raw swap1 hd11069 (by evm_ov),
    raw swap3 hd11070 (by evm_ov),
    raw lor hd11071 (by evm_ov),
    raw swap1 hd11072 (by evm_ov),
    raw swap4 hd11073 (by evm_ov)]
  obtain ⟨_, _, rd11075⟩ := rd11074.sstore hperm hd11074 (by evm_ov)
  norm_num at rd11075
  exact ⟨_, _, by
    simpa [initializeSlot0SstoreWord, initializeSlot0SqrtEventWord,
      initializeSlot0TickEventWord, initializeSlot0ObservationCardinalityEventWord,
      initializeSlot0ObservationCardinalityNextEventWord, codeOwnerStorageWord] using rd11075⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolInitializeSlot0LogAndReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick sqrt : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11075⟩
      (⟨32⟩ :: initializeSlot0SqrtEventWord sqrt :: initializeSlot0TickEventWord tick ::
        ⟨64⟩ :: ⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: tick :: sqrt :: ⟨857⟩ :: R)
      (initializeSlot0EventMem ee sqrt tick) (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 16 ≤ 1024) :
    RDret code g s0 (cA, σ) ByteArray.empty := by
  have hdecode {pc : UInt256} (hlo : 10597 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointBody hlo hhi)]
  have hd11075 : decode code ⟨11075⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11076 : decode code ⟨11076⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11077 : decode code ⟨11077⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11078 : decode code ⟨11078⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11079 : decode code ⟨11079⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11080 : decode code ⟨11080⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11081 : decode code ⟨11081⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11082 : decode code ⟨11082⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11083 : decode code ⟨11083⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11084 : decode code ⟨11084⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11085 : decode code ⟨11085⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11086 : decode code ⟨11086⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11087 : decode code ⟨11087⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11088 : decode code ⟨11088⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11089 : decode code ⟨11089⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11090 : decode code ⟨11090⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11091 : decode code ⟨11091⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11092 : decode code ⟨11092⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11093 : decode code ⟨11093⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11094 :
      decode code ⟨11094⟩ =
        some (.Push .PUSH32, some (initializeSlot0EventTopic, 32)) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11127 : decode code ⟨11127⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11128 : decode code ⟨11128⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11129 : decode code ⟨11129⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11130 : decode code ⟨11130⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11131 : decode code ⟨11131⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11132 : decode code ⟨11132⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11133 : decode code ⟨11133⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11134 : decode code ⟨11134⟩ = some (.LOG1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11135 : decode code ⟨11135⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11136 : decode code ⟨11136⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11137 : decode code ⟨11137⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11138 : decode code ⟨11138⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd11139 : decode code ⟨11139⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]; native_decide
  have hd857 : decode code ⟨857⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd858 : decode code ⟨858⟩ = some (.STOP, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have rd11079 := evm_run h with [
    raw dup4 hd11075 (by evm_ov),
    raw mload 0 (UInt256.ofNat 480) (UInt256.ofNat 15) hd11076 mem_cost
      (initializeSlot0EventMem_mload64 ee sqrt tick)
      (by native_decide) (by evm_ov),
    raw swap2 hd11077 (by evm_ov),
    raw dup3 hd11078 (by evm_ov)]
  have rd11086 := evm_run rd11079 with [
    raw mstore 3 (initializeSlot0LogMem0 ee sqrt tick) (UInt256.ofNat 16)
      hd11079 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw dup2 hd11080 (by evm_ov),
    raw add hd11081 (by evm_ov),
    raw swap2 hd11082 (by evm_ov),
    raw swap1 hd11083 (by evm_ov),
    raw swap2 hd11084 (by evm_ov),
    raw mstore 3 (initializeSlot0LogMem ee sqrt tick) (UInt256.ofNat 17)
      hd11085 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd11135 := evm_run rd11086 with [
    raw dup2 hd11086 (by evm_ov),
    raw mload 0 (UInt256.ofNat 480) (UInt256.ofNat 17) hd11087 mem_cost
      (initializeSlot0LogMem_mload64 ee sqrt tick)
      (by native_decide) (by evm_ov),
    raw swap4 hd11088 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap6 hd11089 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd11090 (by evm_ov),
    raw swap2 hd11091 (by evm_ov),
    raw swap4 hd11092 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd11093 (by evm_ov),
    raw pushConst initializeSlot0EventTopic
      (show Operation.POp.PUSH32 ≠ Operation.POp.PUSH0 by native_decide)
      hd11094
      (by evm_ov),
    raw swap3 hd11127 (by evm_ov),
    raw swap2 hd11128 (by evm_ov),
    raw dup3 hd11129 (by evm_ov),
    raw swap1 hd11130 (by evm_ov),
    raw sub hd11131 (by evm_ov),
    raw add hd11132 (by evm_ov),
    raw swap1 hd11133 (by evm_ov),
    raw log1 0 (UInt256.ofNat 17) hd11134 hperm mem_cost
      (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd11139 := evm_run rd11135 with [
    raw pop hd11135 (by evm_ov),
    raw pop hd11136 (by evm_ov),
    raw pop hd11137 (by evm_ov),
    raw pop hd11138 (by evm_ov)]
  have rd857 := rd11139.jump hd11139 (uniswapV3PoolInitializeJumpDestPatched857 hpatch)
    (by evm_ov)
  have rd858 := rd857.jumpdest hd857 (by evm_ov)
  exact rd858.stop hd858 (by
    have h := hov
    omega)

end Benchmarks.UniswapV3Pool
