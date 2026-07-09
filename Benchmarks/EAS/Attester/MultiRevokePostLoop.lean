import Benchmarks.EAS.Attester.MultiRevokeLoopRun
import Benchmarks.EAS.Attester.MultiRevokePostCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

abbrev attesterMultiRevokeEncoderOffsetMem
    (mem : ByteArray) (dst : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem dst.toNat 32

abbrev attesterMultiRevokeEncoderAwAfterOffset
    (aw dst : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat dst.toNat 32)

abbrev attesterMultiRevokeEncoderLengthMem
    (mem : ByteArray) (dst len : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0
    (attesterMultiRevokeEncoderOffsetMem mem dst) (dst + ⟨32⟩).toNat 32

abbrev attesterMultiRevokeEncoderAwAfterLoad
    (aw dst src : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeEncoderAwAfterOffset aw dst).toNat
      src.toNat 32)

abbrev attesterMultiRevokeEncoderAwAfterLength
    (aw dst src : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeEncoderAwAfterLoad aw dst src).toNat
      (dst + ⟨32⟩).toNat 32)

abbrev attesterMultiRevokeEncoderOuterOffsetWord
    (endPtr dst : UInt256) : UInt256 :=
  UInt256.lnot (⟨63⟩ : UInt256) + UInt256.sub endPtr dst

abbrev attesterMultiRevokeEncoderOuterOffsetMem
    (mem : ByteArray) (dstHead endPtr dst : UInt256) : ByteArray :=
  (UInt256.toByteArray
      (attesterMultiRevokeEncoderOuterOffsetWord endPtr dst)).write 0 mem
    dstHead.toNat 32

abbrev attesterMultiRevokeEncoderOuterOffsetAw
    (aw dstHead : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat dstHead.toNat 32)

abbrev attesterMultiRevokeEncoderOuterSrcWord
    (mem : ByteArray) (aw srcHead : UInt256) : UInt256 :=
  attesterMloadWord mem aw srcHead

abbrev attesterMultiRevokeEncoderOuterSrcAw
    (aw srcHead : UInt256) : UInt256 :=
  attesterMloadAw aw srcHead

abbrev attesterMultiRevokeEncoderOuterSchemaWord
    (mem : ByteArray) (aw srcWord : UInt256) : UInt256 :=
  attesterMloadWord mem aw srcWord

abbrev attesterMultiRevokeEncoderOuterSchemaAw
    (aw srcWord : UInt256) : UInt256 :=
  attesterMloadAw aw srcWord

abbrev attesterMultiRevokeEncoderOuterSchemaMem
    (mem : ByteArray) (endPtr schemaWord : UInt256) : ByteArray :=
  (UInt256.toByteArray schemaWord).write 0 mem endPtr.toNat 32

abbrev attesterMultiRevokeEncoderOuterSchemaStoreAw
    (aw endPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat endPtr.toNat 32)

abbrev attesterMultiRevokeEncoderOuterUidsPtrWord
    (mem : ByteArray) (aw srcWord : UInt256) : UInt256 :=
  attesterMloadWord mem aw ((⟨32⟩ : UInt256) + srcWord)

abbrev attesterMultiRevokeEncoderOuterUidsPtrAw
    (aw srcWord : UInt256) : UInt256 :=
  attesterMloadAw aw ((⟨32⟩ : UInt256) + srcWord)

abbrev attesterMultiRevokeEncoderOuterUidsOffsetMem
    (mem : ByteArray) (endPtr : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨64⟩ : UInt256)).write 0 mem (endPtr + ⟨32⟩).toNat 32

abbrev attesterMultiRevokeEncoderOuterUidsOffsetAw
    (aw endPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (endPtr + ⟨32⟩).toNat 32)

abbrev attesterMultiRevokeEncoderOuterUidsLenWord
    (mem : ByteArray) (aw uidsPtr : UInt256) : UInt256 :=
  attesterMloadWord mem aw uidsPtr

abbrev attesterMultiRevokeEncoderOuterUidsLenAw
    (aw uidsPtr : UInt256) : UInt256 :=
  attesterMloadAw aw uidsPtr

abbrev attesterMultiRevokeEncoderOuterUidsLenMem
    (mem : ByteArray) (endPtr uidsLen : UInt256) : ByteArray :=
  (UInt256.toByteArray uidsLen).write 0 mem (endPtr + ⟨64⟩).toNat 32

abbrev attesterMultiRevokeEncoderOuterUidsLenStoreAw
    (aw endPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (endPtr + ⟨64⟩).toNat 32)

abbrev attesterMultiRevokeEncoderInnerFirstWord
    (mem : ByteArray) (aw uidPayload : UInt256) : UInt256 :=
  attesterMloadWord mem aw uidPayload

abbrev attesterMultiRevokeEncoderInnerFirstAw
    (aw uidPayload : UInt256) : UInt256 :=
  attesterMloadAw aw uidPayload

abbrev attesterMultiRevokeEncoderInnerValueWord
    (mem : ByteArray) (aw firstWord : UInt256) : UInt256 :=
  attesterMloadWord mem aw firstWord

abbrev attesterMultiRevokeEncoderInnerValueAw
    (aw firstWord : UInt256) : UInt256 :=
  attesterMloadAw aw firstWord

abbrev attesterMultiRevokeEncoderInnerValueMem
    (mem : ByteArray) (dstData valueWord : UInt256) : ByteArray :=
  (UInt256.toByteArray valueWord).write 0 mem dstData.toNat 32

abbrev attesterMultiRevokeEncoderInnerValueStoreAw
    (aw dstData : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat dstData.toNat 32)

abbrev attesterMultiRevokeEncoderInnerExtraWord
    (mem : ByteArray) (aw firstWord : UInt256) : UInt256 :=
  attesterMloadWord mem aw ((⟨32⟩ : UInt256) + firstWord)

abbrev attesterMultiRevokeEncoderInnerExtraAw
    (aw firstWord : UInt256) : UInt256 :=
  attesterMloadAw aw ((⟨32⟩ : UInt256) + firstWord)

abbrev attesterMultiRevokeEncoderInnerExtraMem
    (mem : ByteArray) (dstData extraWord : UInt256) : ByteArray :=
  (UInt256.toByteArray extraWord).write 0 mem (dstData + ⟨32⟩).toNat 32

abbrev attesterMultiRevokeEncoderInnerExtraStoreAw
    (aw dstData : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (dstData + ⟨32⟩).toNat 32)

theorem attesterX_multiRevokeDoneToEncoder
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    {k C : ℕ}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨698⟩ : UInt256) (attesterMultiRevokeOuterLoopStack a)
      a.mem a.aw ByteArray.empty a.acc k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2422⟩ : UInt256)
        [⟨4⟩ + attesterMultiRevokeCallFree a.mem a.aw, (⟨128⟩ : UInt256),
          ⟨775⟩, attesterMultiRevokeSelectorLow, attesterMultiRevokeTargetWord v,
          (⟨128⟩ : UInt256), attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I, attesterSecondArrayPayloadStartWord I,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiRevokeCallMemAfterSelector a.mem a.aw)
        (attesterMultiRevokeCallAwAfterSelector a.mem a.aw)
        ByteArray.empty (cA, σ) k' C' := by
  have hshape :=
    AttesterMultiRevokeOuterLoopInv.done_shape
      (cA := cA) (σ := σ) (I := I)
      (schemas := schemas) (schemaUids := schemaUids)
      (a := a) (L := L) (evm := evm) hInv
  rcases hshape with
    ⟨_hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, _hidx,
      _hidxToNat, houterBase, hschemaLen, _hschemaLenToNat, hsecondLen,
      _hsecondLenToNat, hsecondPayload, hschemaPayload, hret, hselector, hacc,
      _hawGe, _hawMul, _houterRead, _houterMemSize, _houter64, _hbaseGe,
      _houterBeforeBase, _hfreeLt⟩
  obtain ⟨k', C', rd2422⟩ :=
    attesterX_multiRevokeLoopExitToEncoder
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (by simpa [attesterMultiRevokeOuterLoopStack, hacc] using rd)
  exact ⟨k', C', by
    simpa [houterBase, hschemaLen, hsecondLen, hsecondPayload, hschemaPayload,
      hret, hselector] using rd2422⟩

theorem attesterMultiRevokeEncoderPreambleLoad_fromDone
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    attesterMloadWord
        (attesterMultiRevokeEncoderOffsetMem
          (attesterMultiRevokeCallMemAfterSelector a.mem a.aw)
          ((⟨4⟩ : UInt256) + attesterMultiRevokeCallFree a.mem a.aw))
        (attesterMultiRevokeEncoderAwAfterOffset
          (attesterMultiRevokeCallAwAfterSelector a.mem a.aw)
          ((⟨4⟩ : UInt256) + attesterMultiRevokeCallFree a.mem a.aw))
        (⟨128⟩ : UInt256) =
      attesterFirstArrayLengthWord I := by
  let free := attesterMultiRevokeCallFree a.mem a.aw
  let memSel := attesterMultiRevokeCallMemAfterSelector a.mem a.aw
  let awLoad := attesterMultiRevokeCallAwAfterMload a.aw
  let awSel := attesterMultiRevokeCallAwAfterSelector a.mem a.aw
  let dst := (⟨4⟩ : UInt256) + free
  let memOff := attesterMultiRevokeEncoderOffsetMem memSel dst
  let awOff := attesterMultiRevokeEncoderAwAfterOffset awSel dst
  have hshape :=
    AttesterMultiRevokeOuterLoopInv.done_shape
      (cA := cA) (σ := σ) (I := I)
      (schemas := schemas) (schemaUids := schemaUids)
      (a := a) (L := L) (evm := evm) hInv
  rcases hshape with
    ⟨_hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, _hidx,
      _hidxToNat, houterBase, hschemaLen, _hschemaLenToNat, _hsecondLen,
      _hsecondLenToNat, _hsecondPayload, _hschemaPayload, _hret, _hselector,
      _hacc, hawGe, hawMul, houterRead, houterMemSize, _houter64, _hbaseGe,
      houterBeforeBase, hfree128⟩
  have hread0 :
      a.mem.readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    simpa [houterBase, hschemaLen] using houterRead
  have hmem0 : 128 + 32 ≤ a.mem.size := by
    simpa [houterBase] using houterMemSize
  have hfreeAbove : 128 + 32 ≤ free.toNat := by
    dsimp [free, attesterMultiRevokeCallFree]
    simpa [houterBase] using houterBeforeBase
  have hfree128Call : free.toNat + 128 < UInt256.size := by
    simpa [free, attesterMultiRevokeCallFree, attesterInnerArrayAllocFreeWord]
      using hfree128
  have hfree63 : free.toNat + 63 < UInt256.size := by
    omega
  have hfree4 : free.toNat + 4 < UInt256.size := by
    omega
  have hdstToNat : dst.toNat = free.toNat + 4 := by
    dsimp [dst]
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 by decide]
    rw [show 4 + free.toNat = free.toNat + 4 by omega, Nat.mod_eq_of_lt hfree4]
  have hdst63 : dst.toNat + 63 < UInt256.size := by
    rw [hdstToNat]
    omega
  have hreadSel :
      memSel.readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    dsimp [memSel, attesterMultiRevokeCallMemAfterSelector, free,
      attesterMultiRevokeCallFree]
    change
      (Reasoning.Theory.writeWord a.mem (attesterMloadWord a.mem a.aw ⟨64⟩).toNat
        attesterMultiRevokeSelectorWord).readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (base := 128) (writeOff := (attesterMloadWord a.mem a.aw ⟨64⟩).toNat)
      (len := attesterFirstArrayLengthWord I)
      hmem0 hfreeAbove hread0
  have hmemSel : 128 + 32 ≤ memSel.size := by
    dsimp [memSel, attesterMultiRevokeCallMemAfterSelector, free,
      attesterMultiRevokeCallFree]
    change
      128 + 32 ≤
        (Reasoning.Theory.writeWord a.mem
          (attesterMloadWord a.mem a.aw ⟨64⟩).toNat
          attesterMultiRevokeSelectorWord).size
    exact le_trans hmem0
      (attesterWriteWord_size_ge_nat a.mem
        (attesterMloadWord a.mem a.aw ⟨64⟩).toNat
        attesterMultiRevokeSelectorWord)
  have hreadOff :
      memOff.readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    dsimp [memOff, attesterMultiRevokeEncoderOffsetMem]
    change
      (Reasoning.Theory.writeWord memSel dst.toNat (⟨32⟩ : UInt256)).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (base := 128) (writeOff := dst.toNat)
      (len := attesterFirstArrayLengthWord I)
      hmemSel (by rw [hdstToNat]; omega) hreadSel
  have hmemOff : (⟨128⟩ : UInt256).toNat + 32 ≤ memOff.size := by
    change 128 + 32 ≤ memOff.size
    dsimp [memOff, attesterMultiRevokeEncoderOffsetMem]
    change
      128 + 32 ≤
        (Reasoning.Theory.writeWord memSel dst.toNat (⟨32⟩ : UInt256)).size
    exact le_trans hmemSel
      (attesterWriteWord_size_ge_nat memSel dst.toNat (⟨32⟩ : UInt256))
  have hM64 : MachineState.M a.aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := a.aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul (by decide)
  have hM64Mul :
      MachineState.M a.aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 <
        UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := a.aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul (by decide)
  have hawLoadMul : awLoad.toNat * 32 < UInt256.size := by
    dsimp [awLoad, attesterMultiRevokeCallAwAfterMload, attesterMloadAw]
    rw [ulit_toNat' _ hM64]
    exact hM64Mul
  have hMSel : MachineState.M awLoad.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := awLoad.toNat) (f := free.toNat)
      hawLoadMul hfree63
  have hMSelMul :
      MachineState.M awLoad.toNat free.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := awLoad.toNat) (f := free.toNat)
      hawLoadMul hfree63
  have hawSelMul : awSel.toNat * 32 < UInt256.size := by
    dsimp [awSel, attesterMultiRevokeCallAwAfterSelector,
      attesterMultiRevokeCallFree, awLoad, free]
    rw [ulit_toNat' _ hMSel]
    exact hMSelMul
  have hMOff : MachineState.M awSel.toNat dst.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := awSel.toNat) (f := dst.toNat)
      hawSelMul hdst63
  have hMOffMul :
      MachineState.M awSel.toNat dst.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := awSel.toNat) (f := dst.toNat)
      hawSelMul hdst63
  have hawOffMul : awOff.toNat * 32 < UInt256.size := by
    dsimp [awOff, attesterMultiRevokeEncoderAwAfterOffset]
    rw [ulit_toNat' _ hMOff]
    exact hMOffMul
  have hcovered : (⟨128⟩ : UInt256).toNat + 32 ≤ awOff.toNat * 32 := by
    dsimp [awOff, attesterMultiRevokeEncoderAwAfterOffset]
    rw [ulit_toNat' _ hMOff]
    change 128 + 32 ≤ MachineState.M awSel.toNat dst.toNat 32 * 32
    have hdstCover :
        dst.toNat + 32 ≤ MachineState.M awSel.toNat dst.toNat 32 * 32 := by
      simpa [Nat.mul_comm] using
        (attesterMachineStateM_covers_word32 awSel.toNat dst.toNat)
    have hdstLower : 128 + 32 ≤ dst.toNat + 32 := by
      rw [hdstToNat]
      omega
    exact le_trans hdstLower hdstCover
  have hawOff :
      ¬ (⟨128⟩ : UInt256) ≥ awOff * (⟨32⟩ : UInt256) :=
    attesterMloadActiveWordsCovers hawOffMul hcovered
  exact attesterMloadWord_of_readWithPadding hmemOff hawOff (by
    change memOff.readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I)
    exact hreadOff)

theorem attesterX_multiRevokeEncoderPreambleToOuterLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {dst : UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hload :
      attesterMloadWord
          (attesterMultiRevokeEncoderOffsetMem mem dst)
          (attesterMultiRevokeEncoderAwAfterOffset aw dst)
          (⟨128⟩ : UInt256) =
        attesterFirstArrayLengthWord I)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2422⟩ : UInt256)
      [dst, (⟨128⟩ : UInt256), ⟨775⟩, attesterMultiRevokeSelectorLow,
        attesterMultiRevokeTargetWord v, (⟨128⟩ : UInt256),
        attesterFirstArrayLengthWord I, attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2460⟩ : UInt256)
        [(⟨0⟩ : UInt256), (⟨128⟩ : UInt256) + ⟨32⟩,
          attesterFirstArrayLengthWord I, dst + ⟨64⟩,
          (dst + UInt256.shiftLeft (attesterFirstArrayLengthWord I) ⟨5⟩) + ⟨64⟩,
          (⟨0⟩ : UInt256), dst, (⟨128⟩ : UInt256), ⟨775⟩,
          attesterMultiRevokeSelectorLow, attesterMultiRevokeTargetWord v,
          (⟨128⟩ : UInt256), attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I, attesterSecondArrayPayloadStartWord I,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiRevokeEncoderLengthMem mem dst (attesterFirstArrayLengthWord I))
        (attesterMultiRevokeEncoderAwAfterLength aw dst (⟨128⟩ : UInt256))
        ByteArray.empty (cA, σ) k' C' := by
  let mem1 := attesterMultiRevokeEncoderOffsetMem mem dst
  let aw1 := attesterMultiRevokeEncoderAwAfterOffset aw dst
  let len := attesterFirstArrayLengthWord I
  let aw2 := attesterMultiRevokeEncoderAwAfterLoad aw dst (⟨128⟩ : UInt256)
  let mem2 := attesterMultiRevokeEncoderLengthMem mem dst len
  let aw3 := attesterMultiRevokeEncoderAwAfterLength aw dst (⟨128⟩ : UInt256)
  have hcostStoreOffset :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          dst :: (⟨32⟩ : UInt256) :: (dst + ⟨32⟩) :: (⟨0⟩ : UInt256) ::
            dst :: (⟨128⟩ : UInt256) :: ⟨775⟩ ::
            attesterMultiRevokeSelectorLow :: attesterMultiRevokeTargetWord v ::
            (⟨128⟩ : UInt256) :: attesterFirstArrayLengthWord I ::
            attesterSecondArrayLengthWord I :: attesterSecondArrayPayloadStartWord I ::
            attesterFirstArrayLengthWord I ::
            ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩) ::
            ⟨97⟩ :: solcSelectorWord I :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadLen :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          (⟨128⟩ : UInt256) :: (dst + ⟨32⟩) :: (dst + ⟨32⟩) ::
            (⟨0⟩ : UInt256) :: dst :: (⟨128⟩ : UInt256) :: ⟨775⟩ ::
            attesterMultiRevokeSelectorLow :: attesterMultiRevokeTargetWord v ::
            (⟨128⟩ : UInt256) :: attesterFirstArrayLengthWord I ::
            attesterSecondArrayLengthWord I :: attesterSecondArrayPayloadStartWord I ::
            attesterFirstArrayLengthWord I ::
            ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩) ::
            ⟨97⟩ :: solcSelectorWord I :: [] →
        memoryExpansionCost s .MLOAD = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreLen :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (dst + ⟨32⟩) :: len :: len :: (dst + ⟨32⟩) ::
            (dst + ⟨32⟩) :: (⟨0⟩ : UInt256) :: dst ::
            (⟨128⟩ : UInt256) :: ⟨775⟩ :: attesterMultiRevokeSelectorLow ::
            attesterMultiRevokeTargetWord v :: (⟨128⟩ : UInt256) ::
            attesterFirstArrayLengthWord I :: attesterSecondArrayLengthWord I ::
            attesterSecondArrayPayloadStartWord I :: attesterFirstArrayLengthWord I ::
            ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩) ::
            ⟨97⟩ :: solcSelectorWord I :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [mem1, aw1, len, aw2, mem2, aw3,
      attesterMultiRevokeEncoderOffsetMem,
      attesterMultiRevokeEncoderAwAfterOffset,
      attesterMultiRevokeEncoderAwAfterLoad,
      attesterMultiRevokeEncoderLengthMem,
      attesterMultiRevokeEncoderAwAfterLength] using
      evm_run rd with [
        raw jumpdest (by attester_decode_at v, ⟨2422⟩, 0x5b, .JUMPDEST)
          (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨2423⟩, 0x5f, .PUSH0)
          (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2424⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup3 (by attester_decode_at v, ⟨2426⟩, 0x82, .DUP3)
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2427⟩, 0x01, .ADD)
          (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2428⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup4 (by attester_decode_at v, ⟨2430⟩, 0x83, .DUP4)
          (by evm_ov),
        raw mstore (Cₘ aw1 - Cₘ aw) mem1 aw1
          (by attester_decode_at v, ⟨2431⟩, 0x52, .MSTORE)
          hcostStoreOffset (by rfl) (by rfl) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨2432⟩, 0x80, .DUP1)
          (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨2433⟩, 0x84, .DUP5)
          (by evm_ov),
        raw mload (Cₘ aw2 - Cₘ aw1) len aw2
          (by attester_decode_at v, ⟨2434⟩, 0x51, .MLOAD)
          hcostLoadLen
          (by simpa [mem1, aw1, len] using hload)
          (by rfl) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨2435⟩, 0x80, .DUP1)
          (by evm_ov),
        raw dup4 (by attester_decode_at v, ⟨2436⟩, 0x83, .DUP4)
          (by evm_ov),
        raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
          (by attester_decode_at v, ⟨2437⟩, 0x52, .MSTORE)
          hcostStoreLen (by rfl) (by rfl) (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2438⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup6 (by attester_decode_at v, ⟨2440⟩, 0x85, .DUP6)
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2441⟩, 0x01, .ADD)
          (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2442⟩, 0x91, .SWAP2)
          (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2443⟩, 0x50, .POP)
          (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2444⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2446⟩, 0x81, .DUP2)
          (by evm_ov),
        raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2447⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw shl (by attester_decode_at v, ⟨2449⟩, 0x1b, .SHL)
          (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨2450⟩, 0x86, .DUP7)
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2451⟩, 0x01, .ADD)
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2452⟩, 0x01, .ADD)
          (by evm_ov),
        raw swap3 (by attester_decode_at v, ⟨2453⟩, 0x92, .SWAP3)
          (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2454⟩, 0x50, .POP)
          (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2455⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨2457⟩, 0x86, .DUP7)
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2458⟩, 0x01, .ADD)
          (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨2459⟩, 0x5f, .PUSH0)
          (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderOuterLoopGuard
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt idx len = ⟨1⟩)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2460⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
        tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2469⟩ : UInt256)
        (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
          tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨2460⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2461⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2462⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨2463⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2464⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2592⟩ (by attester_decode_at v, ⟨2465⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2468⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderOuterLoopToInnerLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2469⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
        tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      let mem1 := attesterMultiRevokeEncoderOuterOffsetMem mem dstHead endPtr dst
      let aw1 := attesterMultiRevokeEncoderOuterOffsetAw aw dstHead
      let srcWord := attesterMultiRevokeEncoderOuterSrcWord mem1 aw1 srcHead
      let aw2 := attesterMultiRevokeEncoderOuterSrcAw aw1 srcHead
      let schemaWord := attesterMultiRevokeEncoderOuterSchemaWord mem1 aw2 srcWord
      let aw3 := attesterMultiRevokeEncoderOuterSchemaAw aw2 srcWord
      let mem2 := attesterMultiRevokeEncoderOuterSchemaMem mem1 endPtr schemaWord
      let aw4 := attesterMultiRevokeEncoderOuterSchemaStoreAw aw3 endPtr
      let uidsPtr := attesterMultiRevokeEncoderOuterUidsPtrWord mem2 aw4 srcWord
      let aw5 := attesterMultiRevokeEncoderOuterUidsPtrAw aw4 srcWord
      let mem3 := attesterMultiRevokeEncoderOuterUidsOffsetMem mem2 endPtr
      let aw6 := attesterMultiRevokeEncoderOuterUidsOffsetAw aw5 endPtr
      let uidsLen := attesterMultiRevokeEncoderOuterUidsLenWord mem3 aw6 uidsPtr
      let aw7 := attesterMultiRevokeEncoderOuterUidsLenAw aw6 uidsPtr
      let mem4 := attesterMultiRevokeEncoderOuterUidsLenMem mem3 endPtr uidsLen
      let aw8 := attesterMultiRevokeEncoderOuterUidsLenStoreAw aw7 endPtr
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2516⟩ : UInt256)
        (uidsLen :: (endPtr + ⟨96⟩) :: (⟨0⟩ : UInt256) ::
          ((⟨32⟩ : UInt256) + uidsPtr) :: idx :: srcHead :: len :: dstHead ::
          endPtr :: scratch :: dst :: src :: ret :: tail)
        mem4 aw8 ByteArray.empty (cA, σ) k' C' := by
  let offsetWord := attesterMultiRevokeEncoderOuterOffsetWord endPtr dst
  let mem1 := attesterMultiRevokeEncoderOuterOffsetMem mem dstHead endPtr dst
  let aw1 := attesterMultiRevokeEncoderOuterOffsetAw aw dstHead
  let srcWord := attesterMultiRevokeEncoderOuterSrcWord mem1 aw1 srcHead
  let aw2 := attesterMultiRevokeEncoderOuterSrcAw aw1 srcHead
  let schemaWord := attesterMultiRevokeEncoderOuterSchemaWord mem1 aw2 srcWord
  let aw3 := attesterMultiRevokeEncoderOuterSchemaAw aw2 srcWord
  let mem2 := attesterMultiRevokeEncoderOuterSchemaMem mem1 endPtr schemaWord
  let aw4 := attesterMultiRevokeEncoderOuterSchemaStoreAw aw3 endPtr
  let uidsPtr := attesterMultiRevokeEncoderOuterUidsPtrWord mem2 aw4 srcWord
  let aw5 := attesterMultiRevokeEncoderOuterUidsPtrAw aw4 srcWord
  let mem3 := attesterMultiRevokeEncoderOuterUidsOffsetMem mem2 endPtr
  let aw6 := attesterMultiRevokeEncoderOuterUidsOffsetAw aw5 endPtr
  let uidsLen := attesterMultiRevokeEncoderOuterUidsLenWord mem3 aw6 uidsPtr
  let aw7 := attesterMultiRevokeEncoderOuterUidsLenAw aw6 uidsPtr
  let mem4 := attesterMultiRevokeEncoderOuterUidsLenMem mem3 endPtr uidsLen
  let aw8 := attesterMultiRevokeEncoderOuterUidsLenStoreAw aw7 endPtr
  have hcostStoreOffset :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          dstHead :: offsetWord :: idx :: srcHead :: len :: dstHead :: endPtr ::
            scratch :: dst :: src :: ret :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadSrc :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          srcHead :: idx :: srcHead :: len :: dstHead :: endPtr :: scratch ::
            dst :: src :: ret :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadSchema :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          srcWord :: srcWord :: idx :: srcHead :: len :: dstHead :: endPtr ::
            scratch :: dst :: src :: ret :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSchema :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          endPtr :: schemaWord :: srcWord :: idx :: srcHead :: len :: dstHead ::
            endPtr :: scratch :: dst :: src :: ret :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadUidsPtr :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          ((⟨32⟩ : UInt256) + srcWord) :: (⟨32⟩ : UInt256) :: idx ::
            srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src ::
            ret :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreUidsOffset :
      ∀ s : State,
        s.machineState.activeWords = aw5 →
        s.machineState.stack =
          (endPtr + ⟨32⟩) :: (⟨64⟩ : UInt256) :: (⟨64⟩ : UInt256) ::
            uidsPtr :: (⟨32⟩ : UInt256) :: idx :: srcHead :: len :: dstHead ::
            endPtr :: scratch :: dst :: src :: ret :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw6 - Cₘ aw5 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadUidsLen :
      ∀ s : State,
        s.machineState.activeWords = aw6 →
        s.machineState.stack =
          uidsPtr :: (⟨64⟩ : UInt256) :: uidsPtr :: (⟨32⟩ : UInt256) ::
            idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst ::
            src :: ret :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw7 - Cₘ aw6 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreUidsLen :
      ∀ s : State,
        s.machineState.activeWords = aw7 →
        s.machineState.stack =
          (endPtr + ⟨64⟩) :: uidsLen :: uidsLen :: uidsPtr ::
            (⟨32⟩ : UInt256) :: idx :: srcHead :: len :: dstHead :: endPtr ::
            scratch :: dst :: src :: ret :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw8 - Cₘ aw7 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [offsetWord, mem1, aw1, srcWord, aw2, schemaWord, aw3, mem2, aw4,
      uidsPtr, aw5, mem3, aw6, uidsLen, aw7, mem4, aw8,
      attesterMultiRevokeEncoderOuterOffsetWord,
      attesterMultiRevokeEncoderOuterOffsetMem,
      attesterMultiRevokeEncoderOuterOffsetAw,
      attesterMultiRevokeEncoderOuterSrcWord,
      attesterMultiRevokeEncoderOuterSrcAw,
      attesterMultiRevokeEncoderOuterSchemaWord,
      attesterMultiRevokeEncoderOuterSchemaAw,
      attesterMultiRevokeEncoderOuterSchemaMem,
      attesterMultiRevokeEncoderOuterSchemaStoreAw,
      attesterMultiRevokeEncoderOuterUidsPtrWord,
      attesterMultiRevokeEncoderOuterUidsPtrAw,
      attesterMultiRevokeEncoderOuterUidsOffsetMem,
      attesterMultiRevokeEncoderOuterUidsOffsetAw,
      attesterMultiRevokeEncoderOuterUidsLenWord,
      attesterMultiRevokeEncoderOuterUidsLenAw,
      attesterMultiRevokeEncoderOuterUidsLenMem,
      attesterMultiRevokeEncoderOuterUidsLenStoreAw] using
      evm_run rd with [
        raw dup7 (by attester_decode_at v, ⟨2469⟩, 0x86, .DUP7) (by evm_ov),
        raw dup6 (by attester_decode_at v, ⟨2470⟩, 0x85, .DUP6) (by evm_ov),
        raw sub (by attester_decode_at v, ⟨2471⟩, 0x03, .SUB) (by evm_ov),
        raw push1 ⟨63⟩ (by attester_decode_at v, ⟨2472⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw not (by attester_decode_at v, ⟨2474⟩, 0x19, .NOT) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2475⟩, 0x01, .ADD) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨2476⟩, 0x84, .DUP5) (by evm_ov),
        raw mstore (Cₘ aw1 - Cₘ aw) mem1 aw1
          (by attester_decode_at v, ⟨2477⟩, 0x52, .MSTORE)
          hcostStoreOffset (by rfl) (by rfl) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2478⟩, 0x81, .DUP2) (by evm_ov),
        raw mload (Cₘ aw2 - Cₘ aw1) srcWord aw2
          (by attester_decode_at v, ⟨2479⟩, 0x51, .MLOAD)
          hcostLoadSrc (by rfl) (by rfl) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨2480⟩, 0x80, .DUP1) (by evm_ov),
        raw mload (Cₘ aw3 - Cₘ aw2) schemaWord aw3
          (by attester_decode_at v, ⟨2481⟩, 0x51, .MLOAD)
          hcostLoadSchema (by rfl) (by rfl) (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨2482⟩, 0x86, .DUP7) (by evm_ov),
        raw mstore (Cₘ aw4 - Cₘ aw3) mem2 aw4
          (by attester_decode_at v, ⟨2483⟩, 0x52, .MSTORE)
          hcostStoreSchema (by rfl) (by rfl) (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2484⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2486⟩, 0x90, .SWAP1) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2487⟩, 0x81, .DUP2) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2488⟩, 0x01, .ADD) (by evm_ov),
        raw mload (Cₘ aw5 - Cₘ aw4) uidsPtr aw5
          (by attester_decode_at v, ⟨2489⟩, 0x51, .MLOAD)
          hcostLoadUidsPtr (by rfl) (by rfl) (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2490⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup3 (by attester_decode_at v, ⟨2492⟩, 0x82, .DUP3) (by evm_ov),
        raw dup9 (by attester_decode_at v, ⟨2493⟩, 0x88, .DUP9) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2494⟩, 0x01, .ADD) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2495⟩, 0x81, .DUP2) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2496⟩, 0x90, .SWAP1) (by evm_ov),
        raw mstore (Cₘ aw6 - Cₘ aw5) mem3 aw6
          (by attester_decode_at v, ⟨2497⟩, 0x52, .MSTORE)
          hcostStoreUidsOffset (by rfl) (by rfl) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2498⟩, 0x81, .DUP2) (by evm_ov),
        raw mload (Cₘ aw7 - Cₘ aw6) uidsLen aw7
          (by attester_decode_at v, ⟨2499⟩, 0x51, .MLOAD)
          hcostLoadUidsLen (by rfl) (by rfl) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2500⟩, 0x90, .SWAP1) (by evm_ov),
        raw dup9 (by attester_decode_at v, ⟨2501⟩, 0x88, .DUP9) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2502⟩, 0x01, .ADD) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2503⟩, 0x81, .DUP2) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2504⟩, 0x90, .SWAP1) (by evm_ov),
        raw mstore (Cₘ aw8 - Cₘ aw7) mem4 aw8
          (by attester_decode_at v, ⟨2505⟩, 0x52, .MSTORE)
          hcostStoreUidsLen (by rfl) (by rfl) (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2506⟩, 0x91, .SWAP2) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2507⟩, 0x01, .ADD) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2508⟩, 0x90, .SWAP1) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨2509⟩, 0x5f, .PUSH0) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2510⟩, 0x90, .SWAP1) (by evm_ov),
        raw push1 ⟨96⟩ (by attester_decode_at v, ⟨2511⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup9 (by attester_decode_at v, ⟨2513⟩, 0x88, .DUP9) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2514⟩, 0x01, .ADD) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2515⟩, 0x90, .SWAP1) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderInnerLoopGuard
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData innerIdx uidPayload : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt innerIdx innerLen = ⟨1⟩)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2516⟩ : UInt256)
      (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2525⟩ : UInt256)
        (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨2516⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2517⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2518⟩, 0x83, .DUP4) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨2519⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2520⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2568⟩ (by attester_decode_at v, ⟨2521⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2524⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderInnerLoopStepPrefix
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData innerIdx uidPayload : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2525⟩ : UInt256)
      (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      let firstWord := attesterMultiRevokeEncoderInnerFirstWord mem aw uidPayload
      let aw1 := attesterMultiRevokeEncoderInnerFirstAw aw uidPayload
      let valueWord := attesterMultiRevokeEncoderInnerValueWord mem aw1 firstWord
      let aw2 := attesterMultiRevokeEncoderInnerValueAw aw1 firstWord
      let mem1 := attesterMultiRevokeEncoderInnerValueMem mem dstData valueWord
      let aw3 := attesterMultiRevokeEncoderInnerValueStoreAw aw2 dstData
      let extraWord := attesterMultiRevokeEncoderInnerExtraWord mem1 aw3 firstWord
      let aw4 := attesterMultiRevokeEncoderInnerExtraAw aw3 firstWord
      let mem2 := attesterMultiRevokeEncoderInnerExtraMem mem1 dstData extraWord
      let aw5 := attesterMultiRevokeEncoderInnerExtraStoreAw aw4 dstData
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2544⟩ : UInt256)
        ((⟨2545⟩ : UInt256) :: innerLen :: dstData :: innerIdx ::
          uidPayload :: tail)
        mem2 aw5 ByteArray.empty (cA, σ) k' C' := by
  let firstWord := attesterMultiRevokeEncoderInnerFirstWord mem aw uidPayload
  let aw1 := attesterMultiRevokeEncoderInnerFirstAw aw uidPayload
  let valueWord := attesterMultiRevokeEncoderInnerValueWord mem aw1 firstWord
  let aw2 := attesterMultiRevokeEncoderInnerValueAw aw1 firstWord
  let mem1 := attesterMultiRevokeEncoderInnerValueMem mem dstData valueWord
  let aw3 := attesterMultiRevokeEncoderInnerValueStoreAw aw2 dstData
  let extraWord := attesterMultiRevokeEncoderInnerExtraWord mem1 aw3 firstWord
  let aw4 := attesterMultiRevokeEncoderInnerExtraAw aw3 firstWord
  let mem2 := attesterMultiRevokeEncoderInnerExtraMem mem1 dstData extraWord
  let aw5 := attesterMultiRevokeEncoderInnerExtraStoreAw aw4 dstData
  have hcostLoadFirst :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          uidPayload :: dstData :: (⟨2545⟩ : UInt256) :: innerLen :: dstData ::
            innerIdx :: uidPayload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadValue :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          firstWord :: firstWord :: dstData :: (⟨2545⟩ : UInt256) ::
            innerLen :: dstData :: innerIdx :: uidPayload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreValue :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          dstData :: valueWord :: firstWord :: dstData :: (⟨2545⟩ : UInt256) ::
            innerLen :: dstData :: innerIdx :: uidPayload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostLoadExtra :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          ((⟨32⟩ : UInt256) + firstWord) :: (⟨32⟩ : UInt256) ::
            dstData :: (⟨2545⟩ : UInt256) :: innerLen :: dstData ::
            innerIdx :: uidPayload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreExtra :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          (dstData + ⟨32⟩) :: extraWord :: (⟨2545⟩ : UInt256) ::
            innerLen :: dstData :: innerIdx :: uidPayload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [firstWord, aw1, valueWord, aw2, mem1, aw3, extraWord, aw4, mem2, aw5,
      attesterMultiRevokeEncoderInnerFirstWord,
      attesterMultiRevokeEncoderInnerFirstAw,
      attesterMultiRevokeEncoderInnerValueWord,
      attesterMultiRevokeEncoderInnerValueAw,
      attesterMultiRevokeEncoderInnerValueMem,
      attesterMultiRevokeEncoderInnerValueStoreAw,
      attesterMultiRevokeEncoderInnerExtraWord,
      attesterMultiRevokeEncoderInnerExtraAw,
      attesterMultiRevokeEncoderInnerExtraMem,
      attesterMultiRevokeEncoderInnerExtraStoreAw] using
      evm_run rd with [
        raw push2 ⟨2545⟩ (by attester_decode_at v, ⟨2525⟩, 0x61, (.Push .PUSH2))
          (by evm_ov),
        raw dup3 (by attester_decode_at v, ⟨2528⟩, 0x82, .DUP3) (by evm_ov),
        raw dup6 (by attester_decode_at v, ⟨2529⟩, 0x85, .DUP6) (by evm_ov),
        raw mload (Cₘ aw1 - Cₘ aw) firstWord aw1
          (by attester_decode_at v, ⟨2530⟩, 0x51, .MLOAD)
          hcostLoadFirst (by rfl) (by rfl) (by evm_ov),
        raw dup1 (by attester_decode_at v, ⟨2531⟩, 0x80, .DUP1) (by evm_ov),
        raw mload (Cₘ aw2 - Cₘ aw1) valueWord aw2
          (by attester_decode_at v, ⟨2532⟩, 0x51, .MLOAD)
          hcostLoadValue (by rfl) (by rfl) (by evm_ov),
        raw dup3 (by attester_decode_at v, ⟨2533⟩, 0x82, .DUP3) (by evm_ov),
        raw mstore (Cₘ aw3 - Cₘ aw2) mem1 aw3
          (by attester_decode_at v, ⟨2534⟩, 0x52, .MSTORE)
          hcostStoreValue (by rfl) (by rfl) (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2535⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2537⟩, 0x90, .SWAP1) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨2538⟩, 0x81, .DUP2) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2539⟩, 0x01, .ADD) (by evm_ov),
        raw mload (Cₘ aw4 - Cₘ aw3) extraWord aw4
          (by attester_decode_at v, ⟨2540⟩, 0x51, .MLOAD)
          hcostLoadExtra (by rfl) (by rfl) (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2541⟩, 0x91, .SWAP2) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2542⟩, 0x01, .ADD) (by evm_ov),
        raw mstore (Cₘ aw5 - Cₘ aw4) mem2 aw5
          (by attester_decode_at v, ⟨2543⟩, 0x52, .MSTORE)
          hcostStoreExtra (by rfl) (by rfl) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderInnerLoopStep
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData innerIdx uidPayload : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2525⟩ : UInt256)
      (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      let firstWord := attesterMultiRevokeEncoderInnerFirstWord mem aw uidPayload
      let aw1 := attesterMultiRevokeEncoderInnerFirstAw aw uidPayload
      let valueWord := attesterMultiRevokeEncoderInnerValueWord mem aw1 firstWord
      let aw2 := attesterMultiRevokeEncoderInnerValueAw aw1 firstWord
      let mem1 := attesterMultiRevokeEncoderInnerValueMem mem dstData valueWord
      let aw3 := attesterMultiRevokeEncoderInnerValueStoreAw aw2 dstData
      let extraWord := attesterMultiRevokeEncoderInnerExtraWord mem1 aw3 firstWord
      let aw4 := attesterMultiRevokeEncoderInnerExtraAw aw3 firstWord
      let mem2 := attesterMultiRevokeEncoderInnerExtraMem mem1 dstData extraWord
      let aw5 := attesterMultiRevokeEncoderInnerExtraStoreAw aw4 dstData
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2516⟩ : UInt256)
        (innerLen :: (dstData + ⟨64⟩) :: (innerIdx + ⟨1⟩) ::
          (uidPayload + ⟨32⟩) :: tail)
        mem2 aw5 ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k1, C1, rd2544⟩ :=
    attesterX_multiRevokeEncoderInnerLoopStepPrefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v htail rd
  exact ⟨_, _, by
    simpa [u256_add_comm] using
      evm_run rd2544 with [
        raw jump (by attester_decode_at v, ⟨2544⟩, 0x56, .JUMP)
          (attesterMultiRevokeEncodeInnerReturnJumpdest v) (by evm_ov),
        raw jumpdest (by attester_decode_at v, ⟨2545⟩, 0x5b, .JUMPDEST) (by evm_ov),
        raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2546⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup3 (by attester_decode_at v, ⟨2548⟩, 0x82, .DUP3) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2549⟩, 0x01, .ADD) (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2550⟩, 0x91, .SWAP2) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2551⟩, 0x50, .POP) (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2552⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨2554⟩, 0x84, .DUP5) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2555⟩, 0x01, .ADD) (by evm_ov),
        raw swap4 (by attester_decode_at v, ⟨2556⟩, 0x93, .SWAP4) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2557⟩, 0x50, .POP) (by evm_ov),
        raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2558⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw dup4 (by attester_decode_at v, ⟨2560⟩, 0x83, .DUP4) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2561⟩, 0x01, .ADD) (by evm_ov),
        raw swap3 (by attester_decode_at v, ⟨2562⟩, 0x92, .SWAP3) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2563⟩, 0x50, .POP) (by evm_ov),
        raw push2 ⟨2516⟩ (by attester_decode_at v, ⟨2564⟩, 0x61, (.Push .PUSH2))
          (by evm_ov),
        raw jump (by attester_decode_at v, ⟨2567⟩, 0x56, .JUMP)
          (attesterMultiRevokeEncodeInnerLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderInnerLoopExitGuard
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData innerIdx uidPayload : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt innerIdx innerLen = ⟨0⟩)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2516⟩ : UInt256)
      (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2568⟩ : UInt256)
        (innerLen :: dstData :: innerIdx :: uidPayload :: tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨2516⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2517⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2518⟩, 0x83, .DUP4) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨2519⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2520⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2568⟩ (by attester_decode_at v, ⟨2521⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2524⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide)
      (attesterMultiRevokeEncodeInnerExitJumpdest v) (by evm_ov)]⟩

structure AttesterMultiRevokeEncoderInnerState where
  dstData : UInt256
  innerIdx : UInt256
  uidPayload : UInt256
  mem : ByteArray
  aw : UInt256

def attesterMultiRevokeEncoderInnerStack
    (innerLen : UInt256) (tail : List UInt256)
    (s : AttesterMultiRevokeEncoderInnerState) : List UInt256 :=
  innerLen :: s.dstData :: s.innerIdx :: s.uidPayload :: tail

def attesterMultiRevokeEncoderInnerStepState
    (s : AttesterMultiRevokeEncoderInnerState) :
    AttesterMultiRevokeEncoderInnerState :=
  let firstWord := attesterMultiRevokeEncoderInnerFirstWord s.mem s.aw s.uidPayload
  let aw1 := attesterMultiRevokeEncoderInnerFirstAw s.aw s.uidPayload
  let valueWord := attesterMultiRevokeEncoderInnerValueWord s.mem aw1 firstWord
  let aw2 := attesterMultiRevokeEncoderInnerValueAw aw1 firstWord
  let mem1 := attesterMultiRevokeEncoderInnerValueMem s.mem s.dstData valueWord
  let aw3 := attesterMultiRevokeEncoderInnerValueStoreAw aw2 s.dstData
  let extraWord := attesterMultiRevokeEncoderInnerExtraWord mem1 aw3 firstWord
  let aw4 := attesterMultiRevokeEncoderInnerExtraAw aw3 firstWord
  let mem2 := attesterMultiRevokeEncoderInnerExtraMem mem1 s.dstData extraWord
  let aw5 := attesterMultiRevokeEncoderInnerExtraStoreAw aw4 s.dstData
  { dstData := s.dstData + ⟨64⟩,
    innerIdx := s.innerIdx + ⟨1⟩,
    uidPayload := s.uidPayload + ⟨32⟩,
    mem := mem2,
    aw := aw5 }

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeEncoderInnerLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData uidPayload : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (Inv : Nat → AttesterMultiRevokeEncoderInnerState → Prop)
    (hidx : ∀ n s, Inv n s → s.innerIdx = UInt256.ofNat (innerLen.toNat - n))
    (hle : ∀ n s, Inv n s → n ≤ innerLen.toNat)
    (hstep :
      ∀ n s, Inv (n + 1) s →
        Inv n (attesterMultiRevokeEncoderInnerStepState s))
    (hInv0 :
      Inv innerLen.toNat
        { dstData := dstData,
          innerIdx := (⟨0⟩ : UInt256),
          uidPayload := uidPayload,
          mem := mem,
          aw := aw })
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2516⟩ : UInt256)
      (innerLen :: dstData :: (⟨0⟩ : UInt256) :: uidPayload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      Inv 0 s' ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2568⟩ : UInt256)
        (attesterMultiRevokeEncoderInnerStack innerLen tail s')
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeEncoderInnerStack innerLen tail
  let memOf : AttesterMultiRevokeEncoderInnerState → ByteArray := fun s => s.mem
  let awOf : AttesterMultiRevokeEncoderInnerState → UInt256 := fun s => s.aw
  have hexit :
      ∀ s, Inv 0 s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2516⟩ : UInt256) (stk s) (memOf s) (awOf s)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2568⟩ : UInt256) (stk s) (memOf s) (awOf s)
            ByteArray.empty (cA, σ) k' C' := by
    intro s hInv k C rd
    have hidxLen : s.innerIdx = innerLen := by
      rw [hidx 0 s hInv]
      simpa using (u256_ofNat_toNat innerLen)
    have hlt : UInt256.lt s.innerIdx innerLen = (⟨0⟩ : UInt256) := by
      rw [hidxLen]
      exact ult_zero (a := innerLen) (b := innerLen) (by rfl)
    exact attesterX_multiRevokeEncoderInnerLoopExitGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerLen := innerLen) (dstData := s.dstData) (innerIdx := s.innerIdx)
      (uidPayload := s.uidPayload) (tail := tail) (mem := s.mem) (aw := s.aw)
      (k := k) (C := C) htail hlt
      (by simpa [stk, memOf, awOf, attesterMultiRevokeEncoderInnerStack] using rd)
  have hbody :
      ∀ n s, Inv (n + 1) s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2516⟩ : UInt256) (stk s) (memOf s) (awOf s)
          ByteArray.empty (cA, σ) k C →
        ∃ s' k' C',
          Inv n s' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2516⟩ : UInt256) (stk s') (memOf s') (awOf s')
            ByteArray.empty (cA, σ) k' C' := by
    intro n s hInv k C rd
    let s' := attesterMultiRevokeEncoderInnerStepState s
    have hidxNat : s.innerIdx.toNat = innerLen.toNat - (n + 1) := by
      rw [hidx (n + 1) s hInv]
      exact ulit_toNat' (innerLen.toNat - (n + 1))
        (lt_of_le_of_lt (Nat.sub_le _ _) innerLen.val.isLt)
    have hltNat : s.innerIdx.toNat < innerLen.toNat := by
      have hnle : n + 1 ≤ innerLen.toNat := hle (n + 1) s hInv
      omega
    have hlt : UInt256.lt s.innerIdx innerLen = (⟨1⟩ : UInt256) :=
      ult_one hltNat
    obtain ⟨k1, C1, rd2525⟩ :=
      attesterX_multiRevokeEncoderInnerLoopGuard
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (innerLen := innerLen) (dstData := s.dstData) (innerIdx := s.innerIdx)
        (uidPayload := s.uidPayload) (tail := tail) (mem := s.mem) (aw := s.aw)
        (k := k) (C := C) htail hlt
        (by simpa [stk, memOf, awOf, attesterMultiRevokeEncoderInnerStack] using rd)
    obtain ⟨k2, C2, rdNext⟩ :=
      attesterX_multiRevokeEncoderInnerLoopStep
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (innerLen := innerLen) (dstData := s.dstData) (innerIdx := s.innerIdx)
        (uidPayload := s.uidPayload) (tail := tail) (mem := s.mem) (aw := s.aw)
        (k := k1) (C := C1) htail rd2525
    refine ⟨s', k2, C2, hstep n s hInv, ?_⟩
    simpa [s', stk, memOf, awOf, attesterMultiRevokeEncoderInnerStack,
      attesterMultiRevokeEncoderInnerStepState] using rdNext
  let s0 : AttesterMultiRevokeEncoderInnerState :=
    { dstData := dstData,
      innerIdx := (⟨0⟩ : UInt256),
      uidPayload := uidPayload,
      mem := mem,
      aw := aw }
  obtain ⟨s', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨2516⟩ : UInt256)) (exit := (⟨2568⟩ : UInt256))
      Inv stk memOf awOf stk memOf awOf hexit hbody
      innerLen.toNat s0 hInv0 k C
      (by
        simpa [s0, stk, memOf, awOf, attesterMultiRevokeEncoderInnerStack]
          using rd)
  exact ⟨s', k', C', hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeEncoderInnerLoopExitToOuterLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {innerLen dstData innerIdx uidPayload idx srcHead len dstHead endPtr
      scratch dst src ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2568⟩ : UInt256)
      (innerLen :: dstData :: innerIdx :: uidPayload :: idx :: srcHead ::
        len :: dstHead :: endPtr :: scratch :: dst :: src :: ret :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2460⟩ : UInt256)
        (((⟨1⟩ : UInt256) + idx) :: ((⟨32⟩ : UInt256) + srcHead) ::
          len :: ((⟨32⟩ : UInt256) + dstHead) :: dstData :: scratch ::
          dst :: src :: ret :: tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa using
      evm_run rd with [
        raw jumpdest (by attester_decode_at v, ⟨2568⟩, 0x5b, .JUMPDEST) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2569⟩, 0x50, .POP) (by evm_ov),
        raw swap7 (by attester_decode_at v, ⟨2570⟩, 0x96, .SWAP7) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2571⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2572⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2573⟩, 0x50, .POP) (by evm_ov),
        raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2574⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw swap4 (by attester_decode_at v, ⟨2576⟩, 0x93, .SWAP4) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨2577⟩, 0x84, .DUP5) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2578⟩, 0x01, .ADD) (by evm_ov),
        raw swap4 (by attester_decode_at v, ⟨2579⟩, 0x93, .SWAP4) (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2580⟩, 0x91, .SWAP2) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2581⟩, 0x90, .SWAP1) (by evm_ov),
        raw swap2 (by attester_decode_at v, ⟨2582⟩, 0x91, .SWAP2) (by evm_ov),
        raw add (by attester_decode_at v, ⟨2583⟩, 0x01, .ADD) (by evm_ov),
        raw swap1 (by attester_decode_at v, ⟨2584⟩, 0x90, .SWAP1) (by evm_ov),
        raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2585⟩, 0x60, (.Push .PUSH1))
          (by evm_ov),
        raw add (by attester_decode_at v, ⟨2587⟩, 0x01, .ADD) (by evm_ov),
        raw push2 ⟨2460⟩ (by attester_decode_at v, ⟨2588⟩, 0x61, (.Push .PUSH2))
          (by evm_ov),
        raw jump (by attester_decode_at v, ⟨2591⟩, 0x56, .JUMP)
          (attesterMultiRevokeEncodeOuterLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeEncoderOuterLoopExitGuard
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt idx len = ⟨0⟩)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2460⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
        tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2592⟩ : UInt256)
        (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
          tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨2460⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2461⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2462⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨2463⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2464⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2592⟩ (by attester_decode_at v, ⟨2465⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2468⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide)
      (attesterMultiRevokeEncodeOuterExitJumpdest v) (by evm_ov)]⟩

structure AttesterMultiRevokeEncoderOuterState where
  idx : UInt256
  srcHead : UInt256
  dstHead : UInt256
  endPtr : UInt256
  mem : ByteArray
  aw : UInt256

def attesterMultiRevokeEncoderOuterStack
    (len scratch dst src ret : UInt256) (tail : List UInt256)
    (s : AttesterMultiRevokeEncoderOuterState) : List UInt256 :=
  s.idx :: s.srcHead :: len :: s.dstHead :: s.endPtr :: scratch :: dst :: src :: ret ::
    tail

def attesterMultiRevokeEncoderOuterInnerLen
    (dst : UInt256) (s : AttesterMultiRevokeEncoderOuterState) : UInt256 :=
  let mem1 := attesterMultiRevokeEncoderOuterOffsetMem s.mem s.dstHead s.endPtr dst
  let aw1 := attesterMultiRevokeEncoderOuterOffsetAw s.aw s.dstHead
  let srcWord := attesterMultiRevokeEncoderOuterSrcWord mem1 aw1 s.srcHead
  let aw2 := attesterMultiRevokeEncoderOuterSrcAw aw1 s.srcHead
  let schemaWord := attesterMultiRevokeEncoderOuterSchemaWord mem1 aw2 srcWord
  let aw3 := attesterMultiRevokeEncoderOuterSchemaAw aw2 srcWord
  let mem2 := attesterMultiRevokeEncoderOuterSchemaMem mem1 s.endPtr schemaWord
  let aw4 := attesterMultiRevokeEncoderOuterSchemaStoreAw aw3 s.endPtr
  let uidsPtr := attesterMultiRevokeEncoderOuterUidsPtrWord mem2 aw4 srcWord
  let aw5 := attesterMultiRevokeEncoderOuterUidsPtrAw aw4 srcWord
  let mem3 := attesterMultiRevokeEncoderOuterUidsOffsetMem mem2 s.endPtr
  let aw6 := attesterMultiRevokeEncoderOuterUidsOffsetAw aw5 s.endPtr
  attesterMultiRevokeEncoderOuterUidsLenWord mem3 aw6 uidsPtr

def attesterMultiRevokeEncoderOuterInnerInitialState
    (dst : UInt256) (s : AttesterMultiRevokeEncoderOuterState) :
    AttesterMultiRevokeEncoderInnerState :=
  let mem1 := attesterMultiRevokeEncoderOuterOffsetMem s.mem s.dstHead s.endPtr dst
  let aw1 := attesterMultiRevokeEncoderOuterOffsetAw s.aw s.dstHead
  let srcWord := attesterMultiRevokeEncoderOuterSrcWord mem1 aw1 s.srcHead
  let aw2 := attesterMultiRevokeEncoderOuterSrcAw aw1 s.srcHead
  let schemaWord := attesterMultiRevokeEncoderOuterSchemaWord mem1 aw2 srcWord
  let aw3 := attesterMultiRevokeEncoderOuterSchemaAw aw2 srcWord
  let mem2 := attesterMultiRevokeEncoderOuterSchemaMem mem1 s.endPtr schemaWord
  let aw4 := attesterMultiRevokeEncoderOuterSchemaStoreAw aw3 s.endPtr
  let uidsPtr := attesterMultiRevokeEncoderOuterUidsPtrWord mem2 aw4 srcWord
  let aw5 := attesterMultiRevokeEncoderOuterUidsPtrAw aw4 srcWord
  let mem3 := attesterMultiRevokeEncoderOuterUidsOffsetMem mem2 s.endPtr
  let aw6 := attesterMultiRevokeEncoderOuterUidsOffsetAw aw5 s.endPtr
  let uidsLen := attesterMultiRevokeEncoderOuterUidsLenWord mem3 aw6 uidsPtr
  let aw7 := attesterMultiRevokeEncoderOuterUidsLenAw aw6 uidsPtr
  let mem4 := attesterMultiRevokeEncoderOuterUidsLenMem mem3 s.endPtr uidsLen
  let aw8 := attesterMultiRevokeEncoderOuterUidsLenStoreAw aw7 s.endPtr
  { dstData := s.endPtr + ⟨96⟩,
    innerIdx := (⟨0⟩ : UInt256),
    uidPayload := (⟨32⟩ : UInt256) + uidsPtr,
    mem := mem4,
    aw := aw8 }

def attesterMultiRevokeEncoderOuterBodyNextState
    (s : AttesterMultiRevokeEncoderOuterState)
    (inner : AttesterMultiRevokeEncoderInnerState) :
    AttesterMultiRevokeEncoderOuterState :=
  { idx := (⟨1⟩ : UInt256) + s.idx,
    srcHead := (⟨32⟩ : UInt256) + s.srcHead,
    dstHead := (⟨32⟩ : UInt256) + s.dstHead,
    endPtr := inner.dstData,
    mem := inner.mem,
    aw := inner.aw }

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeEncoderOuterLoopBodyWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {len scratch dst src ret : UInt256}
    {tail : List UInt256} {outer : AttesterMultiRevokeEncoderOuterState} {k C n : ℕ}
    (htail : tail.length ≤ 1000)
    (hinnerTail : tail.length + 9 ≤ 1000)
    (OuterInv : Nat → AttesterMultiRevokeEncoderOuterState → Prop)
    (InnerInv : Nat → AttesterMultiRevokeEncoderInnerState → Prop)
    (hinnerIdx : ∀ n inner,
      InnerInv n inner →
        inner.innerIdx =
          UInt256.ofNat ((attesterMultiRevokeEncoderOuterInnerLen dst outer).toNat - n))
    (hinnerLe : ∀ n inner,
      InnerInv n inner →
        n ≤ (attesterMultiRevokeEncoderOuterInnerLen dst outer).toNat)
    (hinnerStep :
      ∀ n inner, InnerInv (n + 1) inner →
        InnerInv n (attesterMultiRevokeEncoderInnerStepState inner))
    (hinnerInit :
      InnerInv (attesterMultiRevokeEncoderOuterInnerLen dst outer).toNat
        (attesterMultiRevokeEncoderOuterInnerInitialState dst outer))
    (houterNext :
      ∀ inner, InnerInv 0 inner →
        OuterInv n (attesterMultiRevokeEncoderOuterBodyNextState outer inner))
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2469⟩ : UInt256)
      (attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail outer)
      outer.mem outer.aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      OuterInv n s' ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2460⟩ : UInt256)
        (attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail s')
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let innerTail : List UInt256 :=
    outer.idx :: outer.srcHead :: len :: outer.dstHead :: outer.endPtr :: scratch :: dst :: src ::
      ret :: tail
  obtain ⟨k1, C1, rd2516⟩ :=
    attesterX_multiRevokeEncoderOuterLoopToInnerLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := outer.idx) (srcHead := outer.srcHead) (len := len)
      (dstHead := outer.dstHead) (endPtr := outer.endPtr) (scratch := scratch)
      (dst := dst) (src := src) (ret := ret) (tail := tail)
      (mem := outer.mem) (aw := outer.aw) (k := k) (C := C) htail
      (by simpa [attesterMultiRevokeEncoderOuterStack] using rd)
  obtain ⟨innerDone, k2, C2, hinnerDone, rd2568⟩ :=
    attesterX_multiRevokeEncoderInnerLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerLen := attesterMultiRevokeEncoderOuterInnerLen dst outer)
      (dstData := (attesterMultiRevokeEncoderOuterInnerInitialState dst outer).dstData)
      (uidPayload := (attesterMultiRevokeEncoderOuterInnerInitialState dst outer).uidPayload)
      (tail := innerTail)
      (mem := (attesterMultiRevokeEncoderOuterInnerInitialState dst outer).mem)
      (aw := (attesterMultiRevokeEncoderOuterInnerInitialState dst outer).aw)
      (k := k1) (C := C1) hinnerTail InnerInv hinnerIdx hinnerLe hinnerStep
      hinnerInit
      (by
        simpa [innerTail, attesterMultiRevokeEncoderOuterInnerLen,
          attesterMultiRevokeEncoderOuterInnerInitialState] using rd2516)
  obtain ⟨k3, C3, rd2460⟩ :=
    attesterX_multiRevokeEncoderInnerLoopExitToOuterLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerLen := attesterMultiRevokeEncoderOuterInnerLen dst outer)
      (dstData := innerDone.dstData) (innerIdx := innerDone.innerIdx)
      (uidPayload := innerDone.uidPayload)
      (idx := outer.idx) (srcHead := outer.srcHead) (len := len)
      (dstHead := outer.dstHead) (endPtr := outer.endPtr) (scratch := scratch)
      (dst := dst) (src := src) (ret := ret) (tail := tail)
      (mem := innerDone.mem) (aw := innerDone.aw)
      (k := k2) (C := C2) htail
      (by simpa [innerTail] using rd2568)
  refine ⟨attesterMultiRevokeEncoderOuterBodyNextState outer innerDone, k3, C3,
    houterNext innerDone hinnerDone, ?_⟩
  simpa [attesterMultiRevokeEncoderOuterStack,
    attesterMultiRevokeEncoderOuterBodyNextState] using rd2460

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeEncoderOuterLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (Inv : Nat → AttesterMultiRevokeEncoderOuterState → Prop)
    (hidx : ∀ n s, Inv n s → s.idx = UInt256.ofNat (len.toNat - n))
    (hle : ∀ n s, Inv n s → n ≤ len.toNat)
    (hbody :
      ∀ n s, Inv (n + 1) s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2469⟩ : UInt256)
          (attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail s)
          s.mem s.aw ByteArray.empty (cA, σ) k C →
        ∃ s' k' C',
          Inv n s' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2460⟩ : UInt256)
            (attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail s')
            s'.mem s'.aw ByteArray.empty (cA, σ) k' C')
    (hInv0 :
      Inv len.toNat
        { idx := idx,
          srcHead := srcHead,
          dstHead := dstHead,
          endPtr := endPtr,
          mem := mem,
          aw := aw })
    (hidx0 : idx = (⟨0⟩ : UInt256))
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2460⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src :: ret ::
        tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      Inv 0 s' ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨2592⟩ : UInt256)
        (attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail s')
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeEncoderOuterStack len scratch dst src ret tail
  let memOf : AttesterMultiRevokeEncoderOuterState → ByteArray := fun s => s.mem
  let awOf : AttesterMultiRevokeEncoderOuterState → UInt256 := fun s => s.aw
  have hexit :
      ∀ s, Inv 0 s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2460⟩ : UInt256) (stk s) (memOf s) (awOf s)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2592⟩ : UInt256) (stk s) (memOf s) (awOf s)
            ByteArray.empty (cA, σ) k' C' := by
    intro s hInv k C rd
    have hidxLen : s.idx = len := by
      rw [hidx 0 s hInv]
      simpa using (u256_ofNat_toNat len)
    have hlt : UInt256.lt s.idx len = (⟨0⟩ : UInt256) := by
      rw [hidxLen]
      exact ult_zero (a := len) (b := len) (by rfl)
    exact attesterX_multiRevokeEncoderOuterLoopExitGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := s.idx) (srcHead := s.srcHead) (len := len) (dstHead := s.dstHead)
      (endPtr := s.endPtr) (scratch := scratch) (dst := dst) (src := src)
      (ret := ret) (tail := tail) (mem := s.mem) (aw := s.aw)
      (k := k) (C := C) htail hlt
      (by simpa [stk, memOf, awOf, attesterMultiRevokeEncoderOuterStack] using rd)
  have hstep :
      ∀ n s, Inv (n + 1) s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2460⟩ : UInt256) (stk s) (memOf s) (awOf s)
          ByteArray.empty (cA, σ) k C →
        ∃ s' k' C',
          Inv n s' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2460⟩ : UInt256) (stk s') (memOf s') (awOf s')
            ByteArray.empty (cA, σ) k' C' := by
    intro n s hInv k C rd
    have hidxNat : s.idx.toNat = len.toNat - (n + 1) := by
      rw [hidx (n + 1) s hInv]
      exact ulit_toNat' (len.toNat - (n + 1))
        (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
    have hltNat : s.idx.toNat < len.toNat := by
      have hnle : n + 1 ≤ len.toNat := hle (n + 1) s hInv
      omega
    have hlt : UInt256.lt s.idx len = (⟨1⟩ : UInt256) :=
      ult_one hltNat
    obtain ⟨k1, C1, rd2469⟩ :=
      attesterX_multiRevokeEncoderOuterLoopGuard
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (idx := s.idx) (srcHead := s.srcHead) (len := len) (dstHead := s.dstHead)
        (endPtr := s.endPtr) (scratch := scratch) (dst := dst) (src := src)
        (ret := ret) (tail := tail) (mem := s.mem) (aw := s.aw)
        (k := k) (C := C) htail hlt
        (by simpa [stk, memOf, awOf, attesterMultiRevokeEncoderOuterStack] using rd)
    obtain ⟨s', k2, C2, hInv', rdNext⟩ :=
      hbody n s hInv k1 C1
        (by simpa [stk, attesterMultiRevokeEncoderOuterStack] using rd2469)
    exact ⟨s', k2, C2, hInv', by
      simpa [stk, memOf, awOf, attesterMultiRevokeEncoderOuterStack] using rdNext⟩
  let s0 : AttesterMultiRevokeEncoderOuterState :=
    { idx := idx,
      srcHead := srcHead,
      dstHead := dstHead,
      endPtr := endPtr,
      mem := mem,
      aw := aw }
  obtain ⟨s', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨2460⟩ : UInt256)) (exit := (⟨2592⟩ : UInt256))
      Inv stk memOf awOf stk memOf awOf hexit hstep
      len.toNat s0 hInv0 k C
      (by
        simpa [s0, stk, memOf, awOf, attesterMultiRevokeEncoderOuterStack, hidx0]
          using rd)
  exact ⟨s', k', C', hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeEncoderOuterLoopExitToReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2592⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src ::
        (⟨775⟩ : UInt256) :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨775⟩ : UInt256)
        (endPtr :: tail)
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa using
      evm_run rd with [
        raw jumpdest (by attester_decode_at v, ⟨2592⟩, 0x5b, .JUMPDEST) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2593⟩, 0x50, .POP) (by evm_ov),
        raw swap3 (by attester_decode_at v, ⟨2594⟩, 0x92, .SWAP3) (by evm_ov),
        raw swap7 (by attester_decode_at v, ⟨2595⟩, 0x96, .SWAP7) (by evm_ov),
        raw swap6 (by attester_decode_at v, ⟨2596⟩, 0x95, .SWAP6) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2597⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2598⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2599⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2600⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2601⟩, 0x50, .POP) (by evm_ov),
        raw pop (by attester_decode_at v, ⟨2602⟩, 0x50, .POP) (by evm_ov),
        raw jump (by attester_decode_at v, ⟨2603⟩, 0x56, .JUMP)
          (attesterMultiRevokeEncoderReturnJumpdest v) (by evm_ov)]⟩

theorem attester_u256_ofNat_sub_succ_add_one
    {m n : Nat} (hle : n + 1 ≤ m) (hm : m < UInt256.size) :
    (UInt256.ofNat (m - (n + 1)) + (⟨1⟩ : UInt256)) =
      UInt256.ofNat (m - n) := by
  apply u256_inj
  rw [uadd_toNat]
  rw [ulit_toNat' (m - (n + 1)) (by omega)]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [ulit_toNat' (m - n) (by omega)]
  omega

theorem attester_u256_one_add_ofNat_sub_succ
    {m n : Nat} (hle : n + 1 ≤ m) (hm : m < UInt256.size) :
    ((⟨1⟩ : UInt256) + UInt256.ofNat (m - (n + 1))) =
      UInt256.ofNat (m - n) := by
  rw [u256_add_comm]
  exact attester_u256_ofNat_sub_succ_add_one hle hm

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeEncoderLoopToReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hinnerTail : tail.length + 9 ≤ 1000)
    (hidx0 : idx = (⟨0⟩ : UInt256))
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2460⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src ::
        (⟨775⟩ : UInt256) :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' : AttesterMultiRevokeEncoderOuterState, ∃ k' C',
      s'.idx = len ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨775⟩ : UInt256)
        (s'.endPtr :: tail)
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let OuterInv : Nat → AttesterMultiRevokeEncoderOuterState → Prop :=
    fun n s => s.idx = UInt256.ofNat (len.toNat - n) ∧ n ≤ len.toNat
  have hidx :
      ∀ n s, OuterInv n s → s.idx = UInt256.ofNat (len.toNat - n) := by
    intro n s h
    exact h.1
  have hle : ∀ n s, OuterInv n s → n ≤ len.toNat := by
    intro n s h
    exact h.2
  have hbody :
      ∀ n s, OuterInv (n + 1) s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2469⟩ : UInt256)
          (attesterMultiRevokeEncoderOuterStack len scratch dst src (⟨775⟩ : UInt256)
            tail s)
          s.mem s.aw ByteArray.empty (cA, σ) k C →
        ∃ s' k' C',
          OuterInv n s' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2460⟩ : UInt256)
            (attesterMultiRevokeEncoderOuterStack len scratch dst src (⟨775⟩ : UInt256)
              tail s')
            s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
    intro n s hInv k C rdBody
    let innerLen := attesterMultiRevokeEncoderOuterInnerLen dst s
    let InnerInv : Nat → AttesterMultiRevokeEncoderInnerState → Prop :=
      fun m inner => inner.innerIdx = UInt256.ofNat (innerLen.toNat - m) ∧
        m ≤ innerLen.toNat
    have hinnerIdx :
        ∀ m inner, InnerInv m inner →
          inner.innerIdx =
            UInt256.ofNat ((attesterMultiRevokeEncoderOuterInnerLen dst s).toNat - m) := by
      intro m inner h
      simpa [innerLen] using h.1
    have hinnerLe :
        ∀ m inner, InnerInv m inner →
          m ≤ (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat := by
      intro m inner h
      simpa [innerLen] using h.2
    have hinnerStep :
        ∀ m inner, InnerInv (m + 1) inner →
          InnerInv m (attesterMultiRevokeEncoderInnerStepState inner) := by
      intro m inner h
      constructor
      · change
          (inner.innerIdx + (⟨1⟩ : UInt256)) =
            UInt256.ofNat (innerLen.toNat - m)
        rw [h.1]
        exact attester_u256_ofNat_sub_succ_add_one h.2 innerLen.val.isLt
      · omega
    have hinnerInit :
        InnerInv (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat
          (attesterMultiRevokeEncoderOuterInnerInitialState dst s) := by
      constructor
      · dsimp [attesterMultiRevokeEncoderOuterInnerInitialState]
        rw [show
            innerLen.toNat - (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat = 0 by
          simp [innerLen]]
        simpa using (u256_ofNat_toNat (⟨0⟩ : UInt256)).symm
      · simp [innerLen]
    have houterNext :
        ∀ inner, InnerInv 0 inner →
          OuterInv n (attesterMultiRevokeEncoderOuterBodyNextState s inner) := by
      intro inner _hinner
      constructor
      · change
          ((⟨1⟩ : UInt256) + s.idx) =
            UInt256.ofNat (len.toNat - n)
        rw [hInv.1]
        exact attester_u256_one_add_ofNat_sub_succ hInv.2 len.val.isLt
      · omega
    exact
      attesterX_multiRevokeEncoderOuterLoopBodyWithStateInvariant
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (len := len) (scratch := scratch) (dst := dst) (src := src)
        (ret := (⟨775⟩ : UInt256)) (tail := tail) (outer := s)
        (k := k) (C := C) (n := n)
        htail hinnerTail OuterInv InnerInv hinnerIdx hinnerLe hinnerStep
        hinnerInit houterNext rdBody
  have hInv0 :
      OuterInv len.toNat
        { idx := idx,
          srcHead := srcHead,
          dstHead := dstHead,
          endPtr := endPtr,
          mem := mem,
          aw := aw } := by
    constructor
    · rw [hidx0]
      change (⟨0⟩ : UInt256) = UInt256.ofNat (len.toNat - len.toNat)
      rw [Nat.sub_self]
      simpa using (u256_ofNat_toNat (⟨0⟩ : UInt256)).symm
    · omega
  obtain ⟨s', k1, C1, hInvFinal, rd2592⟩ :=
    attesterX_multiRevokeEncoderOuterLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (srcHead := srcHead) (len := len) (dstHead := dstHead)
      (endPtr := endPtr) (scratch := scratch) (dst := dst) (src := src)
      (ret := (⟨775⟩ : UInt256)) (tail := tail) (mem := mem) (aw := aw)
      (k := k) (C := C) htail OuterInv hidx hle hbody hInv0 hidx0 rd
  obtain ⟨k2, C2, rd775⟩ :=
    attesterX_multiRevokeEncoderOuterLoopExitToReturn
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := s'.idx) (srcHead := s'.srcHead) (len := len)
      (dstHead := s'.dstHead) (endPtr := s'.endPtr) (scratch := scratch)
      (dst := dst) (src := src) (tail := tail) (mem := s'.mem) (aw := s'.aw)
      (k := k1) (C := C1) htail rd2592
  refine ⟨s', k2, C2, ?_, rd775⟩
  rw [hInvFinal.1]
  simpa using (u256_ofNat_toNat len)

end Benchmarks.EAS.Attester
