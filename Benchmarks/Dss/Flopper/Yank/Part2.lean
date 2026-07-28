import Benchmarks.Dss.Flopper.Yank.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper
theorem flopperYankX_suckCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1050 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [yankIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let vow := flopperAddressReturnWord ⟨9⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flopperSlotWord (auctionBidSlot id) σ I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankSuckEndPtr :: yankSuckSelectorWord ::
          vat :: id :: ⟨334⟩ :: sel :: [])
        (yankSuckCalldataMem vow guy bid memMap) (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat vat.toNat)) "suck" 0
        [.address (AccountAddress.ofNat vow.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro id memHash memMap vat vow guy bid
  have hmemHash : memHash.size = 96 := by
    simpa [memHash, id] using
      twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hmemMap : memMap.size = 96 := by
    have hread64Hash : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      simpa [memHash, id] using
        twoWordHashMem_read64 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64
    simpa [memMap, id, memHash] using twoWordHashMem_size_96 id ⟨1⟩ hmemHash
  have hvatCanon : vat.toNat < EVM.addressModulus := by
    simpa [vat, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord ⟨2⟩ σ I)
  have hvowCanon : vow.toNat < EVM.addressModulus := by
    simpa [vow, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord ⟨9⟩ σ I)
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ I)
  obtain ⟨_, _, rd1148⟩ := flopperYankX_toSuckExtcodesizeGuard rd1050
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1148⟩) (okPc := ⟨1160⟩) rd1148
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k1164, C1164, hΘpack, rd1164raw,
      houtsz⟩ :=
    RD.call rd1163 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1164, C1164, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          yankSuckOutPtr.toNat yankSuckInSize.toNat)
          yankSuckOutPtr.toNat yankSuckOutSize.toNat) = UInt256.ofNat 8 := by
      unfold yankSuckOutPtr yankSuckInSize yankSuckOutSize
      native_decide
    have hmin : (min yankSuckOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold yankSuckOutSize
      rfl
    have rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: yankSuckEndPtr :: yankSuckSelectorWord ::
          vat :: id :: ⟨334⟩ :: sel :: [])
        (out.write 0 (yankSuckCalldataMem vow guy bid memMap) yankSuckOutPtr.toNat
          (min yankSuckOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k1164 C1164 :=
      haw ▸ rd1164raw
    rw [hmin, byteArray_write_len_zero] at rd1164
    exact rd1164
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := vat)
      (mem := yankSuckCalldataMem vow guy bid memMap)
      (inOff := yankSuckOutPtr) (inSize := yankSuckInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      flopperAddressWord_address_eq_target
      (yankSuckEncode_eq vow guy bid hmemMap hvowCanon hguyCanon) ?_
    simpa [initState, hperm] using hΘ

theorem flopperYankX_suckCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flopperAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd1050 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1050⟩
      [yankIdWord I, ⟨334⟩, sel]
      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := yankIdWord I
    let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memMap := twoWordHashMem id ⟨1⟩ memHash
    let vat := flopperAddressReturnWord ⟨2⟩ σ I
    let vow := flopperAddressReturnWord ⟨9⟩ σ I
    let guy := flopperAddressReturnWord (auctionPackedSlot id) σ I
    let bid := flopperSlotWord (auctionBidSlot id) σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (⟨0⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
        vat :: id :: ⟨334⟩ :: sel :: [])
      (yankSuckCalldataMem vow guy bid memMap) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  intro id memHash memMap vat vow guy bid
  obtain ⟨_, _, rd1148⟩ := flopperYankX_toSuckExtcodesizeGuard rd1050
  obtain ⟨gasWord, _, _, rd1163⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1148⟩) (okPc := ⟨1160⟩) rd1148
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k1164, C1164, rd1164raw⟩ :=
    RD.callDepthLimit rd1163 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k1164, C1164, ?_⟩
  have hmin : (min yankSuckOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold yankSuckOutSize
    rfl
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        yankSuckOutPtr.toNat yankSuckInSize.toNat)
        yankSuckOutPtr.toNat yankSuckOutSize.toNat) = UInt256.ofNat 8 := by
    unfold yankSuckOutPtr yankSuckInSize yankSuckOutSize
    native_decide
  simpa [yankSuckOutPtr, yankSuckInSize, yankSuckOutSize, hmin,
    byteArray_write_len_zero, haw] using rd1164raw

theorem flopperYankX_suckCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (⟨0⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: yankIdWord I :: ⟨334⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1164⟩) (okPc := ⟨1180⟩) rd1164
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem flopperYankX_suckCallSuccessDelete
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel status : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hstatus : status ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      (status :: yankSuckEndPtr :: yankSuckSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: yankIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ' (auctionBidSlot (yankIdWord I)) ⟨0⟩)
          (auctionLotSlot (yankIdWord I)) ⟨0⟩)
        (auctionPackedSlot (yankIdWord I)) ⟨0⟩)
      ByteArray.empty := by
  have rd1165 := rd1164.iszero (by native_decide) (by evm_ov)
  have rd1166 := rd1165.dup1 (by native_decide) (by evm_ov)
  have rd1167 := rd1166.iszero (by native_decide) (by evm_ov)
  have rd1170 := rd1167.push2 ⟨1180⟩ (by native_decide) (by evm_ov)
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hstatus]
    decide
  have rd1180 := rd1170.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  exact RD.flopperAuctionDeleteTail hperm
    (by native_decide) (by native_decide) (by native_decide) (by simp) rd1180

theorem flopperYankBodyCoreStillLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hlive (by
      have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
      rw [hword, hzero])
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperYankBodyReverts_stillLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
  exact (flopperYankX_stillLive (g := Sat256.ofUInt256 g) hlive
      (flopperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperYankBodyCoreGuyNotSet
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I = ⟨0⟩ := by
    have hword :=
      flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts
        (auctionPackedSlot (yankIdWord I))
    rw [← hword]
    exact hguy
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperYankBodyReverts_guyNotSet evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
  exact (flopperYankX_guyNotSet (g := Sat256.ofUInt256 g) hlive hguy
      (flopperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperYankBodyCoreSuckNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      have hword :=
        flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts
          (auctionPackedSlot (yankIdWord I))
      rw [hword, hzero])
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) = ⟨0⟩ :=
    flopperCodeSize_zero_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hnoCode
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperYankBodyReverts_suckNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hnoCodeSolm)
  obtain ⟨_, _, rd1050⟩ :=
    flopperYankX_readyToSuck (g := Sat256.ofUInt256 g) hlive hguy
      (flopperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  exact (flopperYankX_suckNoCode (g := Sat256.ofUInt256 g) hnoCode rd1050)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperYankBodyCoreSuckCallFailure
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
      (⟨0⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: yankIdWord I :: ⟨334⟩ :: sel :: [])
      (yankSuckCalldataMem
        (flopperAddressReturnWord ⟨9⟩ σ_evm I)
        (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
        (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
        (twoWordHashMem (yankIdWord I) ⟨1⟩
          (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ σ_evm I).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (houtSize : out.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hpostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hvowEq :
      flopperAddressReturnWord ⟨9⟩ σ_evm I =
        flopperAddressReturnWord ⟨9⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨9⟩
  have hguyEq :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I =
        flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (yankIdWord I))
  have hbidEq :
      flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I =
        flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I :=
    flopperSlotWord_accountMapEquiv hAccounts (auctionBidSlot (yankIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ σ_solm I).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I).toNat)]
        (false, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hvatEq, hvowEq, hguyEq, hbidEq] using hcallSolmRaw
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by rw [hguyEq, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, evmCallSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperYankBodyReverts_suckCallFailure evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  exact (flopperYankX_suckCallFailure rd1164 houtSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperYankBodyCoreSuckCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := yankIdWord I
  let memHash := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memMap := twoWordHashMem id ⟨1⟩ memHash
  let vat := flopperAddressReturnWord ⟨2⟩ σ_solm I
  let vow := flopperAddressReturnWord ⟨9⟩ σ_solm I
  let guy := flopperAddressReturnWord (auctionPackedSlot id) σ_solm I
  let bid := flopperSlotWord (auctionBidSlot id) σ_solm I
  let A_suck := (evmSolm.addAccessedAccount (EVM.address (AccountAddress.ofNat vat.toNat))).substate
  have hmemHash : memHash.size = 96 := by
    simpa [memHash, id] using
      twoWordHashMem_size_96 (yankIdWord I) ⟨1⟩ solcFreePtrMem_size
  have hmemMap : memMap.size = 96 := by
    simpa [memMap, id, memHash] using twoWordHashMem_size_96 id ⟨1⟩ hmemHash
  have hvowCanon : vow.toNat < EVM.addressModulus := by
    simpa [vow, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord ⟨9⟩ σ_solm I)
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flopperAddressReturnWord] using
      solcAddrMask_result_canonical (flopperSlotWord (auctionPackedSlot id) σ_solm I)
  have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
    simpa [evmSolm, initState] using hdepth
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat vat.toNat)) "suck" 0
        [.address (AccountAddress.ofNat vow.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)]
        (false, { evmSolm with substate := A_suck }, ByteArray.empty) true := by
    simpa [A_suck] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (AccountAddress.ofNat vat.toNat)) (name := "suck")
        (args := [.address (AccountAddress.ofNat vow.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)])
        (callPerm := true)
        (calldata := (yankSuckCalldataMem vow guy bid memMap).readWithPadding
          yankSuckOutPtr.toNat yankSuckInSize.toNat)
        (yankSuckEncode_eq vow guy bid hmemMap hvowCanon hguyCanon)
        hdepthInit)
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by
      have hword :=
        flopperAddressReturnWord_accountMapEquiv (I := I) hAccounts
          (auctionPackedSlot (yankIdWord I))
      rw [hword, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body .reverted := by
    simpa [evmSolm, vat, vow, guy, bid, id, flopperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      flopperYankBodyReverts_suckCallFailure evmSolm
        { evmSolm with substate := A_suck } I ByteArray.empty
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  obtain ⟨_, _, rd1050⟩ :=
    flopperYankX_readyToSuck (g := Sat256.ofUInt256 g) hlive hguy
      (flopperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
  obtain ⟨_, _, rd1164⟩ :=
    flopperYankX_suckCallDepthLimit (g := Sat256.ofUInt256 g) hcodeSize hdepth rd1050
  exact (flopperYankX_suckCallFailure rd1164 (by native_decide))
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperYankBodyCoreSuckCallSuccess
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A A' I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (_hsz36 : 36 ≤ I.calldata.size)
    (hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩)
    (hguy : flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flopperAddressReturnWord ⟨2⟩ σ_evm I) ≠ ⟨0⟩)
    (rd1164 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
      (⟨1⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ_evm I :: yankIdWord I :: ⟨334⟩ :: sel :: [])
      (yankSuckCalldataMem
        (flopperAddressReturnWord ⟨9⟩ σ_evm I)
        (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
        (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
        (twoWordHashMem (yankIdWord I) ⟨1⟩
          (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ σ_evm I).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (yankTransition.params.map Param.name)
        (transitionSignature yankTransition).paramTypes I.calldata = some (yankLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hpostCallAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv (hcall := hcall) hAccounts
  let evmCallSolm : EVM.State :=
    { evmSolm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
  have hvatEq :
      flopperAddressReturnWord ⟨2⟩ σ_evm I =
        flopperAddressReturnWord ⟨2⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨2⟩
  have hvowEq :
      flopperAddressReturnWord ⟨9⟩ σ_evm I =
        flopperAddressReturnWord ⟨9⟩ σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts ⟨9⟩
  have hguyEq :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I =
        flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I :=
    flopperAddressReturnWord_accountMapEquiv hAccounts (auctionPackedSlot (yankIdWord I))
  have hbidEq :
      flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I =
        flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I :=
    flopperSlotWord_accountMapEquiv hAccounts (auctionBidSlot (yankIdWord I))
  have hcallSolm :
      typedCallViaEVM config evmSolm
        (EVM.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨2⟩ σ_solm I).toNat))
        "suck" 0
        [.address (AccountAddress.ofNat
          (flopperAddressReturnWord ⟨9⟩ σ_solm I).toNat),
        .address (AccountAddress.ofNat
          (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I).toNat),
        .int (Int.ofNat
          (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_solm I).toNat)]
        (true, evmCallSolm, out) true := by
    simpa [evmSolm, evmCallSolm, hvatEq, hvowEq, hguyEq, hbidEq] using hcallSolmRaw
  have hliveSolmWord : flopperSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
    have hword := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨8⟩
    rw [← hword]
    exact hlive
  have hguySolm :
      flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hguy (by rw [hguyEq, hzero])
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (flopperAddressReturnWord ⟨2⟩ σ_solm I) ≠ ⟨0⟩ :=
    flopperCodeSize_ne_accountMapEquiv_addressSlot hAccounts ⟨2⟩ hcodeSize
  have hbody :
      ExecTransitionBody config contract evmSolm (yankLocals I)
        yankTransition.body
        (.returned { contract := contract, locals := yankSuckLocals I }
          (yankDeletePostState evmCallSolm I) none) := by
    simpa [evmSolm, evmCallSolm, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperYankBodyReturns_suckCallSuccess evmSolm evmCallSolm I out
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolmWord
        (by simpa [evmSolm, initState] using hguySolm)
        (by simpa [evmSolm, initState] using hcodeSizeSolm)
        hcallSolm
  have hret :=
    flopperYankX_suckCallSuccessDelete
      (g := Sat256.ofUInt256 g) (σ := σ_evm) (sel := sel) hperm
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) rd1164
  have hRuntimeDeleteEquiv :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ')
        (yankRuntimeDeleteAccountMap I σ'_solm) := by
    unfold yankRuntimeDeleteAccountMap
    exact accountMapEquiv_sstoreAccountMap_three I.codeOwner I.codeOwner I.codeOwner
      (auctionBidSlot (yankIdWord I)) ⟨0⟩
      (auctionLotSlot (yankIdWord I)) ⟨0⟩
      (auctionPackedSlot (yankIdWord I)) ⟨0⟩
      hpostCallAccounts
  have hDeleteSolm :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ'_solm)
        (yankDeletePostState evmCallSolm I).accountMap := by
    simpa [evmCallSolm] using
      yankDeletePostState_accountMapEquiv evmCallSolm I
        (by simp [evmCallSolm, evmSolm, initState])
  have hFinalAccounts :
      accountMapEquiv (yankRuntimeDeleteAccountMap I σ')
        (yankDeletePostState evmCallSolm I).accountMap :=
    accountMapEquiv.trans hRuntimeDeleteEquiv hDeleteSolm
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [yankDeletePostState, yankDeleteAfterTic, yankDeleteAfterGuy,
        yankDeleteAfterLot, yankDeleteAfterBid, evmCallSolm, evmSolm, initState,
        storageStore_createdAccounts])
    (by simpa [yankRuntimeDeleteAccountMap] using hFinalAccounts)
    (by
      simpa [yankTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperYankBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some yankTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flopperYankX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_yank_none_short hsz4 hshort)

theorem flopperYankBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 19))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 19) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
    flopperDispatchYank hsel
  have hreach := flopperReachYankBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flopperDecode_yank_ok (I := I) hsz36
    by_cases hlive : flopperSlotWord ⟨8⟩ σ_evm I = ⟨0⟩
    · by_cases hguy :
          flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I = ⟨0⟩
      · exact flopperYankBodyCoreGuyNotSet hcode hsize hwv hsz36 hlive hguy
          hdispatch hdecode hreach hAccounts
      · by_cases hcodeSize :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (flopperAddressReturnWord ⟨2⟩ σ_evm I) = ⟨0⟩
        · exact flopperYankBodyCoreSuckNoCode hcode hsize hwv hsz36 hlive hguy
            hcodeSize hdispatch hdecode hreach hAccounts
        · by_cases hdepthEq : I.depth = 1024
          · exact flopperYankBodyCoreSuckCallDepthLimit hcode hsize hwv hsz36 hlive
              hguy hcodeSize hdepthEq hdispatch hdecode hreach hAccounts
          · have hdepthLt : I.depth.val < 1024 := by
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              by_contra hn
              have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hn
              have hval : I.depth.val = 1024 := by omega
              apply hdepthEq
              apply Fin.ext
              exact hval
            obtain ⟨_, _, rd1050⟩ :=
              flopperYankX_readyToSuck (g := Sat256.ofUInt256 g) hlive hguy
                (flopperYankX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
            obtain ⟨cA', σ', z, out, A', k1164, C1164, rd1164, hcall, houtSize⟩ :=
              flopperYankX_suckCall (g := Sat256.ofUInt256 g) hperm hcodeSize
                hdepthLt rd1050
            by_cases hz : z = true
            · have rd1164True : RD flopperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                  (⟨1⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
                    flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                    yankIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                  (yankSuckCalldataMem
                    (flopperAddressReturnWord ⟨9⟩ σ_evm I)
                    (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
                    (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
                    (twoWordHashMem (yankIdWord I) ⟨1⟩
                      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
                  (UInt256.ofNat 8) out (cA', σ') k1164 C1164 := by
                simpa [hz] using rd1164
              have hcallTrue :
                  typedCallViaEVM config
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat
                      (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                    "suck" 0
                    [.address (AccountAddress.ofNat
                      (flopperAddressReturnWord ⟨9⟩ σ_evm I).toNat),
                    .address (AccountAddress.ofNat
                      (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I))
                        σ_evm I).toNat),
                    .int (Int.ofNat
                      (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
                    (true,
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ', substate := A', createdAccounts := cA' },
                      out) true := by
                simpa [hz] using hcall
              exact flopperYankBodyCoreSuckCallSuccess hcode hsize hperm hwv hsz36
                hlive hguy hcodeSize rd1164True hcallTrue hdispatch hdecode hAccounts
            · have hzFalse : z = false := Bool.eq_false_iff.mpr hz
              have rd1164False : RD flopperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1164⟩
                  (⟨0⟩ :: yankSuckEndPtr :: yankSuckSelectorWord ::
                    flopperAddressReturnWord ⟨2⟩ σ_evm I ::
                    yankIdWord I :: ⟨334⟩ :: flopperSelWord I :: [])
                  (yankSuckCalldataMem
                    (flopperAddressReturnWord ⟨9⟩ σ_evm I)
                    (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I)) σ_evm I)
                    (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I)
                    (twoWordHashMem (yankIdWord I) ⟨1⟩
                      (twoWordHashMem (yankIdWord I) ⟨1⟩ solcFreePtrMem)))
                  (UInt256.ofNat 8) out (cA', σ') k1164 C1164 := by
                simpa [hzFalse] using rd1164
              have hcallFalse :
                  typedCallViaEVM config
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat
                      (flopperAddressReturnWord ⟨2⟩ σ_evm I).toNat))
                    "suck" 0
                    [.address (AccountAddress.ofNat
                      (flopperAddressReturnWord ⟨9⟩ σ_evm I).toNat),
                    .address (AccountAddress.ofNat
                      (flopperAddressReturnWord (auctionPackedSlot (yankIdWord I))
                        σ_evm I).toNat),
                    .int (Int.ofNat
                      (flopperSlotWord (auctionBidSlot (yankIdWord I)) σ_evm I).toNat)]
                    (false,
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ', substate := A', createdAccounts := cA' },
                      out) true := by
                simpa [hzFalse] using hcall
              exact flopperYankBodyCoreSuckCallFailure hcode hsize hwv hsz36 hlive
                hguy hcodeSize rd1164False hcallFalse houtSize hdispatch hdecode hAccounts
    · exact flopperYankBodyCoreStillLive hcode hsize hwv hsz36 hlive
        hdispatch hdecode hreach hAccounts
  · exact flopperYankBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper
