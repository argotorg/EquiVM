import Benchmarks.Dss.Clipper.TakeCallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeJumpDest4676 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4676⟩ : UInt256) = true := by
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

theorem clipperTakeJumpDest4696 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨4696⟩ : UInt256) = true := by
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

theorem RD.clipperTakeClipperCallNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4664 : RD code ee g s0 ⟨4664⟩
      (UInt256.land solcAddrMask who :: UInt256.land solcAddrMask who :: ⟨0⟩ ::
        ⟨128⟩ :: UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat) :: ⟨128⟩ ::
        ⟨0⟩ :: (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ::
        clipperTakeCallbackSelectorSeed :: UInt256.land solcAddrMask who :: dog :: slice ::
        owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask who) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4664⟩) (okPc := ⟨4676⟩)
    rd4664 hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeClipperCallCodeOkGas {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {target : UInt256} {R : List UInt256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4664 : RD code ee g s0 ⟨4664⟩ (target :: target :: R)
      mem aw out (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code ee g s0 ⟨4679⟩
      (gasWord :: target :: R) mem aw out (cA, σ) k' C' := by
  obtain ⟨gasWord, k', C', rd4679⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4664⟩) (okPc := ⟨4676⟩)
      rd4664 hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4676 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) hov
  exact ⟨gasWord, k', C', by simpa using rd4679⟩

theorem RD.clipperTakeClipperCallStep {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4679 : RD code ee g s0 ⟨4679⟩
      (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hdepth : ee.depth.val < 1024) (hov : R.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ ee.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ
            s0.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
            (AccountAddress.ofUInt256 target)
            (toExecute σ (AccountAddress.ofUInt256 target))
            callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
            (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1)
            ee.header ee.perm) ∧
      RD code ee g s0 ⟨4680⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
        out (cA', σ') k' C' ∧
      out.size < UInt256.size := by
  simpa using RD.call rd4679 (by clipper_runtime_decode) hdepth hov

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 5000000 in
theorem RD.clipperTakeClipperCallPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} {aw : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4664 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4664⟩
      (UInt256.land solcAddrMask who :: UInt256.land solcAddrMask who :: ⟨0⟩ ::
        ⟨128⟩ :: UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat) :: ⟨128⟩ ::
        ⟨0⟩ :: (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ::
        clipperTakeCallbackSelectorSeed :: UInt256.land solcAddrMask who :: dog :: slice ::
        owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      (clipperTakeCallbackCalldataMem I owe slice dataLen dataStart baseMem)
      aw rdata (cA, σ) k C)
    (hbaseMem : baseMem.size = 260)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (UInt256.land solcAddrMask who) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_cb : Batteries.RBSet AccountAddress compare) (σ_cb : AccountMap)
      (zCb : Bool) (outCb : ByteArray) (A_cb : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4680⟩
        ((if zCb then ⟨1⟩ else ⟨0⟩) ::
          (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ::
          clipperTakeCallbackSelectorSeed :: UInt256.land solcAddrMask who :: dog :: slice ::
          owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
          who :: max :: amt :: id :: R)
        (outCb.write 0
          (clipperTakeCallbackCalldataMem I owe slice dataLen dataStart baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outCb.size)).toNat)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M aw.toNat 128
              (UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat)).toNat)
            128 0))
        outCb (cA_cb, σ_cb) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address
          (AccountAddress.ofNat (UInt256.land solcAddrMask who).toNat))
        "clipperCall" 0
        [.address I.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I]
        (zCb,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_cb
            substate := A_cb
            createdAccounts := cA_cb },
          outCb) true ∧
      outCb.size < UInt256.size := by
  have hguardOv :
      (⟨0⟩ :: ⟨128⟩ :: UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat) ::
        ⟨128⟩ :: ⟨0⟩ ::
        (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ::
        clipperTakeCallbackSelectorSeed :: UInt256.land solcAddrMask who :: dog :: slice ::
        owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R).length + 4 ≤ 1024 := by
    simp only [List.length_cons]
    omega
  obtain ⟨gasWord, _, _, rd4679⟩ :=
    RD.clipperTakeClipperCallCodeOkGas v hpatch rd4664 hcodeSize hguardOv
  obtain ⟨cA_cb, σ_cb, zCb, outCb, A_in, callGas, k4680, C4680, hΘpack,
      rd4680raw, houtCbSize⟩ :=
    RD.clipperTakeClipperCallStep v hpatch rd4679 hdepth (by
      simp only [List.length_cons]
      omega)
  obtain ⟨g'', A_cb, hΘ⟩ := hΘpack
  refine ⟨cA_cb, σ_cb, zCb, outCb, A_cb, k4680, C4680, ?_, ?_, houtCbSize⟩
  · exact rd4680raw
  · let evmCb : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmCb) (name := "clipperCall")
      (args := [.address I.source, .int (Int.ofNat owe.toNat),
        .int (Int.ofNat slice.toNat), clipperTakeDataValue I])
      (tgt := EVM.address
        (AccountAddress.ofNat (UInt256.land solcAddrMask who).toNat))
      (targetWord := UInt256.land solcAddrMask who)
      (cA' := cA_cb) (σ' := σ_cb) (A' := A_cb) (A_in := A_in)
      (z := zCb) (o := outCb) (g'' := g'') (callGas := callGas)
      (mem := clipperTakeCallbackCalldataMem I owe slice dataLen dataStart baseMem)
      (inOff := ⟨128⟩)
      (inSize := UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat))
      (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmCb, initState] using h
        rw [hI]
        decide))
      ?_ ?_ ?_
    · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      exact clipperTakeEVMAddressAccountAddress _
    · have hpadLe := clipperTake_paddedSize_le dataLen.toNat
      have hinSizeLt : 164 + ABI.paddedSize dataLen.toNat < UInt256.size := by
        change 164 + ABI.paddedSize dataLen.toNat < 2 ^ 256
        omega
      simpa [show (⟨128⟩ : UInt256).toNat = 128 by decide,
        ulit_toNat' _ hinSizeLt] using
        clipperTakeCallbackEncode_eq v I owe slice dataLen dataStart hbaseMem
          hdataLen hdataLenEq hdataStartEq hlenMax hpayload
    · simpa [evmCb, initState, hperm] using hΘ

theorem RD.clipperTakeClipperCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd4680 : RD code ee g s0 ⟨4680⟩ (⟨0⟩ :: R) mem aw out acc k C)
    (houtSize : out.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4680⟩) (okPc := ⟨4696⟩)
    rd4680 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    houtSize hov

theorem RD.clipperTakeClipperCallSuccessGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {R : List UInt256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4680 : RD code ee g s0 ⟨4680⟩ (status :: R) mem aw out acc k C)
    (hstatus : status ≠ ⟨0⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4698⟩ R mem aw out acc k' C' := by
  obtain ⟨k', C', rd4698⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4680⟩) (okPc := ⟨4696⟩) rd4680 hstatus
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperTakeJumpDest4696 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode) hov
  exact ⟨k', C', by simpa using rd4698⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeClipperCallSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {endPtr selector target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart
      who max amt id : UInt256}
    {R : List UInt256} {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4680 : RD code ee g s0 ⟨4680⟩
      (⟨1⟩ :: endPtr :: selector :: target :: dog :: slice :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw out acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw out acc k' C' := by
  obtain ⟨_, _, rd4698⟩ :=
    RD.clipperTakeClipperCallSuccessGuard v hpatch rd4680
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by simp only [List.length_cons]; omega)
  have rd4701 := evm_run rd4698 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd4701⟩

end Benchmarks.Dss.Clipper
