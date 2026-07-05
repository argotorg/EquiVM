import Benchmarks.Dss.Jug.DripSourceFold

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

theorem RD.jugDripToVatIlksExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {k C : ℕ}
    (rd1323 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1323⟩
      [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, sel]
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1384⟩
      (dripVatTargetWord σ I :: dripVatTargetWord σ I :: ⟨0⟩ :: dripVatIlksOutPtr ::
        dripVatIlksInSize :: dripVatIlksOutPtr :: ⟨64⟩ :: dripVatIlksEndPtr ::
        dripVatIlksSelectorWord :: dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  let target := dripVatTargetWord σ I
  let rawTarget := jugSlotWord ⟨2⟩ σ I
  have htargetMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        rawTarget = target := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
      native_decide
    rw [u256_land_comm]
    rw [hmask]
  have htargetMaskSolc :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (solcSlotWord σ I ⟨2⟩) = dripVatTargetWord σ I := by
    simpa [target, rawTarget, jugSlotWord] using htargetMask
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (dripIlkHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dripIlkHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dripIlkHashMem_size I]; decide) (by decide)
      (dripIlkHashMem_read64 I)
  have hcallMem : (dripVatIlksCalldataMem I (dripIlkHashMem I)).size = 164 :=
    dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)
  have hcallRead64 :
      (dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dripVatIlksCalldataMem_read64 I (dripIlkHashMem_size I) (dripIlkHashMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dripVatIlksCalldataMem I (dripIlkHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
      (fromByteArrayBigEndian
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd1324 := rd1323.jumpdest (by native_decide) (by evm_ov)
  have rd1326 := rd1324.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1327, C1327, rd1327raw⟩ := rd1326.sload (by native_decide) (by evm_ov)
  have rd1327 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1327⟩
      (rawTarget :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1327 C1327 := by
    simpa [rawTarget, jugSlotWord, solcSlotWord] using rd1327raw
  have rd1384 := evm_run rd1327 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨1823590043⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (dripVatIlksSelectorMem (dripIlkHashMem I)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup6,
    swap1,
    raw mstore 3 (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap4,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    swap3,
    push4 dripVatIlksSelectorWord,
    swap3,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap4,
    swap2,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup8,
    dup8,
    dup1]
  have hpc :
      ((⟨1327⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) = (⟨1384⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [target, dripVatIlksSelectorShifted, dripVatIlksSelectorWord, dripVatIlksSelectorMem,
      dripVatIlksCalldataMem, dripVatIlksOutPtr, dripVatIlksInSize, dripVatIlksEndPtr,
      htargetMask, hpc] using rd1384⟩

theorem RD.jugDripVatIlksNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {k C : ℕ}
    (rd1323 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1323⟩
      [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, sel]
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (dripVatTargetWord σ I) = ⟨0⟩) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1384⟩ := RD.jugDripToVatIlksExtcodesizeGuard rd1323
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨1384⟩) (okPc := ⟨1396⟩) rd1384
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.jugDripVatIlksCallReady
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {k C : ℕ}
    (rd1323 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1323⟩
      [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, sel]
      (dripIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (gasWord :: dripVatTargetWord σ I :: ⟨0⟩ :: dripVatIlksOutPtr ::
        dripVatIlksInSize :: dripVatIlksOutPtr :: ⟨64⟩ :: dripVatIlksEndPtr ::
        dripVatIlksSelectorWord :: dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1384⟩ := RD.jugDripToVatIlksExtcodesizeGuard rd1323
  obtain ⟨gasWord, k', C', rd1399⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1384⟩) (okPc := ⟨1396⟩) rd1384
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1399⟩

theorem RD.jugDripVatIlksPostCall
    {cA gh bl σ σ₀ A I} {g sel gasWord : UInt256} {k C : ℕ}
    (rd1399 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (gasWord :: dripVatTargetWord σ I :: ⟨0⟩ :: dripVatIlksOutPtr ::
        dripVatIlksInSize :: dripVatIlksOutPtr :: ⟨64⟩ :: dripVatIlksEndPtr ::
        dripVatIlksSelectorWord :: dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD jugBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
            dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
            sel :: [])
          (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd1400raw, hout⟩ :=
    RD.call rd1399 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          dripVatIlksOutPtr.toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      unfold dripVatIlksOutPtr dripVatIlksInSize
      native_decide
    simpa [dripVatIlksPostCallMem, dripVatIlksOutPtr, dripVatIlksInSize,
      dripVatIlksEndPtr, haw] using rd1400raw

theorem RD.jugDripVatIlksCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel gasWord : UInt256} {k C : ℕ}
    (rd1399 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (gasWord :: dripVatTargetWord σ I :: ⟨0⟩ :: dripVatIlksOutPtr ::
        dripVatIlksInSize :: dripVatIlksOutPtr :: ⟨64⟩ :: dripVatIlksEndPtr ::
        dripVatIlksSelectorWord :: dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd1400raw⟩ :=
    RD.callDepthLimit rd1399 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
        dripVatIlksOutPtr.toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    unfold dripVatIlksOutPtr dripVatIlksInSize
    native_decide
  simpa [dripVatIlksOutPtr, dripVatIlksInSize, dripVatIlksEndPtr, hmin,
    byteArray_write_len_zero, haw] using rd1400raw

theorem RD.jugDripVatIlksCallFailed
    {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1400⟩) (okPc := ⟨1416⟩) rd1400
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.jugDripVatIlksCallSucceeded
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨1⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1418⟩
      (dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨1400⟩) (okPc := ⟨1416⟩) rd1400
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripVatIlksReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd1418 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1418⟩
      (dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rdPop0 := RD.pop rd1418 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 6) rdPush64
    (by native_decide)
    mem_cost
    (dripVatIlksPostCallMem_mload64 I out hshort hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1438⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripVatIlksReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd1418 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1418⟩
      (dripVatIlksEndPtr :: dripVatIlksSelectorWord :: dripVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1446⟩
      (dripVatIlksPrevWord out :: ⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I ::
        ⟨357⟩ :: sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out acc k' C' := by
  have rdPop0 := RD.pop rd1418 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 6) rdPush64
    (by native_decide)
    mem_cost
    (dripVatIlksPostCallMem_mload64_long I out hlo hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1438⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdPopLen ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1 := RD.swap1 rdPush32 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2' := RD.dup2 rdSwap1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAdd := RD.add rdDup2' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload160 := RD.mload 0 (dripVatIlksPrevWord out) (UInt256.ofNat 6) rdAdd
    (by native_decide)
    mem_cost
    (dripVatIlksPostCallMem_mload160_long I out hlo hout)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rdMload160⟩

theorem RD.jugDripLoadBaseDuty
    {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (rd1446 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1446⟩
      (dripVatIlksPrevWord out :: ⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I ::
        ⟨357⟩ :: sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1465⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: dripVatIlksPrevWord out ::
        jugSlotWord ⟨4⟩ σ' I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out))
      (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
            (dripVatIlksPostCallMem I out)).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    exact drip_twoWordHashMem_solcMappingSlot_of_ge64 (⟨1⟩ : UInt256) (fileDutyIlkWord I)
      (by rw [dripVatIlksPostCallMem_size_long I out hlo hout]; omega)
  have rd1448 := RD.push1 rd1446 ⟨4⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k1449, C1449, rd1449raw⟩ := rd1448.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1449 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1449⟩
      (jugSlotWord ⟨4⟩ σ' I :: dripVatIlksPrevWord out :: ⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k1449 C1449 := by
    simpa [jugSlotWord, solcSlotWord] using rd1449raw
  have rd1453pre := evm_run rd1449 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1454 := rd1453pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I)
      (dripVatIlksPostCallMem I out))
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1458pre := evm_run rd1454 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have rd1459 := rd1458pre.mstore 0
    (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out))
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1463pre := evm_run rd1459 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd1464 := rd1463pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 6) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k1465, C1465, rd1465raw⟩ := rd1464.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k1465, C1465, ?_⟩
  have hpc :
      ({ val := 1449 } + UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } +
                    UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } +
                  UInt256.ofNat 2 + { val := 1 } + { val := 1 } + { val := 1 } +
                { val := 1 }) = (⟨1465⟩ : UInt256) := by
    native_decide
  have hslotEq : fileDutyDutySlotFor I = solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) :=
    fileDutyDutySlotFor_eq hsz36
  simpa [hpc, jugSlotWord, solcSlotWord, hslotEq] using rd1465raw

theorem RD.jugDripToAddRoutine
    {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out : ByteArray} {k C : ℕ}
    (rd1465 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1465⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: dripVatIlksPrevWord out ::
        jugSlotWord ⟨4⟩ σ' I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out))
      (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2131⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: jugSlotWord ⟨4⟩ σ' I ::
        ⟨1485⟩ :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out))
      (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have rd1484 := evm_run rd1465 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨1530⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push2 ⟨1524⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push2 ⟨1485⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2131⟩ (by native_decide) (by evm_ov)]
  have rd2131 := rd1484.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd2131⟩

theorem RD.jugDripAddOverflowReverts
    {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out mem : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤ (jugSlotWord ⟨4⟩ σ' I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ' I).toNat)
    (rd2131 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2131⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: jugSlotWord ⟨4⟩ σ' I ::
        ⟨1485⟩ :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let base := jugSlotWord ⟨4⟩ σ' I
  let duty := jugSlotWord (fileDutyDutySlotFor I) σ' I
  have hlt : UInt256.lt (duty + base) base = ⟨1⟩ := by
    simpa [base, duty] using constructorCheckedAddOverflowLt base duty hover
  have rdPushOk := evm_run rd2131 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have rdFallthrough := rdPushOk.jumpiNT (by native_decide)
    (by rw [hlt]; decide)
    (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripAddReturns
    {cA cA' gh bl σ σ' σ₀ A I} {g sel : UInt256}
    {out mem : ByteArray} {k C : ℕ}
    (hno :
      ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ' I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ' I).toNat)
    (rd2131 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2131⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: jugSlotWord ⟨4⟩ σ' I ::
        ⟨1485⟩ :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      ((jugSlotWord ⟨4⟩ σ' I + jugSlotWord (fileDutyDutySlotFor I) σ' I) ::
        ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  let base := jugSlotWord ⟨4⟩ σ' I
  let duty := jugSlotWord (fileDutyDutySlotFor I) σ' I
  have hlt : UInt256.lt (duty + base) base = ⟨0⟩ := by
    simpa [base, duty] using constructorCheckedAddNoOverflowLt base duty hno
  have rdPushOk := evm_run rd2131 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have rd2147 := rdPushOk.jumpiT (by native_decide)
    (by rw [hlt]; decide)
    (by jump_dest)
    (by evm_ov)
  have rd2152 := evm_run rd2147 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1485 := rd2152.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [base, duty, u256_add_comm] using rd1485⟩


end Benchmarks.Dss.Jug
