import Benchmarks.Dss.Jug.DripEVMRpow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

theorem RD.jugDripToDiffRoutine
    {cA cA' gh bl σ σ' σ₀ A I} {g rate prev sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd1530 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1530⟩
      (rate :: prev :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (prev :: rate :: ⟨1570⟩ :: dripVowTargetWord σ' I :: fileDutyIlkWord I ::
        dripVatFoldSelectorWord :: dripVatTargetWord σ' I :: prev :: rate ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  let vatRaw := jugSlotWord ⟨2⟩ σ' I
  let vowRaw := jugSlotWord ⟨3⟩ σ' I
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hvatMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        vatRaw = dripVatTargetWord σ' I := by
    rw [u256_land_comm, hmask]
  have hvowMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        vowRaw = dripVowTargetWord σ' I := by
    rw [u256_land_comm, hmask]
  have rd1531 := rd1530.jumpdest (by decide +native) (by evm_ov)
  have rd1533 := rd1531.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1534, C1534, rd1534raw⟩ := rd1533.sload (by decide +native) (by evm_ov)
  have rd1534 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1534⟩
      (vatRaw :: rate :: prev :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k1534 C1534 := by
    simpa [vatRaw, jugSlotWord, solcSlotWord] using rd1534raw
  have rd1536 := rd1534.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  obtain ⟨k1537, C1537, rd1537raw⟩ := rd1536.sload (by decide +native) (by evm_ov)
  have rd1537 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1537⟩
      (vowRaw :: vatRaw :: rate :: prev :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k1537 C1537 := by
    simpa [vowRaw, jugSlotWord, solcSlotWord] using rd1537raw
  have rd1569 := evm_run rd1537 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 dripVatFoldSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push2 ⟨1570⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw push2 ⟨2397⟩ (by decide +native) (by evm_ov)]
  have rd2397 := rd1569.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [dripVatFoldSelectorWord, dripVatTargetWord, dripVowTargetWord, hvatMask, hvowMask]
      using rd2397⟩

theorem RD.jugDripVatFoldCallGuard
    {cA cA' gh bl σ σ' σ₀ A I} {g delta prev rate sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd1570 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
      (delta :: dripVowTargetWord σ' I :: fileDutyIlkWord I :: dripVatFoldSelectorWord ::
        dripVatTargetWord σ' I :: prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1635⟩
      (dripVatTargetWord σ' I :: dripVatTargetWord σ' I :: ⟨0⟩ :: dripVatFoldOutPtr ::
        dripVatFoldInSize :: dripVatFoldOutPtr :: ⟨0⟩ :: dripVatFoldEndPtr ::
        dripVatFoldSelectorWord :: dripVatTargetWord σ' I :: prev :: rate ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatFoldCalldataMem σ' I delta mem) (UInt256.ofNat 8) out (cA', σ') k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hselector :
      UInt256.shiftLeft
          (UInt256.land (⟨4294967295⟩ : UInt256) dripVatFoldSelectorWord) ⟨224⟩ =
        dripVatFoldSelectorShifted := by
    decide +native
  have hvowCanon : (dripVowTargetWord σ' I).toNat < EVM.addressModulus := by
    simpa [dripVowTargetWord, jugAddressReturnWord] using
      solcAddrMask_result_canonical (jugSlotWord ⟨3⟩ σ' I)
  have hvowMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (dripVowTargetWord σ' I) = dripVowTargetWord σ' I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hvowCanon
  have rd1635 := evm_run rd1570 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (dripVatFoldSelectorMem mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rw [hselector]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (dripVatFoldIlkMem I mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 3 (dripVatFoldVowMem σ' I mem) (UInt256.ofNat 7)
      (by decide +native) mem_cost (by rw [hvowMask]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 3 (dripVatFoldCalldataMem σ' I delta mem) (UInt256.ofNat 8)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost (dripVatFoldCalldataMem_mload64 σ' I delta hmem hread64)
      (by decide) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [dripVatFoldOutPtr, dripVatFoldInSize, dripVatFoldEndPtr,
      dripVatFoldSelectorWord, dripVatFoldSelectorShifted, hselector, hvowMask] using rd1635⟩

theorem RD.jugDripVatFoldCallReady
    {cA cA' gh bl σ σ' σ₀ A I} {g delta prev rate sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (dripVatTargetWord σ' I) ≠ ⟨0⟩)
    (rd1570 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
      (delta :: dripVowTargetWord σ' I :: fileDutyIlkWord I :: dripVatFoldSelectorWord ::
        dripVatTargetWord σ' I :: prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ gasWord k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1650⟩
      (gasWord :: dripVatTargetWord σ' I :: ⟨0⟩ :: dripVatFoldOutPtr ::
        dripVatFoldInSize :: dripVatFoldOutPtr :: ⟨0⟩ :: dripVatFoldEndPtr ::
        dripVatFoldSelectorWord :: dripVatTargetWord σ' I :: prev :: rate ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatFoldCalldataMem σ' I delta mem) (UInt256.ofNat 8) out (cA', σ') k' C' := by
  obtain ⟨_, _, rd1635⟩ := RD.jugDripVatFoldCallGuard hmem hread64 rd1570
  obtain ⟨gasWord, k', C', rd1650⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1635⟩) (okPc := ⟨1647⟩) rd1635
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1650⟩

theorem RD.jugDripVatFoldNoCode
    {cA cA' gh bl σ σ' σ₀ A I} {g delta prev rate sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (dripVatTargetWord σ' I) = ⟨0⟩)
    (rd1570 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
      (delta :: dripVowTargetWord σ' I :: fileDutyIlkWord I :: dripVatFoldSelectorWord ::
        dripVatTargetWord σ' I :: prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1635⟩ := RD.jugDripVatFoldCallGuard hmem hread64 rd1570
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1635⟩) (okPc := ⟨1647⟩) rd1635
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem RD.jugDripVatFoldPostCall
    {cA cA' gh bl σ σ' σ₀ A I} {g delta prev rate sel gasWord : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd1650 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1650⟩
      (gasWord :: dripVatTargetWord σ' I :: ⟨0⟩ :: dripVatFoldOutPtr ::
        dripVatFoldInSize :: dripVatFoldOutPtr :: ⟨0⟩ :: dripVatFoldEndPtr ::
        dripVatFoldSelectorWord :: dripVatTargetWord σ' I :: prev :: rate ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (dripVatFoldCalldataMem σ' I delta mem) (UInt256.ofNat 8) out (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (foldOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, foldOut) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ'
          σ₀ Ain (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatFoldCalldataMem σ' I delta mem).readWithPadding
            dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD jugBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1651⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: dripVatFoldEndPtr :: dripVatFoldSelectorWord ::
            dripVatTargetWord σ' I :: prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ ::
            sel :: [])
          (dripVatFoldCalldataMem σ' I delta mem) (UInt256.ofNat 8) foldOut
          (cA'', σ'') k' C'
      ∧ foldOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, foldOut, Ain, callGas, k', C', hΘ, rd1651raw, hout⟩ :=
    RD.call rd1650 (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, foldOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat foldOut.size)).toNat = 0 := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat foldOut.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat foldOut.size).toNat = 0
      by_cases h : (⟨0⟩ : UInt256) ≤ UInt256.ofNat foldOut.size
      · simp [h]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
          dripVatFoldOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      unfold dripVatFoldOutPtr dripVatFoldInSize
      decide +native
    simpa [dripVatFoldOutPtr, dripVatFoldInSize, dripVatFoldEndPtr, hmin,
      byteArray_write_len_zero, haw] using rd1651raw

theorem RD.jugDripVatFoldCallFailed
    {cA cA'' gh bl σ σ'' σ₀ A I} {g targetWord prev rate sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd1651 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1651⟩
      (⟨0⟩ :: dripVatFoldEndPtr :: dripVatFoldSelectorWord :: targetWord ::
        prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata (cA'', σ'') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1651⟩) (okPc := ⟨1667⟩) rd1651
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp)

theorem RD.jugDripVatFoldCallSucceeded
    {cA gh bl σ σ₀ A I} {g targetWord prev rate sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd1651 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1651⟩
      (⟨1⟩ :: dripVatFoldEndPtr :: dripVatFoldSelectorWord :: targetWord ::
        prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1669⟩
      (dripVatFoldEndPtr :: dripVatFoldSelectorWord :: targetWord ::
        prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1651⟩) (okPc := ⟨1667⟩) rd1651
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripVatFoldStoreRhoReturns
    {cA cA' gh bl σ σ' σ₀ A I} {g targetWord prev rate sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd1669 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1669⟩
      (dripVatFoldEndPtr :: dripVatFoldSelectorWord :: targetWord ::
        prev :: rate :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata (cA', σ') k C) :
    RDret jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cA', sstoreAccountMap I.codeOwner σ' (fileDutyRhoSlotFor I)
        (UInt256.ofNat I.header.timestamp))
      (UInt256.toByteArray rate) := by
  let hashMem := twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ mem
  let retMem := dripVatFoldReturnMem hashMem rate
  have hhashMemSize : hashMem.size = 228 := by
    dsimp [hashMem]
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I) (⟨1⟩ : UInt256)
      (by rw [hmem]; omega), hmem]
  have hhashRead64 : hashMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [hashMem]
    exact drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I) (⟨1⟩ : UInt256)
      (by rw [hmem]; omega) hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (hashMem.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    dsimp [hashMem]
    exact drip_twoWordHashMem_solcMappingSlot_of_ge64 (⟨1⟩ : UInt256)
      (fileDutyIlkWord I) (by rw [hmem]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ hashMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (hashMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue (aw := UInt256.ofNat 8)
      (by rw [hhashMemSize]; decide) (by decide) hhashRead64
  have hretMemSize : retMem.size = 228 := by
    dsimp [retMem]
    exact dripVatFoldReturnMem_size rate hhashMemSize
  have hretRead64 : retMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [retMem]
    exact dripVatFoldReturnMem_read64 rate hhashMemSize hhashRead64
  have hretMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ retMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (retMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue (aw := UInt256.ofNat 8)
      (by rw [hretMemSize]; decide) (by decide) hretRead64
  have hretRead128 : retMem.readWithPadding 128 32 = UInt256.toByteArray rate := by
    dsimp [retMem]
    exact dripVatFoldReturnMem_read128 rate hhashMemSize
  have rd1675pre := evm_run rd1669 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov)]
  have rd1676 := rd1675pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) mem)
    (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd1684pre := evm_run rd1676 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1685 := rd1684pre.mstore 0 hashMem (UInt256.ofNat 8)
    (by decide +native) mem_cost (by dsimp [hashMem, twoWordHashMem, wordAt32Mem]; rfl)
    (by decide +native) (by evm_ov)
  have rd1689pre := evm_run rd1685 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov)]
  have rd1690 := rd1689pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 8) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd1696pre := evm_run rd1690 with [
    raw timestamp (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  obtain ⟨k1697, C1697, rd1697raw⟩ := rd1696pre.sstore hperm (by decide +native)
    (by evm_ov)
  have rd1697 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1697⟩
      (rate :: ⟨357⟩ :: sel :: []) hashMem (UInt256.ofNat 8) rdata
      (cA', sstoreAccountMap I.codeOwner σ' (fileDutyRhoSlotFor I)
        (UInt256.ofNat I.header.timestamp)) k1697 C1697 := by
    simpa [fileDutyRhoSlotFor_eq hsz36, u256_add_comm] using rd1697raw
  have rd1698 := rd1697.swap1 (by decide +native) (by evm_ov)
  have rd357 := rd1698.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact evm_run rd357 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw mstore 0 retMem (UInt256.ofNat 8) (by decide +native) mem_cost
      (by dsimp [retMem, dripVatFoldReturnMem]; rfl) (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hretMload64 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw ret 0 (UInt256.toByteArray rate) (by decide +native) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hretRead128)
      (by evm_ov)]


end Benchmarks.Dss.Jug
