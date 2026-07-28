import Benchmarks.Dss.Vow.FlapDai

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` second `vat.sin(address(this))` call -/

theorem RD.vowFlapToSin1ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1261⟩
      (kissDaiTargetWord acc.2 I :: kissDaiTargetWord acc.2 I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord acc.2 I :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  let target := kissDaiTargetWord acc.2 I
  let rawTarget := vowSlotWord ⟨1⟩ acc.2 I
  have rd1191 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1193 := rd1191.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1194, C1194, rd1194Raw⟩ := rd1193.sload (by native_decide) (by evm_ov)
  have rd1194 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1194⟩
      (rawTarget :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1194 C1194 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd1194Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hSinMem : (healSinCalldataMem I mem).size = 164 :=
    healSinCalldataMem_size I hmem
  have hSinRead64 :
      (healSinCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    healSinCalldataMem_read64 I hmem hread64
  have hmload64Sin :
      (if (⟨64⟩ : UInt256).toNat ≥ (healSinCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((healSinCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSinMem]; decide) (by decide) hSinRead64
  have rd1261 := evm_run rd1194 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨2016186517⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (healSinSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (healSinCalldataMem I mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Sin (by decide) (by evm_ov),
    push2 ⟨1333⟩,
    swap3,
    push2 ⟨1325⟩,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap2,
    and,
    swap2,
    push4 healSinSelector,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  exact ⟨_, _, by
    simpa [target, rawTarget, kissDaiTargetWord, healSinSelectorShifted, healSinSelector,
      healSinSelectorMem, healSinCalldataMem, healSinOutPtr, healSinInSize, healSinEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask] using rd1261⟩

theorem RD.vowFlapSin1NoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1261⟩ := RD.vowFlapToSin1ExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1261⟩) (okPc := ⟨1273⟩) rd1261
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlapToSin1Staticcall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1276⟩
      (gasWord :: kissDaiTargetWord acc.2 I :: healSinOutPtr :: healSinInSize ::
        healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord acc.2 I :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  obtain ⟨_, _, rd1261⟩ := RD.vowFlapToSin1ExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k1276, C1276, rd1276⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1261⟩) (okPc := ⟨1273⟩) rd1261
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1276, C1276, by simpa using rd1276⟩

theorem RD.vowFlapSin1PostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord acc.2 I :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (out.write 0 (healSinCalldataMem I mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := acc.2, createdAccounts := acc.1 }
        (EVM.address (kissVatAddress acc.2 I)) "sin" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) false
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1276⟩ :=
    RD.vowFlapToSin1Staticcall rd hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k1277, C1277, hΘpack, rd1277raw, houtsz⟩ :=
    RD.solcStaticcall rd1276 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1277, C1277, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          healSinOutPtr.toNat healSinInSize.toNat)
          healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [healSinInSize_eq]
      unfold healSinOutPtr
      native_decide
    have hoff : healSinOutPtr.toNat = 128 := by
      unfold healSinOutPtr
      native_decide
    have rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord acc.2 I :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (out.write 0 (healSinCalldataMem I mem) healSinOutPtr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k1277 C1277 :=
      haw ▸ rd1277raw
    rw [hoff] at rd1277
    exact rd1277
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord acc.2 I)
      (mem := healSinCalldataMem I mem) (inOff := healSinOutPtr)
      (inSize := healSinInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget acc.2 I) (healSinEncode_eq I hmem) ?_
    simpa [initState] using hΘ

theorem RD.vowFlapSin1CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1277⟩) (okPc := ⟨1293⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowFlapSin1CallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1277⟩) (okPc := ⟨1293⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlapSin1ReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlapSin1ReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (retWord :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowFlapFreeSinSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : vatSin.toNat < (vowSlotWord ⟨5⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨1333⟩, ⟨0⟩, ⟨357⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hlt)
    (by simp)

theorem RD.vowFlapFreeSinSubSuccess
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I) ::
        ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k1325, C1325, rd1325⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨1333⟩, ⟨0⟩, ⟨357⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k1325, C1325, by simpa [SinVal] using rd1325⟩

theorem RD.vowFlapDebtSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : freeSin.toNat < (vowSlotWord ⟨6⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨1333⟩)
    (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hlt)
    (by simp)

theorem RD.vowFlapDebtSubSuccess
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1333⟩
      (UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I) ::
        ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k1333, C1333, rd1333⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨1333⟩)
    (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k1333, C1333, by simpa [AshVal] using rd1333⟩

abbrev vowDebtNotZeroRawWord : UInt256 :=
  ⟨29412446707286443796640128925362928579183⟩

abbrev vowDebtNotZeroStringWord : UInt256 :=
  UInt256.shiftLeft vowDebtNotZeroRawWord ⟨120⟩

theorem RD.vowFlapDebtNotZero
    {cA gh bl σ σ₀ A I} {g sel debt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1333⟩
      (debt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hdebt : debt ≠ ⟨0⟩)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd1334 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1335₀ := rd1334.iszero (by native_decide) (by evm_ov)
  have rd1335 := rd1335₀
  rw [isZero_eq_zero_of_ne hdebt] at rd1335
  have rd1338 := rd1335.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
  have rd1339 := rd1338.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1343 := evm_run rd1339 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd1347 := rd1343.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1366 := evm_run rd1347 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨17⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1384 := rd1366.pushConst vowDebtNotZeroRawWord
    (width := 17) (op := .PUSH17) (by decide) (by native_decide) (by evm_ov)
  have rd1387₀ := evm_run rd1384 with [
    push1 ⟨120⟩,
    shl]
  have rd1387 := rd1387₀
  rw [show UInt256.shiftLeft vowDebtNotZeroRawWord ⟨120⟩ =
      vowDebtNotZeroStringWord from rfl] at rd1387
  exact evm_run rd1387 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨17⟩ : UInt256) vowDebtNotZeroStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨17⟩ : UInt256)
        vowDebtNotZeroStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vowFlapDebtZero
    {cA gh bl σ σ₀ A I} {g sel debt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1333⟩
      (debt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hdebt : debt = ⟨0⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k' C' := by
  have rd1334 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1335₀ := rd1334.iszero (by native_decide) (by evm_ov)
  have rd1335 := rd1335₀
  rw [hdebt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1335
  have rd1338 := rd1335.push2 ⟨1403⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1338.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

end Benchmarks.Dss.Vow
