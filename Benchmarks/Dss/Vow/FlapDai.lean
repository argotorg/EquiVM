import Benchmarks.Dss.Vow.FlapAdd
import Benchmarks.Dss.Vow.VatDaiCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` first `vat.dai(address(this))` call -/

theorem RD.vowFlapToDai0ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1056⟩
      (kissDaiTargetWord acc.2 I :: kissDaiTargetWord acc.2 I :: ⟨128⟩ ::
        ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        kissDaiTargetWord acc.2 I :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (vatDaiCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  let target := kissDaiTargetWord acc.2 I
  let rawTarget := vowSlotWord ⟨1⟩ acc.2 I
  have rd994 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd996 := rd994.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k997, C997, rd997Raw⟩ := rd996.sload (by native_decide) (by evm_ov)
  have rd997 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨997⟩
      (rawTarget :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k997 C997 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd997Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hDaiMem : (vatDaiCalldataMem I mem).size = 164 :=
    vatDaiCalldataMem_size I hmem
  have hDaiRead64 :
      (vatDaiCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    vatDaiCalldataMem_read64 I hmem hread64
  have hmload64Dai :
      (if (⟨64⟩ : UInt256).toNat ≥ (vatDaiCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vatDaiCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hDaiMem]; decide) (by decide) hDaiRead64
  have rd1056 := evm_run rd997 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨907205027⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (vatDaiSelectorMem mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (vatDaiCalldataMem I mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Dai (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 ⟨1814410054⟩,
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
    simpa [target, rawTarget, kissDaiTargetWord, kissDaiSelectorShifted,
      vatDaiSelectorMem, vatDaiCalldataMem, vowSlotWord, solcSlotWord, solcAddrMask]
      using rd1056⟩

theorem RD.vowFlapDai0NoCode
    {cA gh bl σ σ₀ A I} {g sel surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1056⟩ := RD.vowFlapToDai0ExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1056⟩) (okPc := ⟨1068⟩) rd1056
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlapToDai0Staticcall
    {cA gh bl σ σ₀ A I} {g sel surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1071⟩
      (gasWord :: kissDaiTargetWord acc.2 I :: ⟨128⟩ :: ⟨36⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        kissDaiTargetWord acc.2 I :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (vatDaiCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  obtain ⟨_, _, rd1056⟩ := RD.vowFlapToDai0ExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k1071, C1071, rd1071⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1056⟩) (okPc := ⟨1068⟩) rd1056
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k1071, C1071, rd1071⟩

theorem RD.vowFlapDai0PostCall
    {cA gh bl σ σ₀ A I} {g sel surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outDai : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1814410054⟩ ::
          kissDaiTargetWord acc.2 I :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (outDai.write 0 (vatDaiCalldataMem I mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := acc.2
          createdAccounts := acc.1 }
        (EVM.address (kissVatAddress acc.2 I)) "dai" 0 [.address I.codeOwner]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          outDai) false
    ∧ outDai.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1071⟩ :=
    RD.vowFlapToDai0Staticcall rd hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, outDai, A_in, callGas, k1072, C1072, hΘpack, rd1072raw,
      hosz⟩ :=
    RD.solcStaticcall rd1071 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmDaiIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := acc.2
    createdAccounts := acc.1 }
  refine ⟨cA', σ', z, outDai, A', k1072, C1072, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      native_decide
    exact haw ▸ rd1072raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord acc.2 I)
      (mem := vatDaiCalldataMem I mem) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [evmDaiIn, initState] using h
        exact absurd hdepth (by rw [hEq]; decide))
      (kissVatAddress_eq_daiTarget acc.2 I) (vatDaiEncode_eq I hmem) ?_
    simpa [evmDaiIn, initState] using hΘ

theorem RD.vowFlapDai0CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1072⟩) (okPc := ⟨1088⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowFlapDai0CallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1090⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1072⟩) (okPc := ⟨1088⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlapDai0ReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1090⟩
      (d0 :: d1 :: d2 :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
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
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1090⟩) (okPc := ⟨1110⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlapDai0ReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel surplusNeed retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1090⟩
      (d0 :: d1 :: d2 :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
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
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1113⟩
      (retWord :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1090⟩) (okPc := ⟨1110⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowFlapDai0InsufficientSurplus
    {cA gh bl σ σ₀ A I} {g sel vatDai surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1113⟩
      (vatDai :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hinsuff : vatDai.toNat < surplusNeed.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd1114₀ := rd.lt (by native_decide) (by evm_ov)
  have hlt : UInt256.lt vatDai surplusNeed = ⟨1⟩ :=
    ult_one hinsuff
  have rd1114 := rd1114₀
  rw [hlt] at rd1114
  have rd1115₀ := rd1114.iszero (by native_decide) (by evm_ov)
  have rd1115 := rd1115₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1115
  have rd1118 := rd1115.push2 ⟨1190⟩ (by native_decide) (by evm_ov)
  have rd1119 := rd1118.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1123 := evm_run rd1119 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd1127 := rd1123.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1146 := evm_run rd1127 with [
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
    push1 ⟨24⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨24⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1171 := rd1146.pushConst vowInsufficientSurplusRawWord
    (width := 24) (op := .PUSH24) (by decide) (by native_decide) (by evm_ov)
  have rd1174₀ := evm_run rd1171 with [
    push1 ⟨64⟩,
    shl]
  have rd1174 := rd1174₀
  rw [show UInt256.shiftLeft vowInsufficientSurplusRawWord ⟨64⟩ =
      vowInsufficientSurplusStringWord from rfl] at rd1174
  exact evm_run rd1174 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨24⟩ : UInt256) vowInsufficientSurplusStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨24⟩ : UInt256)
        vowInsufficientSurplusStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vowFlapDai0Enough
    {cA gh bl σ σ₀ A I} {g sel vatDai surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1113⟩
      (vatDai :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : surplusNeed.toNat ≤ vatDai.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k' C' := by
  have rd1114₀ := rd.lt (by native_decide) (by evm_ov)
  have hlt : UInt256.lt vatDai surplusNeed = ⟨0⟩ :=
    ult_zero henough
  have rd1114 := rd1114₀
  rw [hlt] at rd1114
  have rd1115₀ := rd1114.iszero (by native_decide) (by evm_ov)
  have rd1115 := rd1115₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1115
  have rd1118 := rd1115.push2 ⟨1190⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1118.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

end Benchmarks.Dss.Vow
