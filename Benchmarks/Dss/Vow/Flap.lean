import Benchmarks.Dss.Vow.HealSuccess
import Benchmarks.Dss.Vow.VatSinCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` -/

theorem vowDispatch_flap {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩) :
    dispatchMsg contract I.calldata = some flapTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition])
    (post := [flapperTransition, flogTransition, flopTransition, flopperTransition,
      healTransition, humpTransition, kissTransition, liveTransition, relyTransition,
      sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := flapTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, hcd]
      decide +native
  · rw [selectorOf, flapSelectorBytes]
    exact hsel

theorem vowDecode_flap {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
      (transitionSignature flapTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachFlapBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨349⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨234953099⟩ :=
    vowSelWord_eq_of_beq I hsz 0x0e 0x01 0x19 0x8b ⟨234953099⟩
      (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 0))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vowReachLowLowBody 0 (by omega) ⟨349⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by decide +native)

theorem RD.vowFlapToSin0ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨921⟩
      (kissDaiTargetWord σ I :: kissDaiTargetWord σ I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  let rawTarget := vowSlotWord ⟨1⟩ σ I
  obtain ⟨_, _, rd349⟩ := hreach
  have rd350 := rd349.jumpdest (by decide +native) (by evm_ov)
  have rd353 := rd350.push2 ⟨357⟩ (by decide +native) (by evm_ov)
  have rd356 := rd353.push2 ⟨847⟩ (by decide +native) (by evm_ov)
  have rd847 := by
    simpa using rd356.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd850 := rd847.jumpdest (by decide +native) (by evm_ov)
  have rd851 := rd850.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  obtain ⟨k851, C851, rd852₀⟩ := rd851.sload (by decide +native) (by evm_ov)
  have rd852 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨851⟩
      (rawTarget :: ⟨357⟩ :: sel :: []) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k851 C851 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd852₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hSinMem : (healSinCalldataMem I solcFreePtrMem).size = 164 :=
    initialHealSinCalldataMem_size I
  have hSinRead64 :
      (healSinCalldataMem I solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    initialHealSinCalldataMem_read64 I
  have hmload64Sin :
      (if (⟨64⟩ : UInt256).toNat ≥ (healSinCalldataMem I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((healSinCalldataMem I solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSinMem]; decide) (by decide) hSinRead64
  have rd921 := evm_run rd852 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨2016186517⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (healSinSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 3 (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Sin (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap3,
    push2 ⟨993⟩,
    swap3,
    push2 ⟨985⟩,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
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
      vowSlotWord, solcSlotWord, solcAddrMask] using rd921⟩

theorem RD.vowFlapVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd921⟩ := RD.vowFlapToSin0ExtcodesizeGuard hreach
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨921⟩) (okPc := ⟨933⟩) rd921
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem RD.vowFlapToSin0Staticcall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨936⟩
      (gasWord :: kissDaiTargetWord σ I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd921⟩ := RD.vowFlapToSin0ExtcodesizeGuard hreach
  obtain ⟨gasWord, k, C, rd936⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨921⟩) (okPc := ⟨933⟩) rd921
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa using rd936⟩

theorem RD.vowFlapSin0PostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (o.write 0 (healSinCalldataMem I solcFreePtrMem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd936⟩ :=
    RD.vowFlapToSin0Staticcall hreach hcodeSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k937, C937, hΘpack, rd937raw, hosz⟩ :=
    RD.solcStaticcall rd936 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k937, C937, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          healSinOutPtr.toNat healSinInSize.toNat)
          healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [healSinInSize_eq]
      decide +native
    have hoff : healSinOutPtr.toNat = 128 := by
      decide +native
    have rd937 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (o.write 0 (healSinCalldataMem I solcFreePtrMem) healSinOutPtr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k937 C937 :=
      haw ▸ rd937raw
    rw [hoff] at rd937
    exact rd937
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σ I)
      (mem := healSinCalldataMem I solcFreePtrMem) (inOff := healSinOutPtr)
      (inSize := healSinInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ I) (initialHealSinEncode_eq I) ?_
    simpa [initState] using hΘ

theorem RD.vowFlapSin0CallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty
      (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd936⟩ := RD.vowFlapToSin0Staticcall hreach hcodeSize
  obtain ⟨k937, C937, rd937raw⟩ :=
    RD.solcStaticcallDepthLimit rd936 (by decide +native) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        healSinOutPtr.toNat healSinInSize.toNat)
        healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    rw [healSinInSize_eq]
    decide +native
  have hoff : healSinOutPtr.toNat = 128 := by
    decide +native
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd937 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (ByteArray.empty.write 0 (healSinCalldataMem I solcFreePtrMem) healSinOutPtr.toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k937 C937 :=
    haw ▸ rd937raw
  rw [hoff, hmin, byteArray_write_len_zero] at rd937
  exact ⟨k937, C937, rd937⟩

theorem RD.vowFlapSin0CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨937⟩) (okPc := ⟨953⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz hov

theorem RD.vowFlapSin0CallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨955⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨937⟩) (okPc := ⟨953⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlapSin0ReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨955⟩
      (d0 :: d1 :: d2 :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
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
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨955⟩) (okPc := ⟨975⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by simp)

theorem RD.vowFlapSin0ReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨955⟩
      (d0 :: d1 :: d2 :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
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
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨978⟩
      (retWord :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨955⟩) (okPc := ⟨975⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) (by decide +native) (by decide +native) (by decide +native) (by evm_ov)

theorem vowFlapSourceVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvat (by simpa [evm0] using hvatNoCode)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapSourceVatSin0CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (false, evmSin, outSin) false) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapSourceVatSin0DecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin : config.externalABI.decode? "sin" outSin = none) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallSin hdecSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapVatSin0NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapVatSin0NoCode hreach hcodeSize
  have hVat : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTarget : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVat]
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    rw [← hTarget, ← hsame]
    exact hcodeSize
  have haddr :
      kissVatAddress σ_solm I =
        AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I) :=
    kissVatAddress_eq_daiTarget_account σ_solm I
  have hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [initState, State.lookupAccount] using
      extCodeSizeWord_zero_lookup_code_zero
        (σ := σ_solm) (target := kissDaiTargetWord σ_solm I)
        (addr := kissVatAddress σ_solm I) haddr hcodeSizeSolm
  have hbody := vowFlapSourceVatSin0NoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode (by simpa using hbody)

theorem vowFlapSin0CallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd937 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (false, evmSin, outSin) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapSin0CallFailure rd937 hrdataSize (by simp)
  have hbody := vowFlapSourceVatSin0CallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) hwv hvatCode hcallSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlapSin0DecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (rd937 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
      (UInt256.ofNat 6) outSin (cA', σ'_evm) k C)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          outSin) false)
    (hosz : outSin.size < UInt256.size)
    (hshort : outSin.size < 32)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = outSin.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd937' := rd937
  rw [hmin] at rd937'
  obtain ⟨_, _, rd955⟩ :=
    RD.vowFlapSin0CallSuccessToDecode rd937' (by simp)
  have hmem : (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size =
      164 :=
    initialHealSinWrite_size I outSin outSin.size (by omega) (by omega)
  have hread64 :
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    initialHealSinWrite_read64 I outSin outSin.size (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hrev := RD.vowFlapSin0ReturnDecodeShortReverts rd955 hshort hosz hmload64
  have hdecSin : config.externalABI.decode? "sin" outSin = none :=
    vatSinDecode_none_short hshort
  have hbody := vowFlapSourceVatSin0DecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_evm
          substate := A'_evm
          createdAccounts := cA' })
    (outSin := outSin) hwv hvatCode hcallSin hdecSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
