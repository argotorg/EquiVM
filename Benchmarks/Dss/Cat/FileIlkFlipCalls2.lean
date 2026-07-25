import Benchmarks.Dss.Cat.FileIlkFlipCalls
import Benchmarks.Dss.Cat.FileAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,bytes32,address)` — nope/hope external calls + RMW store -/

/-! ### nope calldata coupling — proved over an ABSTRACT base buffer (kiss-style), then bridged to
the concrete `fifNopeCdMem` by `rfl`, so the extract tactics never whnf the 96-byte literal. -/

/-- `nope` selector `MSTORE` at 128 over an abstract base. -/
noncomputable def fifSelMemG (base : ByteArray) : ByteArray :=
  fifNopeSelShifted.toByteArray.write 0 base 128 32

/-- `nope` calldata (selector + arg) over an abstract base. -/
noncomputable def fifCdMemG (base : ByteArray) (arg : UInt256) : ByteArray :=
  arg.toByteArray.write 0 (fifSelMemG base) 132 32

theorem fifSelMemG_gapeq (base : ByteArray) (h : base.size = 96) :
    fifSelMemG base =
      base ++ ffi.ByteArray.zeroes 32 ++ fifNopeSelShifted.toByteArray := by
  unfold fifSelMemG
  rw [toByteArray_write_eq fifNopeSelShifted base 128 (by rw [h]; omega)
    (by rw [h]; exact lt_usize 32 (by norm_num)), h]

theorem fifSelMemG_size (base : ByteArray) (h : base.size = 96) : (fifSelMemG base).size = 160 := by
  rw [fifSelMemG_gapeq base h, ByteArray.size_append, ByteArray.size_append, h,
    fifZeroes32_size, toByteArray_size]

theorem fifSelMemG_selector (base : ByteArray) (h : base.size = 96) :
    (fifSelMemG base).extract 128 132 = vatNopeSelector := by
  rw [fifSelMemG_gapeq base h]
  have hABsz : (base ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, h, fifZeroes32_size]
  rw [extract_append_right_window _ _ 128 132 (by rw [hABsz]), hABsz,
    show (128 : ℕ) - 128 = 0 from rfl, show (132 : ℕ) - 128 = 4 from rfl, toByteArray_eq_toBytesBE]
  native_decide

theorem fifCdMemG_size (base : ByteArray) (h : base.size = 96) (arg : UInt256) :
    (fifCdMemG base arg).size = 164 := by
  unfold fifCdMemG
  exact toByteArray_write32_size_of_le (fifSelMemG base) arg 132 160 164
    (fifSelMemG_size base h) (by rw [fifSelMemG_size base h]; omega) (by decide)

theorem fifCdMemG_read_window (base : ByteArray) (h : base.size = 96) (arg : UInt256) :
    (fifCdMemG base arg).readWithPadding 128 36 = vatNopeSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [fifCdMemG_size base h]), fifCdMemG,
    write32_eq _ (fifSelMemG base) 132 (by rw [toByteArray_size]) (by rw [fifSelMemG_size base h]; omega)]
  have hAsz : ((fifSelMemG base).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, fifSelMemG_size base h]; omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz : ((fifSelMemG base).extract 0 132 ++ arg.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h2 := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h2
  rw [extract_append_left _ _ 128 164 (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), fifSelMemG_selector base h,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

/-- Bridge: the encoder's concrete `fifNopeCdMem I arg` is `fifCdMemG (fifKeccakMem I) arg` by `rfl`. -/
theorem fifNopeCdMem_read_window (I : ExecutionEnv) (arg : UInt256) :
    (fifNopeCdMem I arg).readWithPadding 128 36 = vatNopeSelector ++ arg.toByteArray := by
  have hbridge : fifNopeCdMem I arg = fifCdMemG (fifKeccakMem I) arg := rfl
  rw [hbridge]
  exact fifCdMemG_read_window (fifKeccakMem I) (fifKeccakMem_size I) arg

theorem fifNopeEncode_eq (I : ExecutionEnv) (arg : UInt256)
    (hcanon : arg.toNat < EVM.addressModulus) :
    config.externalABI.encode? "nope" [.address (AccountAddress.ofNat arg.toNat)] =
      some ((fifNopeCdMem I arg).readWithPadding 128 36) := by
  rw [fifNopeCdMem_read_window I arg]
  have hword : EVM.word arg.toNat = arg := u256_ofNat_toNat arg
  have haddr : EVM.word (↑(AccountAddress.ofNat arg.toNat) : ℕ) = arg := by
    have hv : (↑(AccountAddress.ofNat arg.toNat) : ℕ) = arg.toNat := by
      simp only [AccountAddress.ofNat, Fin.ofNat]
      exact Nat.mod_eq_of_lt hcanon
    rw [hv, hword]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatNopeSelector,
    selectorBytes, hcanon, hword, haddr, word_toBytesBE_toByteArray_eq_toByteArray]

/-! ### nope guard + void CALL (⟨3546⟩ → ⟨3562⟩), bundling `callCoincides` (KissSuccess shape) -/

/-- The masked `vat` address word `vat & mask` (the CALL target). -/
abbrev fifVatM (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask

/-- The masked old `ilks[ilk].flip` (the nope arg). -/
abbrev fifNopeArg (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)))

theorem fifNopeArg_canonical (σ : AccountMap) (I : ExecutionEnv) :
    (fifNopeArg σ I).toNat < EVM.addressModulus := by
  rw [fifNopeArg, u256_land_comm solcAddrMask _]
  exact solcAddrMask_result_canonical _

theorem RD.catFileIlkFlipNopePostCall {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3546⟩
      (fifVatM σ I :: fifVatM σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨3696042234⟩ :: fifVatM σ I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifNopeCdMem I (fifNopeArg σ I)) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (fifVatM σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3562⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3696042234⟩ :: fifVatM σ I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (fifNopeCdMem I (fifNopeArg σ I)) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (AccountAddress.ofUInt256 (fifVatM σ I)) "nope" 0
        [.address (AccountAddress.ofNat (fifNopeArg σ I).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd3561⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3546⟩) (okPc := ⟨3558⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘpack, rd3562raw, houtsz⟩ :=
    RD.call rd3561 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat
          (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := rfl
    have rd3562 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3562⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨3696042234⟩ :: fifVatM σ I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (out.write 0 (fifNopeCdMem I (fifNopeArg σ I)) (⟨128⟩ : UInt256).toNat
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k' C' :=
      haw ▸ rd3562raw
    rw [hmin, byteArray_write_len_zero] at rd3562
    exact rd3562
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas) (callPerm := true)
      (targetWord := fifVatM σ I) (mem := fifNopeCdMem I (fifNopeArg σ I))
      (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl
      (by
        have h := fifNopeEncode_eq I (fifNopeArg σ I) (fifNopeArg_canonical σ I)
        simpa [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
          show (⟨36⟩ : UInt256).toNat = 36 from rfl] using h)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.catFileIlkFlipNopeNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3546⟩
      (fifVatM σ I :: fifVatM σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨3696042234⟩ :: fifVatM σ I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifNopeCdMem I (fifNopeArg σ I)) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (fifVatM σ I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨3546⟩) (okPc := ⟨3558⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.catFileIlkFlipNopeCallFailure {cA gh bl σ σ₀ A I} {g : Sat256}
    {flip ret sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3562⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨3696042234⟩ :: fifVatM σ I :: flip ::
        fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨3562⟩) (okPc := ⟨3578⟩) rd rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.catFileIlkFlipNopeCallSuccessToStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {flip ret sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3562⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨3696042234⟩ :: fifVatM σ I :: flip ::
        fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      mem aw rdata acc k C) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3582⟩
      (fifVatM σ I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      mem aw rdata acc k' C' := by
  obtain ⟨k1, C1, rd3580⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨3562⟩) (okPc := ⟨3578⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd3581 := RD.pop rd3580 (by native_decide) (by evm_ov)
  exact ⟨_, _, RD.pop rd3581 (by native_decide) (by evm_ov)⟩

/-! ### RMW `ilks[ilk].flip := flip` store (⟨3582⟩ → ⟨3626⟩) — `keccak(ilk,1)+0`, offset-0 address -/

/-- `twoWordHashMem` read of `[0,64)` = `key ++ slot`, for any base of size ≥ 64 (the size-96
    library lemma is too specific for the 164-byte post-call buffer). -/
theorem fifTwoWordRead0_64 (key slot : UInt256) {base : ByteArray} (hb : 64 ≤ base.size) :
    (twoWordHashMem key slot base).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hinner : ((UInt256.toByteArray key).write 0 base 0 32).size = base.size := by
    rw [write32_eq (UInt256.toByteArray key) base 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega)]
  have hleft :
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32 32).extract
        0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega),
      write32_read_below_len _ _ 32 0 32 (by rw [toByteArray_size]) (by rw [hinner]; omega)
        (by omega) (by rw [hinner]; omega) (by norm_num) (by norm_num),
      write32_read_prefix_len _ _ 0 32 (by rw [toByteArray_size]) (by omega) (by norm_num)
        (by norm_num) (by norm_num)]
    have h := @ByteArray.extract_zero_size (UInt256.toByteArray key)
    rwa [toByteArray_size] at h
  have hright :
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32 32).extract
        32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract' _ 32 32 (by norm_num) (by norm_num)
        (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega),
      write32_read_prefix_len _ _ 32 32 (by rw [toByteArray_size]) (by rw [hinner]; omega)
        (by norm_num) (by norm_num) (by norm_num)]
    have h := @ByteArray.extract_zero_size (UInt256.toByteArray slot)
    rwa [toByteArray_size] at h
  rw [show ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32 32).extract
      0 64 =
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32 32).extract
        0 32 ++
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32 32).extract
        32 64 by rw [ByteArray.extract_append_extract]; norm_num,
    hleft, hright]


theorem RD.catFileIlkFlipStore {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {vatM flip ret sel : UInt256} {mem rdata : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (rd : RD catBytecode ee g s0 ⟨3582⟩
      (vatM :: flip :: fileIlkFlipWhatWord ee :: fileIlkFlipIlkWord ee :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hperm : ee.perm = true) :
    ∃ k' C', RD catBytecode ee g s0 ⟨3626⟩
      (UInt256.land flip solcAddrMask :: solcAddrMask :: ⟨64⟩ :: ⟨0⟩ :: vatM :: flip ::
        fileIlkFlipWhatWord ee :: fileIlkFlipIlkWord ee :: ret :: sel :: [])
      (twoWordHashMem (fileIlkFlipIlkWord ee) ⟨1⟩ mem) (UInt256.ofNat 6) rdata
      (cA', sstoreAccountMap ee.codeOwner σ' (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord ee))
        (setAddressOffset0Word
          (solcSlotWord σ' ee (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord ee))) flip)) k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have rd3584 := rd.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3585 := rd3584.dup5 (by native_decide) (by evm_ov)
  have rd3586 := rd3585.dup2 (by native_decide) (by evm_ov)
  have rd3587 := rd3586.mstore 0 (wordAt0Mem (fileIlkFlipIlkWord ee) mem) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3589 := rd3587.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3591 := rd3589.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3592 := rd3591.mstore 0 (twoWordHashMem (fileIlkFlipIlkWord ee) ⟨1⟩ mem) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3594 := rd3592.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3595 := rd3594.dup1 (by native_decide) (by evm_ov)
  have rd3596 := rd3595.dup3 (by native_decide) (by evm_ov)
  have hkec :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (fileIlkFlipIlkWord ee) ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord ee) := by
    rw [fifTwoWordRead0_64 (fileIlkFlipIlkWord ee) ⟨1⟩ (by rw [hmem]; omega)]
    unfold solcMappingSlot
    exact mappingSlot_single (fileIlkFlipIlkWord ee) ⟨1⟩
  have rd3597 := rd3596.keccak256 0 (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord ee)) (UInt256.ofNat 6)
    (by native_decide) mem_cost hkec (by native_decide) (by evm_ov)
  have rd3597b := rd3597.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3598⟩ := rd3597b.sload (by native_decide) (by evm_ov)
  have rd3599 := rd3598.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3601 := rd3599.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3603 := rd3601.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3605 := rd3603.shl (by native_decide) (by evm_ov)
  have rd3606 := rd3605.sub (by native_decide) (by evm_ov)
  rw [hmask] at rd3606
  have rd3607 := rd3606.not (by native_decide) (by evm_ov)
  have rd3608 := rd3607.and (by native_decide) (by evm_ov)
  have rd3609 := rd3608.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3611 := rd3609.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3613 := rd3611.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3615 := rd3613.shl (by native_decide) (by evm_ov)
  have rd3616 := rd3615.sub (by native_decide) (by evm_ov)
  rw [hmask] at rd3616
  have rd3617 := rd3616.dup7 (by native_decide) (by evm_ov)
  have rd3618 := rd3617.dup2 (by native_decide) (by evm_ov)
  have rd3619 := rd3618.and (by native_decide) (by evm_ov)
  have rd3620 := rd3619.swap2 (by native_decide) (by evm_ov)
  have rd3621 := rd3620.dup3 (by native_decide) (by evm_ov)
  have rd3622 := rd3621.lor (by native_decide) (by evm_ov)
  rw [u256_land_comm solcAddrMask flip, setAddressOffset0Word_bytecode] at rd3622
  have rd3623 := rd3622.swap1 (by native_decide) (by evm_ov)
  have rd3624 := rd3623.swap3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3625⟩ := rd3624.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3625⟩


/-! ### hope calldata coupling — kiss-style over an abstract 164-byte base (in-bounds writes) -/

/-- `0x28ec8bf1 << 226` — the `hope` selector `0xa3b22fc4` in the top 4 bytes. -/
abbrev fifHopeSelShifted : UInt256 := UInt256.shiftLeft ⟨686590961⟩ ⟨226⟩

noncomputable def fifHopeSelMem (base : ByteArray) : ByteArray :=
  fifHopeSelShifted.toByteArray.write 0 base 128 32

noncomputable def fifHopeCdMem (base : ByteArray) (arg : UInt256) : ByteArray :=
  arg.toByteArray.write 0 (fifHopeSelMem base) 132 32

theorem fifHopeSelMem_size {base : ByteArray} (h : base.size = 164) :
    (fifHopeSelMem base).size = 164 := by
  unfold fifHopeSelMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, h, toByteArray_size]
  omega

theorem fifHopeSelMem_read64 {base : ByteArray} (h : base.size = 164)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fifHopeSelMem base).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fifHopeSelMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size]) (by rw [h]; omega) (by omega),
    hread64]

theorem fifHopeCdMem_size {base : ByteArray} (h : base.size = 164) (arg : UInt256) :
    (fifHopeCdMem base arg).size = 164 := by
  unfold fifHopeCdMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [fifHopeSelMem_size h]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, fifHopeSelMem_size h, toByteArray_size]
  omega

theorem fifHopeCdMem_read64 {base : ByteArray} (h : base.size = 164)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (arg : UInt256) :
    (fifHopeCdMem base arg).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fifHopeCdMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [fifHopeSelMem_size h]; omega)
    (by omega), fifHopeSelMem_read64 h hread64]

theorem fifHopeSelMem_selector {base : ByteArray} (h : base.size = 164) :
    (fifHopeSelMem base).extract 128 132 = vatHopeSelector := by
  unfold fifHopeSelMem
  rw [write32_eq _ _ 128 (by rw [toByteArray_size]) (by rw [h]; omega)]
  have hAsz : (base.extract 0 128).size = 128 := by rw [ByteArray.size_extract, h]; omega
  have hBsz : (fifHopeSelShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hABsz :
      (base.extract 0 128 ++ fifHopeSelShifted.toByteArray.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  rw [extract_append_left _ _ 128 132 (by rw [hABsz]; omega),
    extract_append_right_window _ _ 128 132 (by rw [hAsz]),
    hAsz, show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_extract_BA, show 0 + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega,
    toByteArray_eq_toBytesBE]
  native_decide

theorem fifHopeCdMem_read_window {base : ByteArray} (h : base.size = 164) (arg : UInt256) :
    (fifHopeCdMem base arg).readWithPadding 128 36 = vatHopeSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [fifHopeCdMem_size h]), fifHopeCdMem,
    write32_eq _ (fifHopeSelMem base) 132 (by rw [toByteArray_size]) (by rw [fifHopeSelMem_size h]; omega)]
  have hAsz : ((fifHopeSelMem base).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, fifHopeSelMem_size h]; omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz : ((fifHopeSelMem base).extract 0 132 ++ arg.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h2 := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h2
  rw [extract_append_left _ _ 128 164 (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), fifHopeSelMem_selector h,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem fifHopeEncode_eq {base : ByteArray} (h : base.size = 164) (arg : UInt256)
    (hcanon : arg.toNat < EVM.addressModulus) :
    config.externalABI.encode? "hope" [.address (AccountAddress.ofNat arg.toNat)] =
      some ((fifHopeCdMem base arg).readWithPadding 128 36) := by
  rw [fifHopeCdMem_read_window h arg]
  have hword : EVM.word arg.toNat = arg := u256_ofNat_toNat arg
  have haddr : EVM.word (↑(AccountAddress.ofNat arg.toNat) : ℕ) = arg := by
    have hv : (↑(AccountAddress.ofNat arg.toNat) : ℕ) = arg.toNat := by
      simp only [AccountAddress.ofNat, Fin.ofNat]; exact Nat.mod_eq_of_lt hcanon
    rw [hv, hword]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatHopeSelector,
    selectorBytes, hcanon, hword, haddr, word_toBytesBE_toByteArray_eq_toByteArray]

/-- The store's output buffer keeps the free pointer at `[64,96)` (writes at `[0,64)` and `[128,164)`
    don't touch it). -/
theorem twoWordHashMem_read64_preserve (key slot : UInt256) {mem : ByteArray} (h : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  have hinner : ((UInt256.toByteArray key).write 0 mem 0 32).size = mem.size := by
    rw [write32_eq (UInt256.toByteArray key) mem 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by rw [hinner]; omega) (by omega)
      (by rw [hinner]; omega),
    write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega), hread64]


/-! ### hope encoder (⟨3626⟩ → EXTCODESIZE guard ⟨3679⟩) -/

/-- Masked `vat` for the second (hope) call, read from the post-store map. -/
abbrev fifVat2M (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ ee ⟨3⟩)

theorem RD.catFileIlkFlipHopeEncode {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {vatM flip ret sel : UInt256} {mem rdata : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (rd : RD catBytecode ee g s0 ⟨3626⟩
      (UInt256.land flip solcAddrMask :: solcAddrMask :: ⟨64⟩ :: ⟨0⟩ :: vatM :: flip ::
        fileIlkFlipWhatWord ee :: fileIlkFlipIlkWord ee :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD catBytecode ee g s0 ⟨3679⟩
      (fifVat2M σ' ee :: fifVat2M σ' ee :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨2746363844⟩ :: fifVat2M σ' ee :: flip :: fileIlkFlipWhatWord ee ::
        fileIlkFlipIlkWord ee :: ret :: sel :: [])
      (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) rdata (cA', σ') k' C' := by
  have hmload : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd3628 := rd.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3628b⟩ := rd3628.sload (by native_decide) (by evm_ov)
  have rd3629 := rd3628b.dup4 (by native_decide) (by evm_ov)
  have rd3630 := rd3629.mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide) mem_cost hmload
    (by native_decide) (by evm_ov)
  have rd3631 := rd3630.push4 ⟨686590961⟩ (by native_decide) (by evm_ov)
  have rd3636 := rd3631.push1 ⟨226⟩ (by native_decide) (by evm_ov)
  have rd3638 := rd3636.shl (by native_decide) (by evm_ov)
  have rd3639 := rd3638.dup2 (by native_decide) (by evm_ov)
  have rd3640 := rd3639.mstore 0 (fifHopeSelMem mem) (UInt256.ofNat 6)
    (by native_decide) mem_cost
    (by unfold fifHopeSelMem; rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by native_decide) (by evm_ov)
  have rd3641 := rd3640.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3643 := rd3641.dup2 (by native_decide) (by evm_ov)
  have rd3644 := rd3643.add (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide] at rd3644
  have rd3645 := rd3644.swap3 (by native_decide) (by evm_ov)
  have rd3646 := rd3645.swap1 (by native_decide) (by evm_ov)
  have rd3647 := rd3646.swap3 (by native_decide) (by evm_ov)
  have rd3648 := rd3647.mstore 0 (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6)
    (by native_decide) mem_cost
    (by unfold fifHopeCdMem; rw [show (⟨132⟩ : UInt256).toNat = 132 from rfl])
    (by native_decide) (by evm_ov)
  have hmload2 : (if (⟨64⟩ : UInt256).toNat ≥ (fifHopeCdMem mem (UInt256.land flip solcAddrMask)).size
      ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
        ((fifHopeCdMem mem (UInt256.land flip solcAddrMask)).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [fifHopeCdMem_size hmem]; decide) (by decide)
      (fifHopeCdMem_read64 hmem hread64 _)
  have rd3649 := rd3648.swap3 (by native_decide) (by evm_ov)
  have rd3650 := rd3649.mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide) mem_cost hmload2
    (by native_decide) (by evm_ov)
  have rd3651 := rd3650.swap3 (by native_decide) (by evm_ov)
  have rd3652 := rd3651.swap1 (by native_decide) (by evm_ov)
  have rd3653 := rd3652.swap2 (by native_decide) (by evm_ov)
  have rd3654 := rd3653.and (by native_decide) (by evm_ov)
  have rd3655 := rd3654.swap4 (by native_decide) (by evm_ov)
  have rd3656 := rd3655.pop (by native_decide) (by evm_ov)
  have rd3657 := rd3656.push4 ⟨2746363844⟩ (by native_decide) (by evm_ov)
  have rd3662 := rd3657.swap3 (by native_decide) (by evm_ov)
  have rd3663 := rd3662.push1 ⟨36⟩ (by native_decide) (by evm_ov)
  have rd3665 := rd3663.dup1 (by native_decide) (by evm_ov)
  have rd3666 := rd3665.dup4 (by native_decide) (by evm_ov)
  have rd3667 := rd3666.add (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide] at rd3667
  have rd3668 := rd3667.swap4 (by native_decide) (by evm_ov)
  have rd3669 := rd3668.swap2 (by native_decide) (by evm_ov)
  have rd3670 := rd3669.swap3 (by native_decide) (by evm_ov)
  have rd3671 := rd3670.dup3 (by native_decide) (by evm_ov)
  have rd3672 := rd3671.swap1 (by native_decide) (by evm_ov)
  have rd3673 := rd3672.sub (by native_decide) (by evm_ov)
  rw [show UInt256.sub ⟨128⟩ ⟨128⟩ = ⟨0⟩ from by decide] at rd3673
  have rd3674 := rd3673.add (by native_decide) (by evm_ov)
  rw [show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd3674
  have rd3675 := rd3674.dup2 (by native_decide) (by evm_ov)
  have rd3676 := rd3675.dup4 (by native_decide) (by evm_ov)
  have rd3677 := rd3676.dup8 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3677.dup1 (by native_decide) (by evm_ov)⟩


/-! ### hope guard + void CALL (⟨3679⟩ → ⟨3695⟩) + epilogue → `RDret` -/

theorem fifHopeArg_canonical (flip : UInt256) :
    (UInt256.land flip solcAddrMask).toNat < EVM.addressModulus :=
  solcAddrMask_result_canonical flip

theorem RD.catFileIlkFlipHopePostCall {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {mem : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3679⟩
      (fifVat2M σ' I :: fifVat2M σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨2746363844⟩ :: fifVat2M σ' I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) ByteArray.empty
      (cA', σ') k C)
    (hmem : mem.size = 164)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ' (fifVat2M σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (fifVat2M σ' I)) "hope" 0
        [.address (AccountAddress.ofNat (UInt256.land flip solcAddrMask).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd3694⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3679⟩) (okPc := ⟨3691⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k', C', hΘpack, rd3695raw, houtsz⟩ :=
    RD.call rd3694 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat
          (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := rfl
    have rd3695 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (out.write 0 (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (⟨128⟩ : UInt256).toNat
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k' C' :=
      haw ▸ rd3695raw
    rw [hmin, byteArray_write_len_zero] at rd3695
    exact rd3695
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas) (callPerm := true)
      (targetWord := fifVat2M σ' I) (mem := fifHopeCdMem mem (UInt256.land flip solcAddrMask))
      (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl
      (by
        have h := fifHopeEncode_eq hmem (UInt256.land flip solcAddrMask) (fifHopeArg_canonical flip)
        simpa [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
          show (⟨36⟩ : UInt256).toNat = 36 from rfl] using h)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.catFileIlkFlipHopeNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {mem : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3679⟩
      (fifVat2M σ' I :: fifVat2M σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨2746363844⟩ :: fifVat2M σ' I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) ByteArray.empty
      (cA', σ') k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ' (fifVat2M σ' I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨3679⟩) (okPc := ⟨3691⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.catFileIlkFlipHopeCallFailure {cA gh bl σ σ₀ A I} {g : Sat256}
    {flip ret sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
      (⟨0⟩ :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
        fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨3695⟩) (okPc := ⟨3711⟩) rd rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.catFileIlkFlipHopeCallSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    {flip sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
        fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ⟨302⟩ :: sel :: [])
      mem aw rdata acc k C) :
    RDret catBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd3713⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨3695⟩) (okPc := ⟨3711⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd3714 := rd3713.pop (by native_decide) (by evm_ov)
  have rd3715 := rd3714.pop (by native_decide) (by evm_ov)
  have rd3716 := rd3715.pop (by native_decide) (by evm_ov)
  have rd3719 := rd3716.push2 ⟨1030⟩ (by native_decide) (by evm_ov)
  have rd1030 := rd3719.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1031 := rd1030.jumpdest (by native_decide) (by evm_ov)
  have rd1032 := rd1031.pop (by native_decide) (by evm_ov)
  have rd1033 := rd1032.pop (by native_decide) (by evm_ov)
  have rd1034 := rd1033.pop (by native_decide) (by evm_ov)
  have rd302 := rd1034.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd303 := rd302.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd303 (by native_decide) (by simp)

end Benchmarks.Dss.Cat
