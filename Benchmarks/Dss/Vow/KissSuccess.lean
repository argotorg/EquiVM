import Benchmarks.Dss.Vow.Kiss

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `kiss(uint256)` success path -/

abbrev kissHealSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨1021227399⟩ ⟨226⟩

abbrev kissHealSelector : UInt256 :=
  ⟨4084909596⟩

abbrev kissHealOutPtr : UInt256 :=
  ⟨128⟩

abbrev kissHealOutSize : UInt256 :=
  ⟨0⟩

abbrev kissHealInSize : UInt256 :=
  UInt256.add (UInt256.sub kissHealOutPtr kissHealOutPtr) ⟨36⟩

abbrev kissHealEndPtr : UInt256 :=
  UInt256.add kissHealOutPtr ⟨36⟩

noncomputable def kissHealSelectorMem (mem : ByteArray) : ByteArray :=
  kissHealSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def kissHealCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (kissRad I).toByteArray.write 0 (kissHealSelectorMem mem) 132 32

theorem kissHealSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (kissHealSelectorMem mem).size = 164 := by
  unfold kissHealSelectorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem kissHealSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (kissHealSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kissHealSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem kissHealCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (kissHealCalldataMem I mem).size = 164 := by
  unfold kissHealCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [kissHealSelectorMem_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, kissHealSelectorMem_size hmem, toByteArray_size]
  omega

theorem kissHealCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (kissHealCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kissHealCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [kissHealSelectorMem_size hmem]; omega) (by omega),
    kissHealSelectorMem_read64 hmem hread64]

theorem kissHealSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (kissHealSelectorMem mem).extract 128 132 = vatHealSelector := by
  unfold kissHealSelectorMem
  rw [write32_eq _ _ 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (kissHealSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hABsz :
      (mem.extract 0 128 ++ kissHealSelectorShifted.toByteArray.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  rw [extract_append_left _ _ 128 132 (by rw [hABsz]; omega),
    extract_append_right_window _ _ 128 132 (by rw [hAsz]),
    hAsz, show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_extract_BA,
    show 0 + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega,
    toByteArray_eq_toBytesBE]
  native_decide

theorem kissHealCalldataMem_read128_36 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (kissHealCalldataMem I mem).readWithPadding 128 36 =
      vatHealSelector ++ (kissRad I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [kissHealCalldataMem_size I hmem]), kissHealCalldataMem,
    write32_eq _ (kissHealSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [kissHealSelectorMem_size hmem]; omega)]
  have hAsz : ((kissHealSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, kissHealSelectorMem_size hmem]
    omega
  have hBsz : ((kissRad I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((kissHealSelectorMem mem).extract 0 132 ++
        (kissRad I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      (kissRad I).toByteArray.extract 0 32 = (kissRad I).toByteArray := by
    have h := @ByteArray.extract_zero_size (kissRad I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), kissHealSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem kissHealInSize_eq : kissHealInSize = ⟨36⟩ := by
  unfold kissHealInSize kissHealOutPtr
  native_decide

theorem kissHealEndPtr_eq : kissHealEndPtr = ⟨164⟩ := by
  unfold kissHealEndPtr kissHealOutPtr
  native_decide

theorem kissHealEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "heal" [.int (Int.ofNat (kissRad I).toNat)] =
      some ((kissHealCalldataMem I mem).readWithPadding
        kissHealOutPtr.toNat kissHealInSize.toNat) := by
  rw [kissHealInSize_eq]
  change config.externalABI.encode? "heal" [.int (Int.ofNat (kissRad I).toNat)] =
    some ((kissHealCalldataMem I mem).readWithPadding 128 36)
  rw [kissHealCalldataMem_read128_36 I hmem]
  have hlt : (kissRad I).toNat < EVM.twoPow 256 := (kissRad I).val.isLt
  have hword : EVM.word (kissRad I).toNat = kissRad I := by
    show UInt256.ofNat (kissRad I).toNat = kissRad I
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, vatHealSelector, selectorBytes, hlt, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

set_option maxHeartbeats 1000000 in
theorem RD.vowKissSurplusEnoughStoresAsh
    {cA gh bl σ σ₀ A I} {g sel vatDai : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1745⟩
      (vatDai :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hashEnoughDai : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ' I).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o
      (cA',
        sstoreAccountMap I.codeOwner σ' ⟨6⟩
          (UInt256.sub (vowSlotWord ⟨6⟩ σ' I) (kissRad I))) k' C' := by
  have rd1746 := rd.dup2 (by native_decide) (by evm_ov)
  have rd1747₀ := rd1746.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (kissRad I) vatDai = ⟨0⟩ :=
    ugt_zero hvatDaiEnough
  have rd1747 := rd1747₀
  rw [hgt] at rd1747
  have rd1748₀ := rd1747.iszero (by native_decide) (by evm_ov)
  have rd1748 := rd1748₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1748
  have rd1751 := rd1748.push2 ⟨1823⟩ (by native_decide) (by evm_ov)
  have rd1823 := rd1751.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd1824 := rd1823.jumpdest (by native_decide) (by evm_ov)
  have rd1827 := rd1824.push2 ⟨1835⟩ (by native_decide) (by evm_ov)
  have rd1829 := rd1827.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1830, C1830, rd1830₀⟩ := rd1829.sload (by native_decide) (by evm_ov)
  have rd1830 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1830⟩
      (vowSlotWord ⟨6⟩ σ' I :: ⟨1835⟩ :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (cA', σ') k1830 C1830 := by
    simpa [vowSlotWord, solcSlotWord] using rd1830₀
  have rd1831 := rd1830.dup3 (by native_decide) (by evm_ov)
  have rd1834 := rd1831.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1834.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1835⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vowSlotWord ⟨6⟩ σ' I) (b := kissRad I) (ret := ⟨1835⟩)
    (R := [kissRad I, ⟨412⟩, sel])
    (by simpa using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hashEnoughDai (by jump_dest) (by jump_dest) (by simp)
  have rd1836 := rd1835.jumpdest (by native_decide) (by evm_ov)
  have rd1838 := rd1836.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1839⟩ := rd1838.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa using rd1839⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowKissToHealExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1903⟩
      (kissDaiTargetWord σ' I :: kissDaiTargetWord σ' I :: kissHealOutSize ::
        kissHealOutPtr :: kissHealInSize :: kissHealOutPtr :: kissHealOutSize ::
        kissHealEndPtr :: kissHealSelector :: kissDaiTargetWord σ' I ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      (kissHealCalldataMem I mem) (UInt256.ofNat 6) o (cA', σ') k' C' := by
  let target := kissDaiTargetWord σ' I
  have rd1841 := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1842, C1842, rd1842₀⟩ := rd1841.sload (by native_decide) (by evm_ov)
  have rd1842 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1842⟩
      (vowSlotWord ⟨1⟩ σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o (cA', σ') k1842 C1842 := by
    simpa [vowSlotWord, solcSlotWord] using rd1842₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hHealMem : (kissHealCalldataMem I mem).size = 164 :=
    kissHealCalldataMem_size I hmem
  have hHealRead64 :
      (kissHealCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    kissHealCalldataMem_read64 I hmem hread64
  have hmload64Heal :
      (if (⟨64⟩ : UInt256).toNat ≥ (kissHealCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((kissHealCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hHealMem]; decide) (by decide) hHealRead64
  have rd1903 := evm_run rd1842 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨1021227399⟩,
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 0 (kissHealSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup5,
    swap1,
    raw mstore 0 (kissHealCalldataMem I mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Heal (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 kissHealSelector,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 kissHealOutSize,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [target, kissDaiTargetWord, kissHealSelectorShifted, kissHealSelector,
      kissHealSelectorMem, kissHealCalldataMem, kissHealOutPtr, kissHealOutSize,
      kissHealInSize, kissHealEndPtr, vowSlotWord, solcSlotWord, solcAddrMask] using rd1903⟩

theorem RD.vowKissHealNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (kissDaiTargetWord σ' I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1903⟩ := RD.vowKissToHealExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1903⟩) (okPc := ⟨1915⟩) rd1903
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowKissToHealCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (kissDaiTargetWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1918⟩
      (gasWord :: kissDaiTargetWord σ' I :: kissHealOutSize :: kissHealOutPtr ::
        kissHealInSize :: kissHealOutPtr :: kissHealOutSize :: kissHealEndPtr ::
        kissHealSelector :: kissDaiTargetWord σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissHealCalldataMem I mem) (UInt256.ofNat 6) o (cA', σ') k' C' := by
  obtain ⟨_, _, rd1903⟩ := RD.vowKissToHealExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k1918, C1918, rd1918⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1903⟩) (okPc := ⟨1915⟩) rd1903
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1918, C1918, by simpa using rd1918⟩

theorem RD.vowKissHealPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (kissDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
        (kissHealCalldataMem I mem) (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (EVM.address (kissVatAddress σ' I)) "heal" 0
        [.int (Int.ofNat (kissRad I).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1918⟩ :=
    RD.vowKissToHealCall rd hmem hread64 hcodeSize
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k1919, C1919, hΘpack, rd1919raw, houtsz⟩ :=
    RD.call rd1918 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k1919, C1919, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          kissHealOutPtr.toNat kissHealInSize.toNat)
          kissHealOutPtr.toNat kissHealOutSize.toNat) = UInt256.ofNat 6 := by
      rw [kissHealInSize_eq]
      unfold kissHealOutPtr kissHealOutSize
      native_decide
    have hmin : (min kissHealOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold kissHealOutSize
      rfl
    have rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
        (out.write 0 (kissHealCalldataMem I mem) kissHealOutPtr.toNat
          (min kissHealOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k1919 C1919 :=
      haw ▸ rd1919raw
    rw [hmin, byteArray_write_len_zero] at rd1919
    exact rd1919
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := kissDaiTargetWord σ' I)
      (mem := kissHealCalldataMem I mem) (inOff := kissHealOutPtr)
      (inSize := kissHealInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ' I) (kissHealEncode_eq I hmem) ?_
    simpa [initState, hperm] using hΘ

theorem RD.vowKissHealCallFailure
    {cA gh bl σ σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1919⟩) (okPc := ⟨1935⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.vowKissHealCallSuccessToReturn
    {cA gh bl σ σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨412⟩
      [sel] mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1937⟩ := RD.solcCallSuccessGuardOk
    (pc := ⟨1919⟩) (okPc := ⟨1935⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd1938 := rd1937.pop (by native_decide) (by evm_ov)
  have rd1939 := rd1938.pop (by native_decide) (by evm_ov)
  have rd1940 := rd1939.pop (by native_decide) (by evm_ov)
  have rd1941 := rd1940.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1941.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowKissHealCallSuccess
    {cA gh bl σ σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd412⟩ := RD.vowKissHealCallSuccessToReturn rd
  have rd413 := rd412.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd413 (by native_decide) (by simp)

theorem RD.vowKissHealCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o (cA', σ') k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (kissDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector ::
        kissDaiTargetWord σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissHealCalldataMem I mem) (UInt256.ofNat 6) ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨_, _, _, rd1918⟩ := RD.vowKissToHealCall rd hmem hread64 hcodeSize
  obtain ⟨k1919, C1919, rd1919raw⟩ := RD.callDepthLimit
    (by simpa [kissHealOutSize] using rd1918)
    (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        kissHealOutPtr.toNat kissHealInSize.toNat)
        kissHealOutPtr.toNat kissHealOutSize.toNat) = UInt256.ofNat 6 := by
    rw [kissHealInSize_eq]
    unfold kissHealOutPtr kissHealOutSize
    native_decide
  have hmin : (min kissHealOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold kissHealOutSize
    rfl
  have rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector ::
        kissDaiTargetWord σ' I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (ByteArray.empty.write 0 (kissHealCalldataMem I mem) kissHealOutPtr.toNat
        (min kissHealOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA', σ') k1919 C1919 :=
    haw ▸ rd1919raw
  rw [hmin, byteArray_write_len_zero] at rd1919
  exact ⟨k1919, C1919, rd1919⟩

theorem RD.vowKissDaiCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd1703⟩ :=
    RD.vowKissToDaiStaticcall hreach hsz36 hsize hashEnough hcodeSize
  obtain ⟨k1704, C1704, rd1704raw⟩ :=
    RD.solcStaticcallDepthLimit rd1703 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (kissDaiOutPtr I).toNat (kissDaiInSize I).toNat)
        (kissDaiOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
    rw [kissDaiOutPtr_eq, kissDaiInSize_eq]
    native_decide
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd1704 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (ByteArray.empty.write 0 (kissDaiCalldataMem I) (kissDaiOutPtr I).toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k1704 C1704 :=
    haw ▸ rd1704raw
  rw [hmin, byteArray_write_len_zero] at rd1704
  exact ⟨k1704, C1704, rd1704⟩

theorem typedCallViaEVM_zero_setSubstate {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A'
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

-- LIBRARY CANDIDATE: converts the word-level extcodesize guard used by traces into the
-- source-level positive code-size fact used by `evalExpr_extCodeSize`.
theorem extCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

-- LIBRARY CANDIDATE: zero counterpart of `extCodeSizeWord_ne_zero_lookup_code_pos`.
theorem extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem kissDaiTargetWord_sstore_ash (σ : AccountMap) (I : ExecutionEnv) (val : UInt256) :
    kissDaiTargetWord (sstoreAccountMap I.codeOwner σ ⟨6⟩ val) I =
      kissDaiTargetWord σ I := by
  have hslot := sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩ ⟨6⟩ val
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨6⟩)
  simpa [kissDaiTargetWord, vowSlotWord, solcSlotWord] using
    congrArg (fun word => UInt256.land word solcAddrMask) hslot

theorem kissVatAddress_eq_daiTarget_account (σ : AccountMap) (I : ExecutionEnv) :
    kissVatAddress σ I = AccountAddress.ofUInt256 (kissDaiTargetWord σ I) := by
  apply Fin.ext
  simp [kissVatAddress, kissDaiTargetWord, vowAddressReturnWord,
    accountAddress_ofUInt256_eq_ofNat_toNat]

-- LIBRARY CANDIDATE: field preservation facts for `Solm.EVM.storageStore`.
theorem storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

-- LIBRARY CANDIDATE: field preservation facts for `Solm.EVM.storageStore`.
theorem storageStore_genesisBlockHeader
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

-- LIBRARY CANDIDATE: field preservation facts for `Solm.EVM.storageStore`.
theorem storageStore_blocks (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem vowKissSourceHealNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State}
    {outDai : ByteArray} {vatDai AshNew : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ I) (kissRad I))
    (hvatNoCodeHeal :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
  let locals1 := kissLocalsVatDai I vatDai
  let locals2 := kissLocalsVatDaiAshNew I vatDai AshNew
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, kissLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "rad") (value := kissRad I) (kissLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (kissLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.internalCall "sub" [.storage AshRef, .var "rad"] "AshNew")
        (.ok { contract := contract, locals := locals2 } evmDai) := by
    simpa [locals1, locals2, kissFrameAshNew, kissLocalsAshNew, kissLocalsVatDaiAshNew] using
      (kissInternalSubReturn I evmDai (locals := locals1)
        (AshVal := vowSlotWord ⟨6⟩ σ I) (AshNew := AshNew) hAshLoadDai
        (by simpa [locals1] using kissLocalsVatDai_get_rad I vatDai)
        (by simp [locals1, kissLocalsVatDai, kissLocals])
        hAshNew hashEnough)
  have hAshNewVar :
      evalExpr? config { contract := contract, locals := locals2 } evmDai (.var "AshNew") =
        .ok (.int (Int.ofNat AshNew.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDaiAshNew I vatDai AshNew)
        (name := "AshNew") (value := AshNew)
        (kissLocalsVatDaiAshNew_get_AshNew I vatDai AshNew)
  have hassignAsh :
      assignStorageRef? config { contract := contract, locals := locals2 } evmDai
        .storage AshRef (.int (Int.ofNat AshNew.toNat)) =
          .ok ({ contract := contract, locals := locals2 }, evmAsh) := by
    simpa [evmAsh, locals2] using
      assign_kissAshStorage evmDai (locals := locals2) AshNew
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hvatLoadAsh :
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I := by
    calc
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩
          = Solm.EVM.storageLoad
              (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
              evmDai.executionEnv.codeOwner ⟨1⟩ := by
            simp [evmAsh, storageStore_executionEnv]
      _ = Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ := by
            exact storageLoad_storageStore_ne evmDai evmDai.executionEnv.codeOwner
              (by decide : (⟨1⟩ : UInt256) ≠ ⟨6⟩)
      _ = vowSlotWord ⟨1⟩ σ I := hvatLoadDai
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [kissVatAddress, vowAddressReturnWord, hvatLoadAsh] using
      evalExpr_kissVatStorage (evm := evmAsh) (locals := locals2)
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvatHeal (by simpa [evmAsh] using hvatNoCodeHeal)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .le (.var "rad") (.storage AshRef)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
            (perm := false),
          .require (.binary .le (.var "rad") (.var "vatDai")),
          .internalCall "sub" [.storage AshRef, .var "rad"] "AshNew",
          .assign .storage AshRef (.var "AshNew"),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal hsubStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hAshNewVar hassignAsh) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardHeal)
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceHealCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmHeal : EVM.State}
    {outDai outHeal : ByteArray} {vatDai AshNew : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ I) (kissRad I))
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (EVM.address (kissVatAddress σ I)) "heal" 0
        [.int (Int.ofNat (kissRad I).toNat)] (false, evmHeal, outHeal) true) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
  let locals1 := kissLocalsVatDai I vatDai
  let locals2 := kissLocalsVatDaiAshNew I vatDai AshNew
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, kissLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "rad") (value := kissRad I) (kissLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (kissLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.internalCall "sub" [.storage AshRef, .var "rad"] "AshNew")
        (.ok { contract := contract, locals := locals2 } evmDai) := by
    simpa [locals1, locals2, kissFrameAshNew, kissLocalsAshNew, kissLocalsVatDaiAshNew] using
      (kissInternalSubReturn I evmDai (locals := locals1)
        (AshVal := vowSlotWord ⟨6⟩ σ I) (AshNew := AshNew) hAshLoadDai
        (by simpa [locals1] using kissLocalsVatDai_get_rad I vatDai)
        (by simp [locals1, kissLocalsVatDai, kissLocals])
        hAshNew hashEnough)
  have hAshNewVar :
      evalExpr? config { contract := contract, locals := locals2 } evmDai (.var "AshNew") =
        .ok (.int (Int.ofNat AshNew.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDaiAshNew I vatDai AshNew)
        (name := "AshNew") (value := AshNew)
        (kissLocalsVatDaiAshNew_get_AshNew I vatDai AshNew)
  have hassignAsh :
      assignStorageRef? config { contract := contract, locals := locals2 } evmDai
        .storage AshRef (.int (Int.ofNat AshNew.toNat)) =
          .ok ({ contract := contract, locals := locals2 }, evmAsh) := by
    simpa [evmAsh, locals2] using
      assign_kissAshStorage evmDai (locals := locals2) AshNew
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hvatLoadAsh :
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I := by
    calc
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩
          = Solm.EVM.storageLoad
              (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
              evmDai.executionEnv.codeOwner ⟨1⟩ := by
            simp [evmAsh, storageStore_executionEnv]
      _ = Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ := by
            exact storageLoad_storageStore_ne evmDai evmDai.executionEnv.codeOwner
              (by decide : (⟨1⟩ : UInt256) ≠ ⟨6⟩)
      _ = vowSlotWord ⟨1⟩ σ I := hvatLoadDai
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [kissVatAddress, vowAddressReturnWord, hvatLoadAsh] using
      evalExpr_kissVatStorage (evm := evmAsh) (locals := locals2)
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatHeal (by simpa [evmAsh] using hvatCodeHeal)
  have hargsHeal :
      evalExprs? config { contract := contract, locals := locals2 } evmAsh [.var "rad"] =
        .ok [.int (Int.ofNat (kissRad I).toNat)] := by
    simpa [locals2] using
      evalExprs_kissRad (evm := evmAsh) (I := I)
        (locals := kissLocalsVatDaiAshNew I vatDai AshNew)
        (kissLocalsVatDaiAshNew_get_rad I vatDai AshNew)
  have hcallHealStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmAsh
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvatHeal (by simp [evalExpr?, pure])
      hargsHeal hcallHeal
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .le (.var "rad") (.storage AshRef)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
            (perm := false),
          .require (.binary .le (.var "rad") (.var "vatDai")),
          .internalCall "sub" [.storage AshRef, .var "rad"] "AshNew",
          .assign .storage AshRef (.var "AshNew"),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal hsubStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hAshNewVar hassignAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHeal) ?_
    exact ExecBlock.consRevert hcallHealStmt
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissHealNoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai AshNew : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σAsh_evm : AccountMap}
    {evmDai : EVM.State} {mem outDai : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1839 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
      [kissRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) outDai
      (cA', σAsh_evm) k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSizeEvm :
      Reasoning.Theory.extCodeSizeWord σAsh_evm (kissDaiTargetWord σAsh_evm I) =
        ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ_solm I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ_solm I) (kissRad I))
    (hvatNoCodeHeal :
      (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowKissHealNoCode rd1839 hmem hread64 hcodeSizeEvm
  have hbody := vowKissSourceHealNoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (outDai := outDai) (vatDai := vatDai) (AshNew := AshNew)
    hwv hashEnough hvatCode hcallDai hdecDai hvatDaiEnough hAshLoadDai hvatLoadDai
    hAshNew hvatNoCodeHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissHealCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmHeal : EVM.State} {mem outDai outHeal rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨0⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ_solm I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ_solm I) (kissRad I))
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (EVM.address (kissVatAddress σ_solm I)) "heal" 0
        [.int (Int.ofNat (kissRad I).toNat)] (false, evmHeal, outHeal) true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowKissHealCallFailure rd1919 hrdataSize
  have hbody := vowKissSourceHealCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmHeal := evmHeal) (outDai := outDai) (outHeal := outHeal)
    (vatDai := vatDai) (AshNew := AshNew) hwv hashEnough hvatCode hcallDai hdecDai
    hvatDaiEnough hAshLoadDai hvatLoadDai hAshNew hvatCodeHeal hcallHeal
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissHealSuccessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai AshNew : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmHeal : EVM.State} {mem outDai outHeal rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
      (⟨1⟩ :: kissHealEndPtr :: kissHealSelector :: target ::
        kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ_solm I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ_solm I) (kissRad I))
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (EVM.address (kissVatAddress σ_solm I)) "heal" 0
        [.int (Int.ofNat (kissRad I).toNat)] (true, evmHeal, outHeal) true)
    (hdecHeal : config.externalABI.decode? "heal" outHeal = some [])
    (hcreated : acc.1 = evmHeal.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmHeal.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hret := RD.vowKissHealCallSuccess rd1919
  have hbody := vowKissSourceSuccess (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmHeal := evmHeal) (outDai := outDai) (outHeal := outHeal)
    (vatDai := vatDai) (AshNew := AshNew) hwv hashEnough hvatCode hcallDai hdecDai
    hvatDaiEnough hAshLoadDai hvatLoadDai hAshNew hvatCodeHeal hcallHeal hdecHeal
  have henc : returnEquiv ByteArray.empty none kissTransition.returnType := by
    rw [show kissTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated hAccountsFinal henc

set_option maxHeartbeats 0 in
theorem vowKissBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 36
  · exact vowKissShort hcode hsize hperm hwv hsz4 hshort hsel hAccounts
  have hsz36 : 36 ≤ I.calldata.size := by omega
  have hdispatch : dispatchMsg contract I.calldata = some kissTransition :=
    vowDispatch_kiss hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I) := by
    simpa [kissLocals] using vowDecode_kiss_ok (I := I) hsz36
  have hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C :=
    vowReachKissBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  by_cases hnotEnough : (vowSlotWord ⟨6⟩ σ_evm I).toNat < (kissRad I).toNat
  · exact vowKissNotEnoughAshBodyCore hcode hwv hsz36 hsize hdispatch hdecode
      hreach hAccounts hnotEnough
  have hashEnoughEvm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_evm I).toNat := by
    omega
  by_cases hcodeSizeDai :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩
  · exact vowKissNoVatCodeBodyCore hcode hwv hsz36 hsize hdispatch hdecode hreach
      hAccounts hashEnoughEvm hcodeSizeDai
  have hcodeSizeDaiNE :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) ≠ ⟨0⟩ :=
    hcodeSizeDai
  have hAshOrig : vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hVatOrig : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTargetOrig : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVatOrig]
  have hVatAddrOrig : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    simp [kissVatAddress, vowAddressReturnWord, hVatOrig]
  have hashEnoughSolm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat := by
    simpa [← hAshOrig] using hashEnoughEvm
  have hcodeSizeSolmNE :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hcodeSizeDaiNE
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    rw [hsame, hTargetOrig]
    exact hzero
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [initState, State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := kissDaiTargetWord σ_solm I)
        (addr := kissVatAddress σ_solm I)
        (kissVatAddress_eq_daiTarget_account σ_solm I) hcodeSizeSolmNE
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨cA_dai, σ_dai, zDai, oDai, A_dai, k1704, C1704,
        rd1704, hcallDai, hosz⟩ :=
      RD.vowKissDaiPostCall hreach hsz36 hsize hashEnoughEvm hcodeSizeDaiNE hdepthLt
    cases zDai
    · exact vowKissDaiCallFailureBodyCore (cA' := cA_dai) (σ'_evm := σ_dai)
        (A'_evm := A_dai) hcode hwv hdispatch hdecode (by simpa using rd1704)
        (by simpa using hcallDai) hosz hashEnoughEvm hvatCodeSolm hAccounts
    · have rd1704True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
          (⟨1⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
            kissDaiTargetWord σ_evm I :: kissRad I :: ⟨412⟩ :: vowSelWord I :: [])
          (oDai.write 0 (kissDaiCalldataMem I) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat oDai.size)).toNat)
          (UInt256.ofNat 6) oDai (cA_dai, σ_dai) k1704 C1704 := by
        simpa using rd1704
      have hcallDaiTrue :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
            (true,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_dai
                  substate := A_dai
                  createdAccounts := cA_dai },
              oDai) false := by
        simpa using hcallDai
      by_cases ho32 : 32 ≤ oDai.size
      · let vatDai : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (oDai.extract 0 32))
        by_cases hinsuff : vatDai.toNat < (kissRad I).toNat
        · exact vowKissDaiSuccessInsufficientSurplusBodyCore
            (cA' := cA_dai) (σ'_evm := σ_dai) (A'_evm := A_dai)
            hcode hwv hdispatch hdecode rd1704True hcallDaiTrue hosz ho32
            hashEnoughEvm hvatCodeSolm hAccounts (by simpa [vatDai] using hinsuff)
        have hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat := by omega
        have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat oDai.size)).toNat = 32 :=
          kissDaiMin32_toNat_of_ge ho32 hosz
        have rd1704Write := rd1704True
        rw [hmin] at rd1704Write
        obtain ⟨_, _, rd1722⟩ :=
          RD.vowKissDaiCallSuccessToDecode rd1704Write (by simp)
        have hmem : (oDai.write 0 (kissDaiCalldataMem I) 128 32).size = 164 :=
          kissDaiWrite_size I oDai 32 (by omega) ho32
        have hread64 :
            (oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          kissDaiWrite_read64 I oDai 32 (by omega) ho32
        have hmload64 :
            (if (⟨64⟩ : UInt256).toNat ≥
                  (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
                  (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
        have hmload128 :
            (if (⟨128⟩ : UInt256).toNat ≥
                  (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                ((oDai.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
                  (⟨128⟩ : UInt256).toNat 32))) =
              vatDai := by
          have hnot :
              ¬ ((⟨128⟩ : UInt256).toNat ≥
                    (oDai.write 0 (kissDaiCalldataMem I) 128 32).size
                  ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
            rw [hmem]
            native_decide
          rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            kissDaiWrite_read128_32 I oDai ho32]
        obtain ⟨_, _, rd1745⟩ :=
          RD.vowKissDaiReturnDecodeOk (retWord := vatDai) rd1722 ho32 hosz
            hmload64 hmload128
        have hAshDaiEvm : vowSlotWord ⟨6⟩ σ_dai I = vowSlotWord ⟨6⟩ σ_evm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_evm)
            (slot := ⟨6⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_evm)
            hcallDaiTrue
          simpa [initState, vowSlotWord, solcSlotWord] using h
        have hVatDaiEvm : vowSlotWord ⟨1⟩ σ_dai I = vowSlotWord ⟨1⟩ σ_evm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_evm)
            (slot := ⟨1⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_evm)
            hcallDaiTrue
          simpa [initState, vowSlotWord, solcSlotWord] using h
        have hashEnoughDai : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_dai I).toNat := by
          simpa [hAshDaiEvm] using hashEnoughEvm
        let AshNew : UInt256 := UInt256.sub (vowSlotWord ⟨6⟩ σ_solm I) (kissRad I)
        have hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ_solm I) (kissRad I) := rfl
        have hAshNewEvm :
            UInt256.sub (vowSlotWord ⟨6⟩ σ_dai I) (kissRad I) = AshNew := by
          simp [AshNew, hAshDaiEvm, hAshOrig]
        obtain ⟨σ_dai_solm, A_dai_solm, hcallDaiSolmRaw, hStateDaiRaw⟩ :=
          typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDaiTrue)
            (by simp [initState]) hAccounts
        let evmDaiEvm :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai
              substate := A_dai
              createdAccounts := cA_dai }
        let evmDaiSolm :=
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dai_solm
              substate := A_dai_solm
              createdAccounts := cA_dai }
        have hcallDaiSolm :
            typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
              (true, evmDaiSolm, oDai) false := by
          simpa [evmDaiSolm, hVatAddrOrig] using hcallDaiSolmRaw
        have hStateDai : EVMStateEquiv evmDaiEvm evmDaiSolm := by
          simpa [evmDaiEvm, evmDaiSolm] using hStateDaiRaw
        have hdecDai :
            config.externalABI.decode? "dai" oDai =
              some [.int (Int.ofNat vatDai.toNat)] := by
          simpa [vatDai] using kissDaiDecode_ok (o := oDai) ho32
        have hAshLoadDai :
            Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨6⟩ =
              vowSlotWord ⟨6⟩ σ_solm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_solm)
            (slot := ⟨6⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_solm)
            hcallDaiSolm
          simpa [evmDaiSolm, initState, Solm.EVM.storageLoad, vowSlotWord, solcSlotWord]
            using h
        have hvatLoadDai :
            Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨1⟩ =
              vowSlotWord ⟨1⟩ σ_solm I := by
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_solm)
            (slot := ⟨1⟩) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_solm)
            hcallDaiSolm
          simpa [evmDaiSolm, initState, Solm.EVM.storageLoad, vowSlotWord, solcSlotWord]
            using h
        obtain ⟨k1839, C1839, rd1839Raw⟩ :=
          RD.vowKissSurplusEnoughStoresAsh rd1745 hvatDaiEnough hashEnoughDai hperm
        let σAshEvm : AccountMap := sstoreAccountMap I.codeOwner σ_dai ⟨6⟩ AshNew
        have rd1839 : RD vowBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1839⟩
            [kissRad I, ⟨412⟩, vowSelWord I]
            (oDai.write 0 (kissDaiCalldataMem I) 128 32)
            (UInt256.ofNat 6) oDai (cA_dai, σAshEvm) k1839 C1839 := by
          simpa [σAshEvm, hAshNewEvm] using rd1839Raw
        let evmAshSolm :=
          Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨6⟩ AshNew
        let evmAshEvm :=
          Solm.EVM.storageStore evmDaiEvm evmDaiEvm.executionEnv.codeOwner ⟨6⟩ AshNew
        have hStateAsh : EVMStateEquiv evmAshEvm evmAshSolm := by
          simpa [evmAshEvm, evmAshSolm] using
            hStateDai.storageStore_codeOwner ⟨6⟩ (show AshNew = AshNew from rfl)
        have hAccountsAsh : accountMapEquiv σAshEvm evmAshSolm.accountMap := by
          simpa [σAshEvm, evmAshEvm, evmDaiEvm, evmAshSolm, storageStore_accountMap,
            initState] using hStateAsh.accountMap
        have hTargetDaiEvm : kissDaiTargetWord σ_dai I = kissDaiTargetWord σ_evm I := by
          simp [kissDaiTargetWord, hVatDaiEvm]
        have hTargetAshEvm : kissDaiTargetWord σAshEvm I = kissDaiTargetWord σ_evm I := by
          rw [show σAshEvm = sstoreAccountMap I.codeOwner σ_dai ⟨6⟩ AshNew from rfl,
            kissDaiTargetWord_sstore_ash, hTargetDaiEvm]
        have hTargetAshEq :
            kissDaiTargetWord σAshEvm I = kissDaiTargetWord evmAshSolm.accountMap I := by
          have hslot := accountMapEquiv_storage_findD hAccountsAsh I.codeOwner ⟨1⟩ ⟨0⟩
          simp [kissDaiTargetWord, vowSlotWord, hslot]
        have hTargetAshSolmOrig :
            kissDaiTargetWord evmAshSolm.accountMap I = kissDaiTargetWord σ_solm I := by
          rw [← hTargetAshEq, hTargetAshEvm, hTargetOrig]
        have hVatAddrHeal : kissVatAddress σAshEvm I = kissVatAddress σ_solm I := by
          apply Fin.ext
          have hslotAsh : vowSlotWord ⟨1⟩ σAshEvm I = vowSlotWord ⟨1⟩ σ_solm I := by
            have hslotDai : vowSlotWord ⟨1⟩ σ_dai I = vowSlotWord ⟨1⟩ σ_solm I := by
              rw [hVatDaiEvm, hVatOrig]
            simpa [σAshEvm, vowSlotWord, solcSlotWord] using
              (sstoreAccountMap_storage_findD_ne σ_dai I.codeOwner ⟨1⟩ ⟨6⟩ AshNew
                (by decide : (⟨1⟩ : UInt256) ≠ ⟨6⟩)).trans hslotDai
          simp [kissVatAddress, vowAddressReturnWord, hslotAsh]
        by_cases hcodeSizeHeal :
            Reasoning.Theory.extCodeSizeWord σAshEvm
              (kissDaiTargetWord σAshEvm I) = ⟨0⟩
        · have hcodeSizeHealSolm :
              Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
                (kissDaiTargetWord evmAshSolm.accountMap I) = ⟨0⟩ := by
            have hsame :=
              Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsAsh
                (kissDaiTargetWord σAshEvm I)
            have hzeroAtEvmTarget :
                Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
                  (kissDaiTargetWord σAshEvm I) = ⟨0⟩ := by
              rw [← hsame]
              exact hcodeSizeHeal
            simpa [hTargetAshEq] using hzeroAtEvmTarget
          have haddrHeal :
              kissVatAddress σ_solm I =
                AccountAddress.ofUInt256 (kissDaiTargetWord evmAshSolm.accountMap I) := by
            rw [hTargetAshSolmOrig]
            exact kissVatAddress_eq_daiTarget_account σ_solm I
          have hvatNoCodeHeal :
              (UInt256.ofNat
                (((Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                    ⟨6⟩ AshNew).lookupAccount
                  (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
            simpa [evmAshSolm, State.lookupAccount] using
              extCodeSizeWord_zero_lookup_code_zero
                (σ := evmAshSolm.accountMap)
                (target := kissDaiTargetWord evmAshSolm.accountMap I)
                (addr := kissVatAddress σ_solm I) haddrHeal hcodeSizeHealSolm
          exact vowKissHealNoCodeBodyCore (cA' := cA_dai) (σAsh_evm := σAshEvm)
            (evmDai := evmDaiSolm) hcode hwv hdispatch hdecode rd1839 hmem hread64
            hcodeSizeHeal hashEnoughSolm hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough
            hAshLoadDai hvatLoadDai hAshNew hvatNoCodeHeal
        have hcodeSizeHealNE :
            Reasoning.Theory.extCodeSizeWord σAshEvm
              (kissDaiTargetWord σAshEvm I) ≠ ⟨0⟩ :=
          hcodeSizeHeal
        have hcodeSizeHealSolmNE :
            Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
              (kissDaiTargetWord evmAshSolm.accountMap I) ≠ ⟨0⟩ := by
          intro hzero
          apply hcodeSizeHealNE
          have hsame :=
            Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccountsAsh
              (kissDaiTargetWord σAshEvm I)
          have hzeroAtEvmTarget :
              Reasoning.Theory.extCodeSizeWord evmAshSolm.accountMap
                (kissDaiTargetWord σAshEvm I) = ⟨0⟩ := by
            simpa [hTargetAshEq] using hzero
          rw [hsame]
          exact hzeroAtEvmTarget
        have haddrHeal :
            kissVatAddress σ_solm I =
              AccountAddress.ofUInt256 (kissDaiTargetWord evmAshSolm.accountMap I) := by
          rw [hTargetAshSolmOrig]
          exact kissVatAddress_eq_daiTarget_account σ_solm I
        have hvatCodeHealSolm :
            0 < (UInt256.ofNat
              (((Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                  ⟨6⟩ AshNew).lookupAccount
                (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat := by
          simpa [evmAshSolm, State.lookupAccount] using
            extCodeSizeWord_ne_zero_lookup_code_pos
              (σ := evmAshSolm.accountMap)
              (target := kissDaiTargetWord evmAshSolm.accountMap I)
              (addr := kissVatAddress σ_solm I) haddrHeal hcodeSizeHealSolmNE
        obtain ⟨cA_heal, σ_heal, zHeal, outHeal, A_heal, k1919, C1919,
            rd1919, hcallHealEvmRaw, houtHealSize⟩ :=
          RD.vowKissHealPostCall rd1839 hmem hread64 hcodeSizeHealNE hdepthLt hperm
        let evmHealEvmIn :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σAshEvm
              createdAccounts := cA_dai }
        let evmHealEvmOut :=
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_heal
              substate := A_heal
              createdAccounts := cA_heal }
        have hcallHealEvm :
            typedCallViaEVM config evmHealEvmIn
              (EVM.address (kissVatAddress σ_solm I)) "heal" 0
              [.int (Int.ofNat (kissRad I).toNat)]
              (zHeal, evmHealEvmOut, outHeal) true := by
          simpa [evmHealEvmIn, evmHealEvmOut, hVatAddrHeal] using hcallHealEvmRaw
        let evmAshSolmBase := { evmAshSolm with substate := evmHealEvmIn.substate }
        have hcallCreated : evmAshSolmBase.createdAccounts = evmHealEvmIn.createdAccounts := by
          simp [evmAshSolmBase, evmHealEvmIn, evmAshSolm, evmDaiSolm, initState,
            storageStore_createdAccounts]
        have hcallEnv : evmAshSolmBase.executionEnv = evmHealEvmIn.executionEnv := by
          simp [evmAshSolmBase, evmHealEvmIn, evmAshSolm, evmDaiSolm, evmDaiEvm,
            initState, storageStore_executionEnv]
        obtain ⟨σ_heal_solm, A_heal_solm0, hcallHealSolmBase, hAccountsHeal⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evmAshSolmBase)
            hcallHealEvm hAccountsAsh
            (by
              simp [evmHealEvmIn, evmAshSolmBase, evmAshSolm, evmDaiSolm, initState,
                storageStore_σ₀])
            hcallCreated
            (by
              simp [evmHealEvmIn, evmAshSolmBase, evmAshSolm, evmDaiSolm, initState,
                storageStore_genesisBlockHeader])
            (by
              simp [evmHealEvmIn, evmAshSolmBase, evmAshSolm, evmDaiSolm, initState,
                storageStore_blocks])
            (by simp [evmAshSolmBase])
            hcallEnv
        have hdepthNeI : I.depth ≠ 1024 := by
          intro hdepthEq
          rw [hdepthEq] at hdepthLt
          norm_num at hdepthLt
        have hdepthNeBase : evmAshSolmBase.executionEnv.depth ≠ 1024 := by
          simpa [evmAshSolmBase, evmAshSolm, evmDaiSolm, initState, storageStore_executionEnv]
            using hdepthNeI
        obtain ⟨A_heal_solm, hcallHealSolmRaw⟩ :=
          typedCallViaEVM_zero_setSubstate hcallHealSolmBase hdepthNeBase evmAshSolm.substate
        let evmHealSolm :=
          { evmAshSolm with
              accountMap := σ_heal_solm
              substate := A_heal_solm
              createdAccounts := cA_heal }
        have hcallHealSolm :
            typedCallViaEVM config evmAshSolm
              (EVM.address (kissVatAddress σ_solm I)) "heal" 0
              [.int (Int.ofNat (kissRad I).toNat)]
              (zHeal, evmHealSolm, outHeal) true := by
          simpa [evmHealSolm, evmAshSolmBase] using hcallHealSolmRaw
        cases zHeal
        · exact vowKissHealCallFailureBodyCore
            (acc := (cA_heal, σ_heal)) (evmDai := evmDaiSolm) (evmHeal := evmHealSolm)
            hcode hwv hdispatch hdecode (by simpa using rd1919) houtHealSize
            hashEnoughSolm hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough
            hAshLoadDai hvatLoadDai hAshNew hvatCodeHealSolm (by simpa using hcallHealSolm)
        have hdecHeal : config.externalABI.decode? "heal" outHeal = some [] := by
          simp [config, vowExternalABI, decodeVoid?]
        have hcreated : (cA_heal, σ_heal).1 = evmHealSolm.createdAccounts := by
          rfl
        have hAccountsFinal : accountMapEquiv (cA_heal, σ_heal).2 evmHealSolm.accountMap := by
          simpa [evmHealEvmOut, evmHealSolm] using hAccountsHeal
        exact vowKissHealSuccessBodyCore
          (acc := (cA_heal, σ_heal)) (evmDai := evmDaiSolm) (evmHeal := evmHealSolm)
          hcode hwv hdispatch hdecode (by simpa using rd1919)
          hashEnoughSolm hvatCodeSolm hcallDaiSolm hdecDai hvatDaiEnough
          hAshLoadDai hvatLoadDai hAshNew hvatCodeHealSolm (by simpa using hcallHealSolm)
          hdecHeal hcreated hAccountsFinal
      · have hshortRet : oDai.size < 32 := Nat.lt_of_not_ge ho32
        exact vowKissDaiDecodeShortBodyCore (cA' := cA_dai) (σ'_evm := σ_dai)
          (A'_evm := A_dai) hcode hwv hdispatch hdecode rd1704True hcallDaiTrue
          hosz hshortRet hashEnoughEvm hvatCodeSolm hAccounts
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    obtain ⟨k1704, C1704, rd1704⟩ :=
      RD.vowKissDaiCallDepthLimit hreach hsz36 hsize hashEnoughEvm hcodeSizeDaiNE hdepthEq
    let evm0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let A_dai := (evm0.addAccessedAccount (EVM.address (kissVatAddress σ_evm I))).substate
    have hcallDaiDepth :
        typedCallViaEVM config evm0
          (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
          (false, { evm0 with accountMap := σ_evm, substate := A_dai, createdAccounts := cA },
            ByteArray.empty) false := by
      simpa [evm0, A_dai, initState] using
        (callNotMade_depthLimit (cfg := config) (evm := evm0)
          (tgt := EVM.address (kissVatAddress σ_evm I)) (name := "dai")
          (args := [.address I.codeOwner]) (callPerm := false)
          (kissDaiEncode_eq I) (by simpa [evm0, initState] using hdepthEq))
    exact vowKissDaiCallFailureBodyCore (cA' := cA) (σ'_evm := σ_evm)
      (A'_evm := A_dai) hcode hwv hdispatch hdecode rd1704 hcallDaiDepth
      (by native_decide) hashEnoughEvm hvatCodeSolm hAccounts

end Benchmarks.Dss.Vow
