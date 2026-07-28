import Benchmarks.Dss.Vow.FlapSin1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` final `flapper.kick(bump, 0)` calldata memory -/

abbrev flapKickSelectorWord : UInt256 :=
  ⟨3393242137⟩

abbrev flapKickSelectorShifted : UInt256 :=
  UInt256.shiftLeft flapKickSelectorWord ⟨224⟩

abbrev flapKickOutPtr : UInt256 := ⟨128⟩

abbrev flapKickInSize : UInt256 := ⟨68⟩

abbrev flapKickOutSize : UInt256 := ⟨32⟩

abbrev flapKickEndPtr : UInt256 := ⟨196⟩

noncomputable def flapKickSelectorMem (mem : ByteArray) : ByteArray :=
  flapKickSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def flapKickBumpMem (bump : UInt256) (mem : ByteArray) : ByteArray :=
  bump.toByteArray.write 0 (flapKickSelectorMem mem) 132 32

noncomputable def flapKickCalldataMem (bump : UInt256) (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (flapKickBumpMem bump mem) 164 32

theorem flapKickSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (flapKickSelectorMem mem).size = 164 := by
  unfold flapKickSelectorMem
  exact toByteArray_write32_size_of_le mem flapKickSelectorShifted 128 164 164 hmem
    (by rw [hmem]; omega) (by omega)

theorem flapKickBumpMem_size (bump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flapKickBumpMem bump mem).size = 164 := by
  unfold flapKickBumpMem
  exact toByteArray_write32_size_of_le (flapKickSelectorMem mem) bump 132 164 164
    (flapKickSelectorMem_size hmem)
    (by rw [flapKickSelectorMem_size hmem]; omega) (by omega)

theorem flapKickCalldataMem_size (bump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (flapKickCalldataMem bump mem).size = 196 := by
  unfold flapKickCalldataMem
  exact toByteArray_write32_size_of_le (flapKickBumpMem bump mem) (⟨0⟩ : UInt256) 164
    164 196 (flapKickBumpMem_size bump hmem)
    (by rw [flapKickBumpMem_size bump hmem]) (by omega)

theorem flapKickSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flapKickSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flapKickSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem flapKickBumpMem_read64 (bump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flapKickBumpMem bump mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold flapKickBumpMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [flapKickSelectorMem_size hmem]; omega) (by omega),
    flapKickSelectorMem_read64 hmem hread64]

theorem flapKickCalldataMem_read64 (bump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flapKickCalldataMem bump mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flapKickCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [flapKickBumpMem_size bump hmem]) (by omega),
    flapKickBumpMem_read64 bump hmem hread64]

theorem flapKickCalldataMem_read128_4 (bump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flapKickCalldataMem bump mem).readWithPadding 128 4 =
      flapKickSelector := by
  have hBumpSize := flapKickBumpMem_size bump hmem
  have hSelectorSize := flapKickSelectorMem_size hmem
  unfold flapKickCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (flapKickBumpMem bump mem) 164 128 4
      (by rw [hBumpSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hBumpSize]; native_decide)]
  unfold flapKickBumpMem
  rw [toByteArray_write_read_below_len_of_gap bump (flapKickSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold flapKickSelectorMem
  rw [toByteArray_write_read_window_of_gap flapKickSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  native_decide

theorem flapKickCalldataMem_read132_32 (bump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flapKickCalldataMem bump mem).readWithPadding 132 32 =
      bump.toByteArray := by
  have hBumpSize := flapKickBumpMem_size bump hmem
  have hSelectorSize := flapKickSelectorMem_size hmem
  unfold flapKickCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (⟨0⟩ : UInt256)
      (flapKickBumpMem bump mem) 164 132 32
      (by rw [hBumpSize])
      (by omega) (by omega) (by omega)
      (by rw [hBumpSize]; native_decide)]
  unfold flapKickBumpMem
  rw [toByteArray_write_read_back_of_gap bump (flapKickSelectorMem mem) 132
      (by rw [hSelectorSize]; native_decide)]

theorem flapKickCalldataMem_read164_32 (bump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flapKickCalldataMem bump mem).readWithPadding 164 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  have hBumpSize := flapKickBumpMem_size bump hmem
  unfold flapKickCalldataMem
  rw [toByteArray_write_read_back_of_gap (⟨0⟩ : UInt256) (flapKickBumpMem bump mem) 164
      (by rw [hBumpSize]; native_decide)]

theorem flapKickCalldataMem_read128_68 (bump : UInt256)
    {mem : ByteArray} (hmem : mem.size = 164) :
    (flapKickCalldataMem bump mem).readWithPadding 128 68 =
      flapKickSelector ++ bump.toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
  have hsize : (flapKickCalldataMem bump mem).size = 196 :=
    flapKickCalldataMem_size bump hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (flapKickCalldataMem bump mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (flapKickCalldataMem bump mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize])]
  rw [flapKickCalldataMem_read128_4 bump hmem,
    flapKickCalldataMem_read132_32 bump hmem,
    flapKickCalldataMem_read164_32 bump hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem flapKickEncode_eq (bump : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    config.externalABI.encode? "kick" [.int (Int.ofNat bump.toNat), .int 0] =
      some ((flapKickCalldataMem bump mem).readWithPadding
        flapKickOutPtr.toNat flapKickInSize.toNat) := by
  change config.externalABI.encode? "kick" [.int (Int.ofNat bump.toNat), .int 0] =
    some ((flapKickCalldataMem bump mem).readWithPadding 128 68)
  rw [flapKickCalldataMem_read128_68 bump hmem]
  have hbumpLt : bump.toNat < EVM.twoPow 256 := bump.val.isLt
  have hbumpWord : EVM.word bump.toNat = bump := by
    show UInt256.ofNat bump.toNat = bump
    exact u256_ofNat_toNat _
  have hzeroLt : (0 : ℕ) < EVM.twoPow 256 := by
    native_decide
  have hzeroWord : EVM.word 0 = (⟨0⟩ : UInt256) := rfl
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, flapKickSelector, selectorBytes, hbumpLt, hbumpWord,
    hzeroLt, hzeroWord]
  apply ByteArray.ext
  simp [word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.data_append, Array.append_assoc]

theorem flapKickAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σ I).toNat) =
      AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt
    (by
      simp [EVM.twoPow, AccountAddress.size])

set_option maxHeartbeats 1000000 in
theorem RD.vowFlapToKickExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    let target := vowAddressReturnWord ⟨2⟩ acc.2 I
    let bump := vowSlotWord ⟨10⟩ acc.2 I
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1482⟩
      (target :: target :: ⟨0⟩ :: flapKickOutPtr :: flapKickInSize ::
        flapKickOutPtr :: flapKickOutSize :: flapKickEndPtr ::
        flapKickSelectorWord :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (flapKickCalldataMem bump mem)
      (UInt256.ofNat 7) o acc k' C' := by
  intro target bump
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hKickMem : (flapKickCalldataMem bump mem).size = 196 := by
    simpa [bump] using flapKickCalldataMem_size bump hmem
  have hKickRead64 :
      (flapKickCalldataMem bump mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [bump] using flapKickCalldataMem_read64 bump hmem hread64
  have hmload64Kick :
      (if (⟨64⟩ : UInt256).toNat ≥ (flapKickCalldataMem bump mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((flapKickCalldataMem bump mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hKickMem]; decide) (by decide) hKickRead64
  have rd1404 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1406 := rd1404.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1407, C1407, rd1407Raw⟩ := rd1406.sload (by native_decide) (by evm_ov)
  have rd1407 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1407⟩
      (vowSlotWord ⟨2⟩ acc.2 I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1407 C1407 := by
    simpa [vowSlotWord, solcSlotWord] using rd1407Raw
  have rd1409 := rd1407.push1 ⟨10⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1410, C1410, rd1410Raw⟩ := rd1409.sload (by native_decide) (by evm_ov)
  have rd1410 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1410⟩
      (bump :: vowSlotWord ⟨2⟩ acc.2 I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1410 C1410 := by
    simpa [bump, vowSlotWord, solcSlotWord] using rd1410Raw
  have rd1482 := evm_run rd1410 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 flapKickSelectorWord,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 0 (flapKickSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap3,
    swap1,
    swap3,
    raw mstore 0 (flapKickBumpMem bump mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨0⟩,
    push1 ⟨36⟩,
    dup4,
    add,
    dup2,
    swap1,
    raw mstore 3 (flapKickCalldataMem bump mem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64Kick (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap4,
    and,
    swap3,
    push4 flapKickSelectorWord,
    swap3,
    push1 flapKickInSize,
    dup1,
    dup3,
    add,
    swap4,
    push1 flapKickOutSize,
    swap4,
    swap3,
    dup4,
    swap1,
    sub,
    swap1,
    swap2,
    add,
    swap1,
    dup3,
    swap1,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [target, bump, flapKickSelectorShifted, flapKickSelectorWord,
      flapKickSelectorMem, flapKickBumpMem, flapKickCalldataMem,
      flapKickOutPtr, flapKickInSize, flapKickOutSize, flapKickEndPtr,
      vowAddressReturnWord, vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd1482⟩

theorem RD.vowFlapKickNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (vowAddressReturnWord ⟨2⟩ acc.2 I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let target := vowAddressReturnWord ⟨2⟩ acc.2 I
  let bump := vowSlotWord ⟨10⟩ acc.2 I
  obtain ⟨_, _, rd1482⟩ := RD.vowFlapToKickExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1482⟩) (okPc := ⟨1494⟩)
    (by simpa [target, bump] using rd1482)
    (by simpa [target] using hcodeSize)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlapKickCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (vowAddressReturnWord ⟨2⟩ acc.2 I) ≠ ⟨0⟩) :
    let target := vowAddressReturnWord ⟨2⟩ acc.2 I
    let bump := vowSlotWord ⟨10⟩ acc.2 I
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1497⟩
      (gasWord :: target :: ⟨0⟩ :: flapKickOutPtr :: flapKickInSize ::
        flapKickOutPtr :: flapKickOutSize :: flapKickEndPtr ::
        flapKickSelectorWord :: target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (flapKickCalldataMem bump mem)
      (UInt256.ofNat 7) o acc k' C' := by
  intro target bump
  obtain ⟨_, _, rd1482⟩ := RD.vowFlapToKickExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k', C', rd1497⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1482⟩) (okPc := ⟨1494⟩)
      (by simpa [target, bump] using rd1482)
      (by simpa [target] using hcodeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k', C', by simpa [target, bump] using rd1497⟩

theorem RD.vowFlapKickPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (vowAddressReturnWord ⟨2⟩ acc.2 I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024) :
    let target := vowAddressReturnWord ⟨2⟩ acc.2 I
    let bump := vowSlotWord ⟨10⟩ acc.2 I
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: flapKickEndPtr :: flapKickSelectorWord ::
          target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (out.write 0 (flapKickCalldataMem bump mem) flapKickOutPtr.toNat
          (min flapKickOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 7) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := acc.2, createdAccounts := acc.1 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "kick" 0
        [.int (Int.ofNat bump.toNat), .int 0]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  intro target bump
  obtain ⟨gasWord, _, _, rd1497⟩ :=
    RD.vowFlapKickCall rd hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k1498, C1498, hΘpack, rd1498raw, houtsz⟩ :=
    RD.call rd1497 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1498, C1498, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          flapKickOutPtr.toNat flapKickInSize.toNat)
          flapKickOutPtr.toNat flapKickOutSize.toNat) = UInt256.ofNat 7 := by
      unfold flapKickOutPtr flapKickInSize flapKickOutSize
      native_decide
    exact haw ▸ rd1498raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := target)
      (mem := flapKickCalldataMem bump mem)
      (inOff := flapKickOutPtr) (inSize := flapKickInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (by simpa [target] using flapKickAddress_eq_target acc.2 I)
      (flapKickEncode_eq bump hmem) ?_
    simpa [initState, target, hperm] using hΘ

theorem flapKickWrite_size (bump : UInt256) {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (flapKickCalldataMem bump mem) 128 L).size = 196 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact flapKickCalldataMem_size bump hmem
  · rw [write_eq_gen o (flapKickCalldataMem bump mem) 128 L (by omega) hLo
      (by rw [flapKickCalldataMem_size bump hmem]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      flapKickCalldataMem_size bump hmem]
    omega

theorem flapKickWrite_read64 (bump : UInt256) {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (flapKickCalldataMem bump mem) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact flapKickCalldataMem_read64 bump hmem hread64
  · rw [write_read_below_gen o (flapKickCalldataMem bump mem) 128 L 64
      (by omega) hLo (by rw [flapKickCalldataMem_size bump hmem]; omega)
      (by omega),
      flapKickCalldataMem_read64 bump hmem hread64]

theorem flapKickWrite_read128_32 (bump : UInt256) {mem : ByteArray} (o : ByteArray)
    (hmem : mem.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 (flapKickCalldataMem bump mem) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (flapKickCalldataMem bump mem) 128 ho32
    (by rw [flapKickCalldataMem_size bump hmem]; omega)

theorem RD.vowFlapKickCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1498⟩) (okPc := ⟨1514⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowFlapKickCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1498⟩) (okPc := ⟨1514⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowFlapKickReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 7) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1516⟩) (okPc := ⟨1536⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlapKickReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1516⟩
      (d0 :: d1 :: d2 :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 7) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1539⟩
      (retWord :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 7) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1516⟩) (okPc := ⟨1536⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowFlapKickDecodedToPublicReturn
    {cA gh bl σ σ₀ A I} {g sel id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1539⟩
      (id :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      (id :: sel :: []) mem (UInt256.ofNat 7) o acc k' C' := by
  have rd1540 := rd.swap2 (by native_decide) (by evm_ov)
  have rd1541 := rd1540.swap1 (by native_decide) (by evm_ov)
  have rd1542 := rd1541.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1542.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowFlapKickPublicReturn
    {cA gh bl σ σ₀ A I} {g sel id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem memout o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      (id :: sel :: []) mem (UInt256.ofNat 7) o acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmemout : (UInt256.toByteArray id).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray id) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray id) := by
  exact evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 7) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray id) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.vowFlapKickSuccess
    {cA gh bl σ σ₀ A I} {g sel target bump id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
      (⟨1⟩ :: flapKickEndPtr :: flapKickSelectorWord ::
        target :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (out.write 0 (flapKickCalldataMem bump mem) flapKickOutPtr.toNat
        (min flapKickOutSize (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ out.size)
    (hosz : out.size < UInt256.size)
    (hid : id = UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray id) := by
  have hmin : (min flapKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    simpa [flapKickOutSize] using kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1498 := rd
  rw [hmin, show flapKickOutPtr.toNat = 128 from by native_decide] at rd1498
  obtain ⟨_, _, rd1516⟩ :=
    RD.vowFlapKickCallSuccessToDecode rd1498 (by simp)
  have hmemWrite : (out.write 0 (flapKickCalldataMem bump mem) 128 32).size =
      196 :=
    flapKickWrite_size bump out 32 hmem (by omega) ho32
  have hread64Write :
      (out.write 0 (flapKickCalldataMem bump mem) 128 32).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    flapKickWrite_read64 bump out 32 hmem hread64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (out.write 0 (flapKickCalldataMem bump mem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((out.write 0 (flapKickCalldataMem bump mem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (out.write 0 (flapKickCalldataMem bump mem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((out.write 0 (flapKickCalldataMem bump mem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (out.write 0 (flapKickCalldataMem bump mem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩) := by
      rw [hmemWrite]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      flapKickWrite_read128_32 bump out hmem ho32]
  obtain ⟨_, _, rd1539Raw⟩ :=
    RD.vowFlapKickReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
      rd1516 ho32 hosz hmload64 hmload128
  have rd1539 := by
    simpa [← hid] using rd1539Raw
  obtain ⟨_, _, rd357⟩ := RD.vowFlapKickDecodedToPublicReturn rd1539
  let memCall := out.write 0 (flapKickCalldataMem bump mem) 128 32
  let memRet := (UInt256.toByteArray id).write 0 memCall 128 32
  have hmemCallSize : memCall.size = 196 := by
    simpa [memCall] using hmemWrite
  have hread64Call : memCall.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memCall] using hread64Write
  have hmemRetSize : memRet.size = 196 := by
    unfold memRet
    exact toByteArray_write32_size_of_le memCall id 128 196 196 hmemCallSize
      (by rw [hmemCallSize]; omega) (by omega)
  have hread64Ret : memRet.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold memRet
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmemCallSize]; omega) (by omega), hread64Call]
  have hmload64Ret :
      (if (⟨64⟩ : UInt256).toNat ≥ memRet.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memRet.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemRetSize]; decide) (by decide) hread64Ret
  have hread128Ret : memRet.readWithPadding 128 32 = UInt256.toByteArray id := by
    unfold memRet
    exact toByteArray_write32_read_back memCall id 128 (by rw [hmemCallSize]; omega)
  exact RD.vowFlapKickPublicReturn
    (memout := memRet) rd357 hmload64 (by rfl) hmload64Ret hread128Ret

end Benchmarks.Dss.Vow
