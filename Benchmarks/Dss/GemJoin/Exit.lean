import Benchmarks.Dss.GemJoin.Join

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.GemJoin

/-! ## `exit(address,uint256)` -/

abbrev exitStore (I : ExecutionEnv) : Store :=
  joinStore I

theorem gemJoinDecode_exit_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  simpa [exitStore, joinStore, joinUsrValue, joinWadValue, joinUsrWord, joinWadWord,
    calldataWord] using
    decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem gemJoinDecode_exit_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

theorem gemJoinReachExitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 3)) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨428⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : gemJoinSelWord I = ⟨0xef693bed⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0xef 0x69 0x3b 0xed ⟨0xef693bed⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc 5))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachHighBody 5 (by omega) ⟨428⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinExitX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1544⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := gemJoinBytecode) (entry := ⟨428⟩) (ret := ⟨254⟩)
    (decoded := ⟨450⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by
      apply ult_zero
      rw [usub_ofNat_word_toNat (by omega : 4 ≤ I.calldata.size) hsize]
      change 64 ≤ I.calldata.size - 4
      omega)
  obtain ⟨_, _, hroutine⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked
    (code := gemJoinBytecode) (decoded := ⟨450⟩) (ret := ⟨254⟩) (routine := ⟨1544⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [joinWadWord, joinUsrMaskedWord, joinUsrWord, calldataWord] using hroutine⟩

theorem gemJoinExitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := gemJoinBytecode) (sel := sel) (entry := ⟨428⟩) (ret := ⟨254⟩)
    (decoded := ⟨450⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem gemJoinDecode_transferReturn_true {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩) :
    config.externalABI.decode? "transfer" out = some [.bool true] := by
  change decodeBoolReturn? out = some [.bool true]
  exact gemJoinDecode_transferFromReturn_true hlo hword

theorem gemJoinDecode_transferReturn_false {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    config.externalABI.decode? "transfer" out = some [.bool false] := by
  change decodeBoolReturn? out = some [.bool false]
  exact gemJoinDecode_transferFromReturn_false hlo hword

theorem gemJoinDecode_transferReturn_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "transfer" out = none := by
  change decodeBoolReturn? out = none
  exact gemJoinDecode_transferFromReturn_none_short hshort

set_option maxHeartbeats 1000000 in
theorem gemJoinExitX_overflowRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hwadHigh : intLimit < (joinWadWord I).toNat)
    (h : RD gemJoinBytecode I g s0 ⟨1544⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g s0 := by
  have hwadHighNat : (2 : ℕ) ^ 255 < (joinWadWord I).toNat := by
    norm_num [intLimit] at hwadHigh ⊢
    exact hwadHigh
  have hgt :
      UInt256.gt (joinWadWord I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨1⟩ := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩ =
      (⟨0x8000000000000000000000000000000000000000000000000000000000000000⟩ :
        UInt256) by native_decide]
    apply ugt_one
    simpa using hwadHighNat
  have rd1553pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hgt] at rd1553pre
  have rd1556 := rd1553pre.pushConst (⟨1620⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1557 := rd1556.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1557⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x47656d4a6f696e2f6f766572666c6f77⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x47656d4a6f696e2f6f766572666c6f7700000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd1557
    (by
      unfold solcErrorStringRevertTailWf
      repeat' apply And.intro
      all_goals native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem gemJoinExitX_nonoverflowOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (h : RD gemJoinBytecode I g s0 ⟨1544⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I g s0 ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hwadOkNat : (joinWadWord I).toNat ≤ (2 : ℕ) ^ 255 := by
    norm_num [intLimit] at hwadOk ⊢
    exact hwadOk
  have hgt :
      UInt256.gt (joinWadWord I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩ =
      (⟨0x8000000000000000000000000000000000000000000000000000000000000000⟩ :
        UInt256) by native_decide]
    apply ugt_zero
    simpa using hwadOkNat
  have rd1553pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hgt] at rd1553pre
  have rd1556 := rd1553pre.pushConst (⟨1620⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1556.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

abbrev exitSlipUsrWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev exitSlipNegWord (I : ExecutionEnv) : UInt256 :=
  UInt256.sub ⟨0⟩ (joinWadWord I)

noncomputable def exitSlipCalldataMem (I : ExecutionEnv) (σ : AccountMap)
    (mem : ByteArray) : ByteArray :=
  (exitSlipNegWord I).toByteArray.write 0
    (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 32

theorem exitSlipCalldataMem_size_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).size = 228 := by
  unfold exitSlipCalldataMem
  exact toByteArray_write32_size_of_le
    (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem)
    (exitSlipNegWord I) 196 196 228
    (joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem)
    (by
      rw [joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I)
        hmem])
    (by omega)

theorem exitSlipCalldataMem_read64_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitSlipCalldataMem I σ mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold exitSlipCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by
      rw [joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I)
        hmem])
    (by omega),
    joinSlipUsrMem_read64_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I)
      hmem hread64]

theorem exitSlipCalldataMem_read128_4_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).readWithPadding 128 4 = vatSlipSelector := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hSelectorSize := joinSlipSelectorMem_size_of_size96 hmem
  unfold exitSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (exitSlipNegWord I)
      (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 128 4
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_below_len_of_gap (exitSlipUsrWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164 128 4
      (by rw [hIlkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold joinSlipIlkMem
  rw [toByteArray_write_read_below_len_of_gap (gemJoinSlotWord ⟨2⟩ σ I)
      (joinSlipSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold joinSlipSelectorMem
  rw [toByteArray_write_read_window_of_gap joinSlipSelectorShifted mem 128 0 4
      (by omega) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  native_decide

theorem exitSlipCalldataMem_read132_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).readWithPadding 132 32 =
      (gemJoinSlotWord ⟨2⟩ σ I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hSelectorSize := joinSlipSelectorMem_size_of_size96 hmem
  unfold exitSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (exitSlipNegWord I)
      (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 132 32
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_below_len_of_gap (exitSlipUsrWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164 132 32
      (by rw [hIlkSize]) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold joinSlipIlkMem
  rw [toByteArray_write_read_back_of_gap (gemJoinSlotWord ⟨2⟩ σ I)
      (joinSlipSelectorMem mem) 132
      (by rw [hSelectorSize]; native_decide)]

theorem exitSlipCalldataMem_read164_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).readWithPadding 164 32 =
      (exitSlipUsrWord I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  unfold exitSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (exitSlipNegWord I)
      (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 164 32
      (by rw [hUsrSize]) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_back_of_gap (exitSlipUsrWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164
      (by rw [hIlkSize]; native_decide)]

theorem exitSlipCalldataMem_read196_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).readWithPadding 196 32 =
      (exitSlipNegWord I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  unfold exitSlipCalldataMem
  rw [toByteArray_write_read_back_of_gap (exitSlipNegWord I)
      (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196
      (by rw [hUsrSize]; native_decide)]

theorem exitSlipCalldataMem_read128_100_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitSlipCalldataMem I σ mem).readWithPadding 128 100 =
      vatSlipSelector ++ (gemJoinSlotWord ⟨2⟩ σ I).toByteArray ++
        (exitSlipUsrWord I).toByteArray ++ (exitSlipNegWord I).toByteArray := by
  have hsize : (exitSlipCalldataMem I σ mem).size = 228 :=
    exitSlipCalldataMem_size_of_size96 I σ hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (exitSlipCalldataMem I σ mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (exitSlipCalldataMem I σ mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (exitSlipCalldataMem I σ mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [exitSlipCalldataMem_read128_4_of_size96 I σ hmem,
    exitSlipCalldataMem_read132_32_of_size96 I σ hmem,
    exitSlipCalldataMem_read164_32_of_size96 I σ hmem,
    exitSlipCalldataMem_read196_32_of_size96 I σ hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem exit_wordOfInt_neg_wad_eq (I : ExecutionEnv)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit) :
    EVM.wordOfInt (-(Int.ofNat (joinWadWord I).toNat)) = exitSlipNegWord I := by
  have hwadOkNat : (joinWadWord I).toNat ≤ (2 : ℕ) ^ 255 := by
    norm_num [intLimit] at hwadOk ⊢
    exact hwadOk
  by_cases hzero : joinWadWord I = ⟨0⟩
  · unfold exitSlipNegWord
    rw [hzero]
    native_decide
  · have hposNat : 0 < (joinWadWord I).toNat := by
      cases hword : joinWadWord I with
      | mk val =>
          cases val using Fin.cases
          · exfalso
            apply hzero
            simp [hword]
          · simp [UInt256.toNat, hword]
    apply u256_inj
    have hneg : -(Int.ofNat (joinWadWord I).toNat) < 0 := by
      have hposInt : (0 : Int) < (joinWadWord I).toNat := by
        exact_mod_cast hposNat
      exact neg_neg_of_pos hposInt
    have habs :
        (-(Int.ofNat (joinWadWord I).toNat)).natAbs = (joinWadWord I).toNat := by
      rw [Int.natAbs_neg]
      simpa using Int.natAbs_natCast (joinWadWord I).toNat
    have hltModW : (joinWadWord I).toNat < EVM.wordModulus :=
      lt_of_le_of_lt hwadOkNat (by native_decide : (2 : ℕ) ^ 255 < EVM.wordModulus)
    have hltMod :
        (-(Int.ofNat (joinWadWord I).toNat)).natAbs < EVM.wordModulus := by
      rw [habs]
      exact hltModW
    unfold EVM.wordOfInt
    simp only [hneg, if_true, habs]
    rw [Nat.mod_eq_of_lt hltModW]
    have hne : (joinWadWord I).toNat ≠ 0 := Nat.ne_of_gt hposNat
    rw [if_neg hne]
    have hwordToNat :
        (EVM.word (EVM.wordModulus - (joinWadWord I).toNat)).toNat =
          UInt256.size - (joinWadWord I).toNat := by
      change (UInt256.ofNat (EVM.wordModulus - (joinWadWord I).toNat)).toNat =
        UInt256.size - (joinWadWord I).toNat
      rw [show EVM.wordModulus = UInt256.size by native_decide]
      rw [ulit_toNat' (UInt256.size - (joinWadWord I).toNat)
        (Nat.sub_lt (by native_decide : 0 < UInt256.size) hposNat)]
    have hsubToNat :
        (exitSlipNegWord I).toNat = UInt256.size - (joinWadWord I).toNat := by
      unfold exitSlipNegWord
      rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := joinWadWord I)
        (by simpa using hposNat)]
      simp [UInt256.toNat]
    exact hwordToNat.trans hsubToNat.symm

abbrev exitNegWadValue (I : ExecutionEnv) : Value :=
  .int (-(Int.ofNat (joinWadWord I).toNat))

set_option maxHeartbeats 1000000 in
theorem exitSlipEncode_eq (I : ExecutionEnv) (σ : AccountMap) {mem : ByteArray}
    (hmem : mem.size = 96) (hwadOk : (joinWadWord I).toNat ≤ intLimit) :
    config.externalABI.encode? "slip"
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)),
          .address I.source, exitNegWadValue I] =
      some ((exitSlipCalldataMem I σ mem).readWithPadding 128 100) := by
  rw [exitSlipCalldataMem_read128_100_of_size96 I σ hmem]
  have hwadOkNat : (joinWadWord I).toNat ≤ EVM.twoPow 255 := by
    norm_num [intLimit, EVM.twoPow] at hwadOk ⊢
    exact hwadOk
  have hnegLower :
      -(Int.ofNat (EVM.twoPow 255)) ≤ -(Int.ofNat (joinWadWord I).toNat) := by
    have hwadOkInt :
        (Int.ofNat (joinWadWord I).toNat) ≤ Int.ofNat (EVM.twoPow 255) := by
      exact Int.ofNat_le.mpr hwadOkNat
    omega
  have hnegUpper :
      -(Int.ofNat (joinWadWord I).toNat) < Int.ofNat (EVM.twoPow 255) := by
    have hpos : (0 : Int) < Int.ofNat (EVM.twoPow 255) := by norm_num [EVM.twoPow]
    have hnonpos : -(Int.ofNat (joinWadWord I).toNat) ≤ 0 :=
      neg_nonpos.mpr (Int.ofNat_nonneg _)
    exact lt_of_le_of_lt hnonpos hpos
  have hilkLen : (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (gemJoinSlotWord ⟨2⟩ σ I)
  have hnegBytes :
      UInt256.toByteArray (EVM.wordOfInt (-(Int.ofNat (joinWadWord I).toNat))) =
        (exitSlipNegWord I).toByteArray := by
    rw [exit_wordOfInt_neg_wad_eq I hwadOk]
  change UInt256.toByteArray (EVM.wordOfInt (-(↑(joinWadWord I).toNat : Int))) =
    (exitSlipNegWord I).toByteArray at hnegBytes
  have hsrcWord :
      EVM.word ↑I.source = exitSlipUsrWord I := by
    rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    bytes32, bytes32Width, addr, int256, int256Int, vatSlipSelector, selectorBytes,
    exitNegWadValue, hsrcWord, hilkLen, ABI.zeroBytes]
  rw [if_pos ⟨hwadOkNat, hnegUpper⟩]
  simp [word_toBytesBE_toByteArray_eq_toByteArray, ABI.zeroBytes]
  rw [hnegBytes]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinExitToSlipExtcodesizeGuard
    {cA σ I} {g sel : UInt256}
    {s0 : State} {k C : ℕ}
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨1701⟩
      (gemJoinAddressReturnWord ⟨1⟩ σ I :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        ⟨0⟩ :: ⟨128⟩ :: joinSlipInSize :: joinSlipOutPtr :: ⟨0⟩ ::
        joinSlipEndPtr :: joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  let target := gemJoinAddressReturnWord ⟨1⟩ σ I
  let rawTarget := gemJoinSlotWord ⟨1⟩ σ I
  let ilk := gemJoinSlotWord ⟨2⟩ σ I
  have rd1621 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1623 := rd1621.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1624, C1624, rd1624Raw⟩ := rd1623.sload (by native_decide) (by evm_ov)
  have rd1624 : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨1624⟩
      (rawTarget :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1624 C1624 := by
    simpa [rawTarget, gemJoinSlotWord, solcSlotWord] using rd1624Raw
  have rd1626 := rd1624.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1627, C1627, rd1627Raw⟩ := rd1626.sload (by native_decide) (by evm_ov)
  have rd1627 : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨1627⟩
      (ilk :: rawTarget :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1627 C1627 := by
    simpa [ilk, gemJoinSlotWord, solcSlotWord] using rd1627Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hSlipMem : (exitSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
    exitSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
  have hSlipRead64 :
      (exitSlipCalldataMem I σ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitSlipCalldataMem_read64_of_size96 I σ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Slip :
      (if (⟨64⟩ : UInt256).toNat ≥ (exitSlipCalldataMem I σ solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitSlipCalldataMem I σ solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSlipMem]; decide) (by decide) hSlipRead64
  have hSelectorShift :
      UInt256.shiftLeft (⟨1047437295⟩ : UInt256) ⟨225⟩ =
        joinSlipSelectorShifted := by
    native_decide
  have hSelectorMemEq :
      (UInt256.shiftLeft (⟨1047437295⟩ : UInt256) ⟨225⟩).toByteArray.write 0
          solcFreePtrMem 128 32 =
        joinSlipSelectorMem solcFreePtrMem := by
    rw [hSelectorShift]
    rfl
  have hUsrMemEq :
      (UInt256.ofNat I.source.val).toByteArray.write 0
          (joinSlipIlkMem ilk solcFreePtrMem)
          ((⟨128⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat 32 =
        joinSlipUsrMem (exitSlipUsrWord I) ilk solcFreePtrMem := by
    change (UInt256.ofNat I.source.val).toByteArray.write 0
        (joinSlipIlkMem ilk solcFreePtrMem) 164 32 =
      joinSlipUsrMem (exitSlipUsrWord I) ilk solcFreePtrMem
    rfl
  have hNegMemEq :
      (UInt256.sub (⟨0⟩ : UInt256) (joinWadWord I)).toByteArray.write 0
          (joinSlipUsrMem (exitSlipUsrWord I) ilk solcFreePtrMem)
          ((⟨128⟩ : UInt256) + (⟨68⟩ : UInt256)).toNat 32 =
        exitSlipCalldataMem I σ solcFreePtrMem := by
    change (exitSlipNegWord I).toByteArray.write 0
        (joinSlipUsrMem (exitSlipUsrWord I) (gemJoinSlotWord ⟨2⟩ σ I)
          solcFreePtrMem) 196 32 =
      exitSlipCalldataMem I σ solcFreePtrMem
    rfl
  have hInSizeExpr :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ =
        (⟨100⟩ : UInt256) := by
    native_decide
  have hEndPtrExpr :
      (⟨128⟩ : UInt256) + ⟨100⟩ = (⟨228⟩ : UInt256) := by
    native_decide
  have rd1631 := evm_run rd1627 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1631' : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨1631⟩
      (⟨128⟩ :: ⟨64⟩ :: ilk :: rawTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k1627 + 1 + 1 + 1) (C1627 + 3 + 3 + (0 + 3)) := by
    simpa [ilk, rawTarget] using rd1631
  have rd1701 := evm_run rd1631' with [
    push4 ⟨1047437295⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (joinSlipSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost hSelectorMemEq (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap3,
    swap1,
    swap3,
    raw mstore 3 (joinSlipIlkMem ilk solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    caller,
    push1 ⟨36⟩,
    dup4,
    add,
    raw mstore 3 (joinSlipUsrMem (exitSlipUsrWord I) ilk solcFreePtrMem)
      (UInt256.ofNat 7) (by native_decide) mem_cost hUsrMemEq (by decide) (by evm_ov),
    push1 ⟨0⟩,
    dup5,
    dup2,
    sub,
    push1 ⟨68⟩,
    dup5,
    add,
    raw mstore 3 (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost hNegMemEq (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Slip (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap4,
    and,
    swap3,
    push4 joinSlipSelectorWord,
    swap3,
    push1 ⟨100⟩,
    dup1,
    dup3,
    add,
    swap4,
    swap3,
    swap2,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  have hpc1701 :
      (⟨1631⟩ : UInt256) + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨1701⟩ := by
    native_decide
  rw [hpc1701] at rd1701
  exact ⟨_, _, by
    simpa [target, rawTarget, ilk, joinSlipSelectorShifted, joinSlipSelectorWord,
      joinSlipSelectorMem, joinSlipIlkMem, joinSlipUsrMem, exitSlipCalldataMem,
      exitSlipUsrWord, exitSlipNegWord, joinSlipInSize, joinSlipOutPtr, joinSlipEndPtr,
      gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord, solcAddrMask, hInSizeExpr,
      hEndPtrExpr,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = ⟨100⟩
        from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] using rd1701⟩

theorem RD.gemJoinExitToSlipCallReady
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1716⟩
      (gasWord :: gemJoinAddressReturnWord ⟨1⟩ σ I :: ⟨0⟩ :: ⟨128⟩ ::
        joinSlipInSize :: joinSlipOutPtr :: ⟨0⟩ :: joinSlipEndPtr ::
        joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1620⟩ := hreach
  obtain ⟨_, _, rd1701⟩ := RD.gemJoinExitToSlipExtcodesizeGuard hwadOk rd1620
  obtain ⟨gasWord, k, C, rd1716⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1701⟩) (okPc := ⟨1713⟩) rd1701
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [joinSlipOutPtr] using rd1716⟩

theorem RD.gemJoinExitSlipNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) = ⟨0⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1620⟩ := hreach
  obtain ⟨_, _, rd1701⟩ := RD.gemJoinExitToSlipExtcodesizeGuard hwadOk rd1620
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1701⟩) (okPc := ⟨1713⟩) rd1701
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.gemJoinExitSlipPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k C : ℕ),
      RD gemJoinBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: joinSlipEndPtr :: joinSlipSelectorWord ::
          gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
          ⟨254⟩ :: sel :: [])
        (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) out (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)),
          .address I.source, exitNegWadValue I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1716⟩ :=
    RD.gemJoinExitToSlipCallReady hreach hwadOk hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k1717, C1717, hΘpack, rd1717raw, houtSize⟩ :=
    RD.call rd1716 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1717, C1717, ?_, ?_, houtSize⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat joinSlipInSize.toNat)
          joinSlipOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      unfold joinSlipInSize joinSlipOutPtr
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
        exact Nat.zero_le _
      simp [min, hle]
    have rd1717 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: joinSlipEndPtr :: joinSlipSelectorWord ::
          gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
          ⟨254⟩ :: sel :: [])
        (out.write 0 (exitSlipCalldataMem I σ solcFreePtrMem) joinSlipOutPtr.toNat
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k1717 C1717 :=
      haw ▸ rd1717raw
    rw [hmin, byteArray_write_len_zero] at rd1717
    exact rd1717
  · have htgt :
        EVM.address (joinVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, joinVatAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
      rw [show EVM.twoPow 160 = AccountAddress.size by rfl, Nat.mod_mod]
    refine Reasoning.Theory.callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gemJoinAddressReturnWord ⟨1⟩ σ I)
      (mem := exitSlipCalldataMem I σ solcFreePtrMem) (inOff := ⟨128⟩)
      (inSize := joinSlipInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from by
        simpa [initState] using h]; decide))
      htgt
      (by simpa [joinSlipInSize] using
        exitSlipEncode_eq I σ solcFreePtrMem_size hwadOk)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.gemJoinExitSlipCallFailure
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1717⟩) (okPc := ⟨1733⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem RD.gemJoinExitSlipCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, _, rd1716⟩ := RD.gemJoinExitToSlipCallReady hreach hwadOk hcodeSize
  obtain ⟨k1717, C1717, rd1717raw⟩ :=
    RD.callDepthLimit rd1716 (by native_decide)
      (by simpa [initState] using hdepth) (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat joinSlipInSize.toNat)
        joinSlipOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    unfold joinSlipInSize joinSlipOutPtr
    native_decide
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    native_decide
  have rd1717 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (ByteArray.empty.write 0 (exitSlipCalldataMem I σ solcFreePtrMem)
        joinSlipOutPtr.toNat
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k1717 C1717 :=
    haw ▸ rd1717raw
  rw [hmin, byteArray_write_len_zero] at rd1717
  exact ⟨k1717, C1717, rd1717⟩

theorem RD.gemJoinExitSlipCallSuccessToTransferSetup
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (⟨1⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨_, _, rd1735⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1717⟩) (okPc := ⟨1733⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  exact ⟨_, _, RD.pop rd1735 (by native_decide) (by simp)⟩

/-! ### Runtime calldata for `gem.transfer(address,uint256)` -/

abbrev exitTransferSelectorShifted : UInt256 :=
  ⟨0xa9059cbb00000000000000000000000000000000000000000000000000000000⟩
abbrev exitTransferSelectorWord : UInt256 := ⟨0xa9059cbb⟩
abbrev exitTransferOutPtr : UInt256 := ⟨128⟩
abbrev exitTransferInSize : UInt256 := ⟨68⟩
abbrev exitTransferOutSize : UInt256 := ⟨32⟩
abbrev exitTransferEndPtr : UInt256 := ⟨196⟩

noncomputable def exitTransferSelectorMem (mem : ByteArray) : ByteArray :=
  exitTransferSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def exitTransferUsrMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (joinUsrMaskedWord I).toByteArray.write 0 (exitTransferSelectorMem mem) 132 32

noncomputable def exitTransferCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (joinWadWord I).toByteArray.write 0 (exitTransferUsrMem I mem) 164 32

theorem exitTransferSelectorMem_size {mem : ByteArray} (hmem : mem.size = 228) :
    (exitTransferSelectorMem mem).size = 228 := by
  unfold exitTransferSelectorMem
  exact toByteArray_write32_size_of_le mem exitTransferSelectorShifted 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem exitTransferUsrMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferUsrMem I mem).size = 228 := by
  unfold exitTransferUsrMem
  exact toByteArray_write32_size_of_le (exitTransferSelectorMem mem) (joinUsrMaskedWord I)
    132 228 228 (exitTransferSelectorMem_size hmem)
    (by rw [exitTransferSelectorMem_size hmem]; omega) (by omega)

theorem exitTransferCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferCalldataMem I mem).size = 228 := by
  unfold exitTransferCalldataMem
  exact toByteArray_write32_size_of_le (exitTransferUsrMem I mem) (joinWadWord I)
    164 228 228 (exitTransferUsrMem_size I hmem)
    (by rw [exitTransferUsrMem_size I hmem]; omega) (by omega)

theorem exitTransferSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitTransferSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold exitTransferSelectorMem
  rw [toByteArray_write_read_below_of_gap exitTransferSelectorShifted mem 128 64
    (by omega) (by omega) (by rw [hmem]; native_decide), hread64]

theorem exitTransferUsrMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitTransferUsrMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold exitTransferUsrMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [exitTransferSelectorMem_size hmem]; omega) (by omega),
    exitTransferSelectorMem_read64 hmem hread64]

theorem exitTransferCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitTransferCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold exitTransferCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [exitTransferUsrMem_size I hmem]; omega) (by omega),
    exitTransferUsrMem_read64 I hmem hread64]

theorem exitTransferCalldataMem_read128_4 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferCalldataMem I mem).readWithPadding 128 4 = gemTransferSelector := by
  have hUsrSize := exitTransferUsrMem_size I hmem
  have hSelectorSize := exitTransferSelectorMem_size hmem
  unfold exitTransferCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (exitTransferUsrMem I mem) 164 128 4
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold exitTransferUsrMem
  rw [toByteArray_write_read_below_len_of_gap (joinUsrMaskedWord I)
      (exitTransferSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold exitTransferSelectorMem
  rw [toByteArray_write_read_window_of_gap exitTransferSelectorShifted mem 128 0 4
      (by omega) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  native_decide

theorem exitTransferCalldataMem_read132_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferCalldataMem I mem).readWithPadding 132 32 =
      (joinUsrMaskedWord I).toByteArray := by
  have hUsrSize := exitTransferUsrMem_size I hmem
  have hSelectorSize := exitTransferSelectorMem_size hmem
  unfold exitTransferCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (exitTransferUsrMem I mem) 164 132 32
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; native_decide)]
  unfold exitTransferUsrMem
  rw [toByteArray_write_read_back_of_gap (joinUsrMaskedWord I)
      (exitTransferSelectorMem mem) 132
      (by rw [hSelectorSize]; native_decide)]

theorem exitTransferCalldataMem_read164_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferCalldataMem I mem).readWithPadding 164 32 =
      (joinWadWord I).toByteArray := by
  have hUsrSize := exitTransferUsrMem_size I hmem
  unfold exitTransferCalldataMem
  rw [toByteArray_write_read_back_of_gap (joinWadWord I) (exitTransferUsrMem I mem) 164
      (by rw [hUsrSize]; native_decide)]

theorem exitTransferCalldataMem_read128_68 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitTransferCalldataMem I mem).readWithPadding 128 68 =
      gemTransferSelector ++ (joinUsrMaskedWord I).toByteArray ++
        (joinWadWord I).toByteArray := by
  have hsize : (exitTransferCalldataMem I mem).size = 228 :=
    exitTransferCalldataMem_size I hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (exitTransferCalldataMem I mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (exitTransferCalldataMem I mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [exitTransferCalldataMem_read128_4 I hmem,
    exitTransferCalldataMem_read132_32 I hmem,
    exitTransferCalldataMem_read164_32 I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem exitTransferEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    config.externalABI.encode? "transfer" [joinUsrValue I, joinWadValue I] =
      some ((exitTransferCalldataMem I mem).readWithPadding 128 68) := by
  rw [exitTransferCalldataMem_read128_68 I hmem]
  have husrVal :
      (AccountAddress.ofNat (joinUsrWord I).toNat).val = (joinUsrMaskedWord I).toNat := by
    have h := joinAddressOfNat_toNat_masked (joinUsrWord I)
    simpa [joinUsrMaskedWord, u256_land_comm] using h
  have husrWord :
      EVM.word ↑(AccountAddress.ofNat (joinUsrWord I).toNat) = joinUsrMaskedWord I := by
    change UInt256.ofNat (AccountAddress.ofNat (joinUsrWord I).toNat).val = joinUsrMaskedWord I
    rw [husrVal]
    exact u256_ofNat_toNat _
  have hwadInt : (joinWadWord I).toNat < EVM.twoPow 256 := (joinWadWord I).val.isLt
  have hWadBytes :
      UInt256.toByteArray (EVM.word (joinWadWord I).toNat) =
        (joinWadWord I).toByteArray := by
    exact congrArg UInt256.toByteArray (u256_ofNat_toNat (joinWadWord I))
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, gemTransferSelector, selectorBytes,
    joinUsrValue, joinWadValue, husrWord, hwadInt,
    word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  rw [show UInt256.toByteArray (EVM.word (joinWadWord I).toNat) =
      (joinWadWord I).toByteArray from hWadBytes]
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinExitToTransferExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1811⟩
      (gemJoinAddressReturnWord ⟨3⟩ σcur I :: gemJoinAddressReturnWord ⟨3⟩ σcur I ::
        ⟨0⟩ :: ⟨128⟩ :: exitTransferInSize :: exitTransferOutPtr ::
        exitTransferOutSize :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) outSlip (cAcur, σcur) k' C' := by
  let target := gemJoinAddressReturnWord ⟨3⟩ σcur I
  let rawTarget := gemJoinSlotWord ⟨3⟩ σcur I
  have rd1738 := rd.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1739, C1739, rd1739raw⟩ := rd1738.sload (by native_decide) (by evm_ov)
  have rd1739 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1739⟩
      (rawTarget :: joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k1739 C1739 := by
    simpa [rawTarget, gemJoinSlotWord, solcSlotWord] using rd1739raw
  have hSlipMem : (exitSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
    exitSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
  have hSlipRead64 :
      (exitSlipCalldataMem I σ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitSlipCalldataMem_read64_of_size96 I σ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Slip :
      (if (⟨64⟩ : UInt256).toNat ≥ (exitSlipCalldataMem I σ solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitSlipCalldataMem I σ solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSlipMem]; decide) (by decide) hSlipRead64
  have hTransferMem :
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem)).size = 228 :=
    exitTransferCalldataMem_size I hSlipMem
  have hTransferRead64 :
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitTransferCalldataMem_read64 I hSlipMem hSlipRead64
  have hmload64Transfer :
      (if (⟨64⟩ : UInt256).toNat ≥
            (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hTransferMem]; decide) (by decide) hTransferRead64
  have hSelectorShift :
      UInt256.shiftLeft (⟨2835717307⟩ : UInt256) ⟨224⟩ =
        exitTransferSelectorShifted := by
    native_decide
  have hSelectorMemEq :
      (UInt256.shiftLeft (⟨2835717307⟩ : UInt256) ⟨224⟩).toByteArray.write 0
          (exitSlipCalldataMem I σ solcFreePtrMem) 128 32 =
        exitTransferSelectorMem (exitSlipCalldataMem I σ solcFreePtrMem) := by
    rw [hSelectorShift]
    rfl
  have hUsrMaskedCanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
    simpa [joinUsrMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (joinUsrWord I)
  have hSolcMaskLiteral :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have hUsrMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (joinUsrMaskedWord I) =
        joinUsrMaskedWord I := by
    rw [hSolcMaskLiteral]
    exact solcAddrMask_clean_left hUsrMaskedCanon
  have hUsrMemEq :
      (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (joinUsrMaskedWord I)).toByteArray.write 0
          (exitTransferSelectorMem (exitSlipCalldataMem I σ solcFreePtrMem))
          ((⟨128⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat 32 =
        exitTransferUsrMem I (exitSlipCalldataMem I σ solcFreePtrMem) := by
    rw [hUsrMask]
    change (joinUsrMaskedWord I).toByteArray.write 0
        (exitTransferSelectorMem (exitSlipCalldataMem I σ solcFreePtrMem)) 132 32 =
      exitTransferUsrMem I (exitSlipCalldataMem I σ solcFreePtrMem)
    rfl
  have hWadMemEq :
      (joinWadWord I).toByteArray.write 0
          (exitTransferUsrMem I (exitSlipCalldataMem I σ solcFreePtrMem))
          ((⟨128⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat 32 =
        exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem) := by
    change (joinWadWord I).toByteArray.write 0
        (exitTransferUsrMem I (exitSlipCalldataMem I σ solcFreePtrMem)) 164 32 =
      exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem)
    rfl
  have rd1811 := evm_run rd1739 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Slip (by decide) (by evm_ov),
    push4 ⟨2835717307⟩,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 0 (exitTransferSelectorMem (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost hSelectorMemEq (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    dup8,
    dup2,
    and,
    push1 ⟨4⟩,
    dup4,
    add,
    raw mstore 0 (exitTransferUsrMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost hUsrMemEq (by decide) (by evm_ov),
    push1 ⟨36⟩,
    dup3,
    add,
    dup8,
    swap1,
    raw mstore 0
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost hWadMemEq (by decide) (by evm_ov),
    swap2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Transfer (by decide) (by evm_ov),
    swap2,
    swap1,
    swap3,
    and,
    swap4,
    pop,
    push4 exitTransferSelectorWord,
    swap3,
    pop,
    push1 ⟨68⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  have hpc1811 :
      (⟨1739⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨1811⟩ := by
    native_decide
  exact ⟨_, _, by
    simpa [target, rawTarget, exitTransferSelectorShifted, exitTransferSelectorWord,
      exitTransferSelectorMem, exitTransferUsrMem, exitTransferCalldataMem,
      exitTransferInSize, exitTransferOutPtr, exitTransferOutSize, exitTransferEndPtr,
      gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord, hSolcMaskLiteral, hUsrMask,
      u256_land_comm, UInt256.add, UInt256.sub,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨68⟩ = ⟨68⟩
        from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide]
      using rd1811⟩

theorem RD.gemJoinExitToTransferCallReady
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1826⟩
      (gasWord :: gemJoinAddressReturnWord ⟨3⟩ σcur I :: ⟨0⟩ :: ⟨128⟩ ::
        exitTransferInSize :: exitTransferOutPtr :: exitTransferOutSize ::
        exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) outSlip (cAcur, σcur) k' C' := by
  obtain ⟨_, _, rd1811⟩ := RD.gemJoinExitToTransferExtcodesizeGuard rd
  obtain ⟨gasWord, k, C, rd1826⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1811⟩) (okPc := ⟨1823⟩) rd1811
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [exitTransferOutPtr] using rd1826⟩

theorem RD.gemJoinExitTransferNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) = ⟨0⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1811⟩ := RD.gemJoinExitToTransferExtcodesizeGuard rd
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1811⟩) (okPc := ⟨1823⟩) rd1811
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.gemJoinExitTransferPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {Acur : Substate}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outTransfer : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: exitTransferEndPtr ::
          exitTransferSelectorWord :: gemJoinAddressReturnWord ⟨3⟩ σcur I ::
          joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
        (outTransfer.write 0
          (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
          exitTransferOutPtr.toNat
          (min exitTransferOutSize (UInt256.ofNat outTransfer.size)).toNat)
        (UInt256.ofNat 8) outTransfer (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σcur, substate := Acur, createdAccounts := cAcur }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σcur, substate := Acur, createdAccounts := cAcur })) "transfer" 0
        [joinUsrValue I, joinWadValue I]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' },
          outTransfer) true
    ∧ outTransfer.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1826⟩ := RD.gemJoinExitToTransferCallReady rd hcodeSize
  obtain ⟨cA', σ', z, outTransfer, A_in, callGas, k1827, C1827, hΘpack, rd1827raw,
      houtSize⟩ :=
    RD.call rd1826 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, outTransfer, A', k1827, C1827, ?_, ?_, houtSize⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat exitTransferInSize.toNat)
          exitTransferOutPtr.toNat exitTransferOutSize.toNat) =
          UInt256.ofNat 8 := by
      unfold exitTransferInSize exitTransferOutPtr exitTransferOutSize
      native_decide
    exact haw ▸ rd1827raw
  · have htgt :
        EVM.address (joinGemAddressOf
            { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σcur, substate := Acur, createdAccounts := cAcur }) =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σcur I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
      rw [show EVM.twoPow 160 = AccountAddress.size by rfl, Nat.mod_mod]
    refine Reasoning.Theory.callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gemJoinAddressReturnWord ⟨3⟩ σcur I)
      (mem := exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := exitTransferInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from by
        simpa [initState] using h]; decide))
      htgt
      (by
        have hSlipMem :
            (exitSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
          exitSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
        simpa [exitTransferInSize] using
          exitTransferEncode_eq I hSlipMem)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.gemJoinExitTransferCallFailure
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      (⟨0⟩ :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k C)
    (houtSize : outTransfer.size < UInt256.size) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1827⟩) (okPc := ⟨1843⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem RD.gemJoinExitTransferCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      (⟨0⟩ :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) ByteArray.empty (cAcur, σcur) k' C' := by
  obtain ⟨_, _, _, rd1826⟩ := RD.gemJoinExitToTransferCallReady rd hcodeSize
  obtain ⟨k1827, C1827, rd1827raw⟩ :=
    RD.callDepthLimit rd1826 (by native_decide)
      (by simpa [initState] using hdepth) (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat exitTransferInSize.toNat)
        exitTransferOutPtr.toNat exitTransferOutSize.toNat) = UInt256.ofNat 8 := by
    unfold exitTransferInSize exitTransferOutPtr exitTransferOutSize
    native_decide
  have hmin :
      (min exitTransferOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    native_decide
  have rd1827 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      (⟨0⟩ :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (ByteArray.empty.write 0
        (exitTransferCalldataMem I (exitSlipCalldataMem I σ solcFreePtrMem))
        exitTransferOutPtr.toNat
        (min exitTransferOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cAcur, σcur) k1827 C1827 :=
    haw ▸ rd1827raw
  rw [hmin, byteArray_write_len_zero] at rd1827
  exact ⟨k1827, C1827, rd1827⟩

theorem RD.gemJoinExitTransferCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      (⟨1⟩ :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1845⟩
      (exitTransferEndPtr :: exitTransferSelectorWord :: gemTarget ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1827⟩) (okPc := ⟨1843⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem RD.gemJoinExitTransferReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1845⟩
      (exitTransferEndPtr :: exitTransferSelectorWord :: gemTarget ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hshort : outTransfer.size < 32)
    (hhi : outTransfer.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1845⟩) (okPc := ⟨1865⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.gemJoinExitTransferReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g sel gemTarget retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1845⟩
      (exitTransferEndPtr :: exitTransferSelectorWord :: gemTarget ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hlo : 32 ≤ outTransfer.size)
    (hhi : outTransfer.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1868⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1845⟩) (okPc := ⟨1865⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinExitTransferReturnFalseReverts
    {cA gh bl σ σ₀ A I} {g sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1868⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hret : retWord = ⟨0⟩)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd1871 := rd.pushConst (⟨1942⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1872 := rd1871.jumpiNT (by native_decide) hret (by evm_ov)
  have rdMload := evm_run rd1872 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨23⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨23⟩ mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨0x23b2b6a537b4b717b330b4b632b216ba3930b739b332b9⟩ : UInt256)
    (width := 23) (op := .PUSH23) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨73⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨0x23b2b6a537b4b717b330b4b632b216ba3930b739b332b9⟩ : UInt256) ⟨73⟩ =
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩ by native_decide] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0
      (solcErrorStringMem3 ⟨23⟩
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩ mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size228 ⟨23⟩
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩
        hmem hread64)
      (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinExitTransferReturnTrueToStop
    {cA gh bl σ σ₀ A I} {g sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1868⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hret : retWord ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd1871 := rd.pushConst (⟨1942⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1942 := rd1871.jumpiT (by native_decide) hret (by jump_dest) (by evm_ov)
  have rd1947pre := evm_run rd1942 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1950 := rd1947pre.mstore 0 ((joinWadWord I).toByteArray.write 0 mem 128 32)
    (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have hmemWrite : ((joinWadWord I).toByteArray.write 0 mem 128 32).size = 228 := by
    exact toByteArray_write32_size_of_le mem (joinWadWord I) 128 228 228 hmem
      (by rw [hmem]; omega) (by omega)
  have hread64Write :
      ((joinWadWord I).toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega), hread64]
  have hmload64Write :
      (if (⟨64⟩ : UInt256).toNat ≥ ((joinWadWord I).toByteArray.write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (((joinWadWord I).toByteArray.write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have rd1962pre := evm_run rd1950 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Write (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (joinUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = joinUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    have hcanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
      simpa [joinUsrMaskedWord, u256_land_comm] using
        solcAddrMask_result_canonical (joinUsrWord I)
    exact solcAddrMask_clean hcanon
  rw [hmask] at rd1962pre
  have rd1963pre := evm_run rd1962pre with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1996 := rd1963pre.pushConst
    (⟨0x22d324652c93739755cf4581508b60875ebdd78c20c0cff5cf8e23452b299631⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd2005pre := evm_run rd1996 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2006 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0x22d324652c93739755cf4581508b60875ebdd78c20c0cff5cf8e23452b299631⟩)
    (d := joinUsrMaskedWord I)
    (t := [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd2005pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2009pre := evm_run rd2006 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd255 := rd2009pre.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd255 (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

abbrev exitLocalsAfterSlip (I : ExecutionEnv) : Store :=
  (exitStore I).insert "slipRet" .unit

abbrev exitLocalsAfterTransferOk (I : ExecutionEnv) : Store :=
  (exitLocalsAfterSlip I).insert "transferOk" (.bool true)

abbrev exitLocalsAfterTransferFalse (I : ExecutionEnv) : Store :=
  (exitLocalsAfterSlip I).insert "transferOk" (.bool false)

theorem evalExpr_exit_wad_le_true (evm : EVM.State) (I : ExecutionEnv)
    (hwad : (joinWadWord I).toNat ≤ intLimit) :
    evalExpr? config { contract := contract, locals := exitStore I } evm
      (.binary .le (.var "wad") (.intLit intLimit)) = .ok (.bool true) := by
  have hget : (exitStore I).get? "wad" = some (joinWadValue I) := by
    unfold exitStore joinStore
    simp
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  simp [EvalResult.ofOption, joinWadValue, evalBinaryOp?]
  exact hwad

theorem evalExpr_exit_wad_le_false (evm : EVM.State) (I : ExecutionEnv)
    (hwad : intLimit < (joinWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := exitStore I } evm
      (.binary .le (.var "wad") (.intLit intLimit)) = .ok (.bool false) := by
  have hget : (exitStore I).get? "wad" = some (joinWadValue I) := by
    unfold exitStore joinStore
    simp
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  simp [EvalResult.ofOption, joinWadValue, evalBinaryOp?]
  exact hwad

theorem evalExpr_exit_neg_asInt256_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitStore I } evm
      (.unary .neg (asInt256 (.var "wad"))) = .ok (exitNegWadValue I) := by
  unfold asInt256 exitNegWadValue
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [show (exitStore I).get? "wad" = some (joinWadValue I) by
    unfold exitStore joinStore
    simp]
  simp [joinWadValue, int256St, int256Int, castValue?, EvalResult.ofOption,
    evalUnaryOp?]

theorem evalExprs_exit_slipArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := exitStore I } evm
      [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
        .ok
          [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
            .address evm.executionEnv.source, exitNegWadValue I] := by
  simp [evalExprs?, evalExpr_join_ilk evm I, sender, evalExpr?, envValue,
    evalExpr_exit_neg_asInt256_wad evm I, EvalResult.bind, bind, pure, exitStore]

theorem evalExpr_exit_gem_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evm
      (.storage gemRef) = .ok (.address (joinGemAddressOf evm)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := exitLocalsAfterSlip I })
    (slot := gemRef)
    (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨3⟩)
    (hbase := by simp [exitLocalsAfterSlip, exitStore, joinStore, gemRef])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, exitLocalsAfterSlip, exitStore, joinStore,
        gemRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by exact gemJoinStorageLocLoad_address_offset0 evm ⟨3⟩)]

theorem evalExpr_exit_wad_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evm (.var "wad") =
      .ok (joinWadValue I) := by
  simp only [evalExpr?]
  rw [show (exitLocalsAfterSlip I).get? "wad" = some (joinWadValue I) by
    rw [exitLocalsAfterSlip, store_get_ne (L := exitStore I) (k := "slipRet") (a := "wad")
      .unit (by native_decide)]
    unfold exitStore joinStore
    simp]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_exit_usr_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evm (.var "usr") =
      .ok (joinUsrValue I) := by
  simp only [evalExpr?]
  rw [show (exitLocalsAfterSlip I).get? "usr" = some (joinUsrValue I) by
    rw [exitLocalsAfterSlip, store_get_ne (L := exitStore I) (k := "slipRet") (a := "usr")
      .unit (by native_decide)]
    unfold exitStore joinStore
    simp [Std.HashMap.getElem_insert]]
  unfold EvalResult.ofOption
  rfl

theorem evalExprs_exit_transferArgs_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := exitLocalsAfterSlip I } evm
      [.var "usr", .var "wad"] = .ok [joinUsrValue I, joinWadValue I] := by
  simp [evalExprs?, evalExpr_exit_usr_afterSlip evm I, evalExpr_exit_wad_afterSlip evm I,
    EvalResult.bind, bind, pure, exitLocalsAfterSlip, exitStore]

theorem evalExpr_exit_transferOk_true (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitLocalsAfterTransferOk I } evm
      (.var "transferOk") = .ok (.bool true) := by
  simp only [evalExpr?]
  rw [show (exitLocalsAfterTransferOk I).get? "transferOk" = some (.bool true) by
    unfold exitLocalsAfterTransferOk
    rw [store_get_self]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_exit_transferOk_false (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := exitLocalsAfterTransferFalse I } evm
      (.var "transferOk") = .ok (.bool false) := by
  simp only [evalExpr?]
  rw [show (exitLocalsAfterTransferFalse I).get? "transferOk" = some (.bool false) by
    unfold exitLocalsAfterTransferFalse
    rw [store_get_self]]
  unfold EvalResult.ofOption
  rfl

theorem gemJoinExitBodySuccess (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transfer" outTransfer = some [.bool true]) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body
      (.returned { contract := contract, locals := exitLocalsAfterTransferOk I }
        evmTransfer none) := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        (.ok { contract := contract, locals := exitLocalsAfterSlip I } evmSlip) := by
    simpa [exitLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_exit_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [exitLocalsAfterSlip, exitStore, joinLocalsAfterSlip] using
      evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        [.var "usr", .var "wad"] = .ok [joinUsrValue I, joinWadValue I] :=
    evalExprs_exit_transferArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transfer" (.intLit 0)
          [.var "usr", .var "wad"] "transferOk")
        (.ok { contract := contract, locals := exitLocalsAfterTransferOk I } evmTransfer) := by
    simpa [exitLocalsAfterTransferOk, collapseReturns] using
      ExecStmt.externalCallSuccess hgem (by simp [evalExpr?, pure]) htransferArgs
        hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockOK ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  refine ExecBlock.consNormal htransferStmt ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_exit_transferOk_true evmTransfer I))
    ExecBlock.nil

theorem gemJoinExitBodyRevertsOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadHigh : intLimit < (joinWadWord I).toNat) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_exit_wad_le_false evm I hwadHigh))

theorem gemJoinExitBodyRevertsVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_false evm I hvatNoCode
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hvatGuard)

theorem gemJoinExitBodyRevertsSlipCallFailure
    (evm evmSlip : EVM.State) (I : ExecutionEnv) {outSlip : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (false, evmSlip, outSlip) true) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  exact ExecBlock.consRevert hslipStmt

theorem gemJoinExitBodyRevertsGemNoCode
    (evm evmSlip : EVM.State) (I : ExecutionEnv) {outSlip : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemNoCode :
      (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        (.ok { contract := contract, locals := exitLocalsAfterSlip I } evmSlip) := by
    simpa [exitLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgemGuard :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool false) := by
    simpa [exitLocalsAfterSlip, exitStore, joinLocalsAfterSlip] using
      evalExpr_join_gemCodeGuard_afterSlip_false evmSlip I hgemNoCode
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hgemGuard)

theorem gemJoinExitBodyRevertsTransferCallFailure
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (false, evmTransfer, outTransfer) true) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        (.ok { contract := contract, locals := exitLocalsAfterSlip I } evmSlip) := by
    simpa [exitLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_exit_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [exitLocalsAfterSlip, exitStore, joinLocalsAfterSlip] using
      evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        [.var "usr", .var "wad"] = .ok [joinUsrValue I, joinWadValue I] :=
    evalExprs_exit_transferArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transfer" (.intLit 0)
          [.var "usr", .var "wad"] "transferOk")
        .reverted := by
    exact ExecStmt.externalCallFailure hgem (by simp [evalExpr?, pure]) htransferArgs
      hcallTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert htransferStmt

theorem gemJoinExitBodyRevertsTransferDecode
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transfer" outTransfer = none) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        (.ok { contract := contract, locals := exitLocalsAfterSlip I } evmSlip) := by
    simpa [exitLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_exit_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [exitLocalsAfterSlip, exitStore, joinLocalsAfterSlip] using
      evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        [.var "usr", .var "wad"] = .ok [joinUsrValue I, joinWadValue I] :=
    evalExprs_exit_transferArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transfer" (.intLit 0)
          [.var "usr", .var "wad"] "transferOk")
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hgem (by simp [evalExpr?, pure])
      htransferArgs hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert htransferStmt

theorem gemJoinExitBodyRevertsTransferFalse
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          .address evm.executionEnv.source, exitNegWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transfer" outTransfer = some [.bool false]) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [exitStore, joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := exitStore I } evm
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              .address evm.executionEnv.source, exitNegWadValue I] :=
    evalExprs_exit_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet")
        (.ok { contract := contract, locals := exitLocalsAfterSlip I } evmSlip) := by
    simpa [exitLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_exit_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [exitLocalsAfterSlip, exitStore, joinLocalsAfterSlip] using
      evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        [.var "usr", .var "wad"] = .ok [joinUsrValue I, joinWadValue I] :=
    evalExprs_exit_transferArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := exitLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transfer" (.intLit 0)
          [.var "usr", .var "wad"] "transferOk")
        (.ok { contract := contract, locals := exitLocalsAfterTransferFalse I } evmTransfer) := by
    simpa [exitLocalsAfterTransferFalse, collapseReturns] using
      ExecStmt.externalCallSuccess hgem (by simp [evalExpr?, pure]) htransferArgs
        hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_exit_wad_le_true evm I hwadOk)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  refine ExecBlock.consNormal htransferStmt ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_exit_transferOk_false evmTransfer I))

theorem gemJoinExitBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (gemJoinExitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (gemJoinDecode_exit_none_short hsz4 hshort)

theorem gemJoinExitBodyCoreOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadHigh : intLimit < (joinWadWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd1544⟩ :=
    gemJoinExitX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  have hrev := gemJoinExitX_overflowRevert (g := Sat256.ofUInt256 g) hwadHigh rd1544
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    simpa [evmSolm, initState] using
      gemJoinExitBodyRevertsOverflow evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hwadHigh
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreVatNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatNoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd1544⟩ :=
    gemJoinExitX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, rd1620⟩ := gemJoinExitX_nonoverflowOk (g := Sat256.ofUInt256 g)
    hwadOk rd1544
  have hrev := RD.gemJoinExitSlipNoCode
    (g := g) ⟨_, _, rd1620⟩ hwadOk hvatNoCode
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hsolmAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      rw [← hsame]
      exact hvatNoCode
    simpa [hVatSlot] using hsolmAtEvmTarget
  have hvatAddr :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatNoCodeSolm :
      (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hvatAddr]
    unfold Reasoning.Theory.extCodeSizeWord at hnoCodeSolm
    cases hacc :
      σ_solm.find? (AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I)) with
    | none =>
        simpa [evmSolm, initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
    | some acc =>
        have hword := congrArg UInt256.toNat hnoCodeSolm
        simpa [evmSolm, initState, State.lookupAccount, hacc] using hword
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsVatNoCode evmSolm I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatNoCodeSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreSlipCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨428⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd1544⟩ :=
    gemJoinExitX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, rd1620⟩ := gemJoinExitX_nonoverflowOk (g := Sat256.ofUInt256 g)
    hwadOk rd1544
  obtain ⟨_, _, rd1717⟩ := RD.gemJoinExitSlipCallDepthLimit
    (g := g) ⟨_, _, rd1620⟩ hwadOk hvatCode hdepth
  have hrev := RD.gemJoinExitSlipCallFailure rd1717
    (by native_decide : ByteArray.empty.size < UInt256.size)
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  let evmSlip :=
    { evmSolm with
      substate := (evmSolm.addAccessedAccount (EVM.address (joinVatAddressOf evmSolm))).substate }
  have hcallSlipDepth :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (false, evmSlip, ByteArray.empty) true := by
    simpa [evmSlip, evmSolm, initState] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (joinVatAddressOf evmSolm)) (name := "slip")
        (args :=
          [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
            .address evmSolm.executionEnv.source, exitNegWadValue I])
        (callPerm := true)
        (by
          simpa [evmSolm, initState, joinSlipInSize] using
            exitSlipEncode_eq I σ_solm solcFreePtrMem_size hwadOk)
        (by simpa [evmSolm, initState] using hdepth))
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsSlipCallFailure evmSolm evmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipDepth
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreSlipCallFailure
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip : Batteries.RBSet AccountAddress compare} {σ_slip : AccountMap}
    {outSlip : ByteArray} {A_slip : Substate} {k1717 C1717 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1717 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ_evm I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ_evm solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cA_slip, σ_slip) k1717 C1717)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (false, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (houtSlipSize : outSlip.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev := RD.gemJoinExitSlipCallFailure rd1717 houtSlipSize
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (false, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, _hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, evmSolm, initState]) hAccounts
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  let evmSolmSlip := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (false, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (false, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    have hcallSlipSolmStorage := hcallSlipSolmEvmIlk
    rw [← hIlkArg] at hcallSlipSolmStorage
    simpa [evmSolm, initState] using hcallSlipSolmStorage
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsSlipCallFailure evmSolm evmSolmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreGemNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip : Batteries.RBSet AccountAddress compare} {σ_slip : AccountMap}
    {outSlip : ByteArray} {A_slip : Substate} {k1736 C1736 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemNoCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1736 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1736⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ_evm I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (exitSlipCalldataMem I σ_evm solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cA_slip, σ_slip) k1736 C1736)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  have hrev := RD.gemJoinExitTransferNoCode rd1736 hgemNoCode
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    have hcallSlipSolmStorage := hcallSlipSolmEvmIlk
    rw [← hIlkArg] at hcallSlipSolmStorage
    simpa [evmSolm, initState] using hcallSlipSolmStorage
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemNoCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      rw [← hsame]
      exact hgemNoCode
    simpa [hGemSlot] using hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemNoCodeSolm :
      (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hgemAddrSolm]
    unfold Reasoning.Theory.extCodeSizeWord at hgemNoCodeSolmWord
    cases hacc :
      σ_slip_solm.find? (AccountAddress.ofUInt256
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)) with
    | none =>
        simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
    | some acc =>
        have hword := congrArg UInt256.toNat hgemNoCodeSolmWord
        simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount, hacc] using hword
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsGemNoCode evmSolm evmSolmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm hgemNoCodeSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreTransferCallFailure
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer : ByteArray} {A_slip A_transfer : Substate} {k1827 C1827 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1827 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1827⟩
      (⟨0⟩ :: exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σ_slip I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (outTransfer.write 0
        (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
        exitTransferOutPtr.toNat
        (min exitTransferOutSize (UInt256.ofNat outTransfer.size)).toNat)
      (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k1827 C1827)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hrev := RD.gemJoinExitTransferCallFailure rd1827 houtTransferSize
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    have hcallSlipSolmStorage := hcallSlipSolmEvmIlk
    rw [← hIlkArg] at hcallSlipSolmStorage
    simpa [evmSolm, initState] using hcallSlipSolmStorage
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (false, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, _hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (false, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsTransferCallFailure evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreTransferDecodeShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer : ByteArray} {A_slip A_transfer : Substate} {k1845 C1845 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hshort : outTransfer.size < 32)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1845 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1845⟩
      (exitTransferEndPtr :: exitTransferSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σ_slip I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (outTransfer.write 0
        (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
        exitTransferOutPtr.toNat
        (min exitTransferOutSize (UInt256.ofNat outTransfer.size)).toNat)
      (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k1845 C1845)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hSlipMem :
      (exitSlipCalldataMem I σ_evm solcFreePtrMem).size = 228 :=
    exitSlipCalldataMem_size_of_size96 I σ_evm solcFreePtrMem_size
  have hSlipRead64 :
      (exitSlipCalldataMem I σ_evm solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitSlipCalldataMem_read64_of_size96 I σ_evm solcFreePtrMem_size solcFreePtrMem_read64
  have hBaseMem :
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem)).size = 228 :=
    exitTransferCalldataMem_size I hSlipMem
  have hBaseRead64 :
      (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitTransferCalldataMem_read64 I hSlipMem hSlipRead64
  have hmin :
      (min exitTransferOutSize (UInt256.ofNat outTransfer.size)).toNat =
        outTransfer.size := by
    simpa [exitTransferOutSize] using joinTransferFromMin32_toNat_of_lt hshort
  have hmem :
      (outTransfer.write 0
        (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
        exitTransferOutPtr.toNat outTransfer.size).size = 228 := by
    simpa [exitTransferOutPtr] using
      joinTransferFromReturnWrite_size outTransfer.size hBaseMem (by omega) (by omega)
  have hread64 :
      (outTransfer.write 0
        (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
        exitTransferOutPtr.toNat outTransfer.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [exitTransferOutPtr] using
      joinTransferFromReturnWrite_read64 outTransfer.size hBaseMem hBaseRead64
        (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outTransfer.write 0
              (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
              exitTransferOutPtr.toNat outTransfer.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outTransfer.write 0
            (exitTransferCalldataMem I (exitSlipCalldataMem I σ_evm solcFreePtrMem))
            exitTransferOutPtr.toNat outTransfer.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hrev := RD.gemJoinExitTransferReturnDecodeShortReverts
    (by simpa [hmin] using rd1845) hshort houtTransferSize hmload64
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    have hcallSlipSolmStorage := hcallSlipSolmEvmIlk
    rw [← hIlkArg] at hcallSlipSolmStorage
    simpa [evmSolm, initState] using hcallSlipSolmStorage
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, _hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transfer" outTransfer = none :=
    gemJoinDecode_transferReturn_none_short hshort
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsTransferDecode evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinExitBodyCoreTransferReturnTrueSmall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer mem : ByteArray} {A_slip A_transfer : Substate} {k1868 C1868 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hret : retWord ≠ ⟨0⟩)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32)) ≠ ⟨0⟩)
    (hlo : 32 ≤ outTransfer.size)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1868 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1868⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k1868 C1868)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hretFinal := RD.gemJoinExitTransferReturnTrueToStop rd1868 hret hperm hmem hread64
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transfer" 0
        [joinUsrValue I, joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transfer" outTransfer = some [.bool true] :=
    gemJoinDecode_transferReturn_true hlo hword
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body
        (.returned { contract := contract, locals := exitLocalsAfterTransferOk I }
          evmSolmTransfer none) := by
    exact gemJoinExitBodySuccess evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  have hStateTransfer : EVMStateEquiv evmEvmTransfer evmSolmTransfer := by
    refine ⟨?_, ?_, ?_⟩
    · simp [evmEvmTransfer, evmSolmTransfer, evmSolmSlip, evmEvm, evmSolm, initState]
    · simp [evmEvmTransfer, evmSolmTransfer]
    · simpa [evmEvmTransfer, evmSolmTransfer] using hAccountsTransfer
  have henc : returnEquiv ByteArray.empty none exitTransition.returnType := by
    rw [show exitTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hretFinal.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
    rfl (accountMapEquiv.refl σ_transfer) hStateTransfer henc


theorem gemJoinExitBodyCoreTransferReturnFalseSmall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer mem : ByteArray} {A_slip A_transfer : Substate} {k1868 C1868 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hwadOk : (joinWadWord I).toNat ≤ intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hret : retWord = ⟨0⟩)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32)) = ⟨0⟩)
    (hlo : 32 ≤ outTransfer.size)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (rd1868 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1868⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k1868 C1868)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hrev := RD.gemJoinExitTransferReturnFalseReverts rd1868 hret hmem hread64
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          .address I.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          .address evmSolm.executionEnv.source, exitNegWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transfer" 0 [joinUsrValue I, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transfer" 0
        [joinUsrValue I, joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transfer" outTransfer = some [.bool false] :=
    gemJoinDecode_transferReturn_false hlo hword
  have hbody :
      ExecTransitionBody config contract evmSolm (exitStore I) exitTransition.body .reverted := by
    exact gemJoinExitBodyRevertsTransferFalse evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hwadOk hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody


theorem gemJoinExitBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some exitTransition :=
    gemJoinDispatchExit hsel
  have hreach := gemJoinReachExitBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hwadHigh : intLimit < (joinWadWord I).toNat
    · exact gemJoinExitBodyCoreOverflow hcode hsize hwv hsz68 hwadHigh hdispatch
        (gemJoinDecode_exit_ok hsz68) hreach
    · have hwadOk : (joinWadWord I).toNat ≤ intLimit := by omega
      by_cases hvatNoCode :
          Reasoning.Theory.extCodeSizeWord σ_evm
            (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩
      · exact gemJoinExitBodyCoreVatNoCode hcode hsize hwv hsz68 hwadOk hvatNoCode
          hdispatch (gemJoinDecode_exit_ok hsz68) hreach hAccounts
      · have hvatCode :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩ := hvatNoCode
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨_, _, rd1544⟩ :=
            gemJoinExitX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
          obtain ⟨_, _, rd1620⟩ := gemJoinExitX_nonoverflowOk
            (g := Sat256.ofUInt256 g) hwadOk rd1544
          obtain ⟨cA_slip, σ_slip, zSlip, outSlip, A_slip, k1717, C1717,
              rd1717, hcallSlipEvmRaw, houtSlipSize⟩ :=
            RD.gemJoinExitSlipPostCall ⟨_, _, rd1620⟩ hwadOk hvatCode hperm hdepthLt
          cases zSlip
          · exact gemJoinExitBodyCoreSlipCallFailure hcode hsize hwv hsz68 hwadOk
              hvatCode hdispatch (gemJoinDecode_exit_ok hsz68) rd1717
              (by simpa using hcallSlipEvmRaw) houtSlipSize hAccounts
          · obtain ⟨_, _, rd1736⟩ := RD.gemJoinExitSlipCallSuccessToTransferSetup rd1717
            by_cases hgemNoCode :
                Reasoning.Theory.extCodeSizeWord σ_slip
                  (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = (⟨0⟩ : UInt256)
            · exact gemJoinExitBodyCoreGemNoCode hcode hsize hwv hsz68 hwadOk
                hvatCode hgemNoCode hdispatch (gemJoinDecode_exit_ok hsz68)
                rd1736 (by simpa using hcallSlipEvmRaw) hAccounts
            · have hgemCode :
                  Reasoning.Theory.extCodeSizeWord σ_slip
                    (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ (⟨0⟩ : UInt256) :=
                hgemNoCode
              obtain ⟨cA_transfer, σ_transfer, zTransfer, outTransfer, A_transfer,
                  k1827, C1827, rd1827, hcallTransferEvmRaw, houtTransferSize⟩ :=
                RD.gemJoinExitTransferPostCall (Acur := A_slip) rd1736 hgemCode
                  hperm hdepthLt
              cases zTransfer
              · exact gemJoinExitBodyCoreTransferCallFailure hcode hsize hwv hsz68
                  hwadOk hvatCode hgemCode hdepthLt hdispatch
                  (gemJoinDecode_exit_ok hsz68) rd1827
                  (by simpa using hcallSlipEvmRaw)
                  (by simpa using hcallTransferEvmRaw) houtTransferSize hAccounts
              · obtain ⟨_, _, rd1845⟩ := RD.gemJoinExitTransferCallSuccessToDecode rd1827
                by_cases hshort : outTransfer.size < 32
                · exact gemJoinExitBodyCoreTransferDecodeShort hcode hsize hwv hsz68
                    hwadOk hvatCode hgemCode hdepthLt hshort hdispatch
                    (gemJoinDecode_exit_ok hsz68) rd1845
                    (by simpa using hcallSlipEvmRaw)
                    (by simpa using hcallTransferEvmRaw) houtTransferSize hAccounts
                · have hlo : 32 ≤ outTransfer.size := by omega
                  have hSlipMem :
                      (exitSlipCalldataMem I σ_evm solcFreePtrMem).size = 228 :=
                    exitSlipCalldataMem_size_of_size96 I σ_evm solcFreePtrMem_size
                  have hSlipRead64 :
                      (exitSlipCalldataMem I σ_evm solcFreePtrMem).readWithPadding 64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    exitSlipCalldataMem_read64_of_size96 I σ_evm solcFreePtrMem_size
                      solcFreePtrMem_read64
                  have hBaseMem :
                      (exitTransferCalldataMem I
                        (exitSlipCalldataMem I σ_evm solcFreePtrMem)).size = 228 :=
                    exitTransferCalldataMem_size I hSlipMem
                  have hBaseRead64 :
                      (exitTransferCalldataMem I
                        (exitSlipCalldataMem I σ_evm solcFreePtrMem)).readWithPadding 64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    exitTransferCalldataMem_read64 I hSlipMem hSlipRead64
                  have hmin :
                      (min exitTransferOutSize (UInt256.ofNat outTransfer.size)).toNat = 32 := by
                    simpa [exitTransferOutSize] using
                      joinTransferFromMin32_toNat_of_ge hlo houtTransferSize
                  let retWord : UInt256 :=
                    UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
                  let transferReturnMem : ByteArray :=
                    outTransfer.write 0
                      (exitTransferCalldataMem I
                        (exitSlipCalldataMem I σ_evm solcFreePtrMem))
                      exitTransferOutPtr.toNat 32
                  have hmem : transferReturnMem.size = 228 := by
                    simpa [transferReturnMem, exitTransferOutPtr] using
                      joinTransferFromReturnWrite_size 32 hBaseMem (by omega) (by omega)
                  have hread64 :
                      transferReturnMem.readWithPadding 64 32 =
                      UInt256.toByteArray ⟨128⟩ := by
                    simpa [transferReturnMem, exitTransferOutPtr] using
                      joinTransferFromReturnWrite_read64 32 hBaseMem hBaseRead64
                        (by omega) (by omega)
                  have hread128 :
                      transferReturnMem.readWithPadding 128 32 =
                      outTransfer.extract 0 32 := by
                    simpa [transferReturnMem, exitTransferOutPtr] using
                      joinTransferFromReturnWrite_read128_32 hBaseMem hlo
                  have hmload64 :
                      (if (⟨64⟩ : UInt256).toNat ≥ transferReturnMem.size
                          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then
                          ⟨0⟩
                       else
                          UInt256.ofNat
                            (fromByteArrayBigEndian
                              (transferReturnMem.readWithPadding
                                (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ := by
                    exact mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
                  have hnot128 :
                      ¬ ((⟨128⟩ : UInt256).toNat ≥ transferReturnMem.size
                          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩) := by
                    exact not_or.mpr
                      ⟨by
                        rw [hmem]
                        native_decide,
                      by native_decide⟩
                  have hmload128 :
                      (if (⟨128⟩ : UInt256).toNat ≥ transferReturnMem.size
                          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then
                          ⟨0⟩
                       else
                          UInt256.ofNat
                            (fromByteArrayBigEndian
                              (transferReturnMem.readWithPadding
                                  (⟨128⟩ : UInt256).toNat 32))) =
                        retWord := by
                    rw [if_neg hnot128]
                    rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide]
                    rw [hread128]
                  obtain ⟨_, _, rd1868⟩ :=
                    RD.gemJoinExitTransferReturnDecodeOk (retWord := retWord)
                      (by simpa [hmin, transferReturnMem] using rd1845)
                      hlo houtTransferSize hmload64 hmload128
                  by_cases hretZero : retWord = ⟨0⟩
                  · have hword :
                        UInt256.ofNat
                          (fromByteArrayBigEndian (outTransfer.extract 0 32)) = ⟨0⟩ := by
                      simpa [retWord] using hretZero
                    exact gemJoinExitBodyCoreTransferReturnFalseSmall hcode hsize hwv hperm
                      hsz68 hwadOk hvatCode hgemCode hdepthLt hretZero hword hlo hmem
                      hread64 hdispatch (gemJoinDecode_exit_ok hsz68) rd1868
                      hcallSlipEvmRaw hcallTransferEvmRaw hAccounts
                  · have hword :
                        UInt256.ofNat
                          (fromByteArrayBigEndian (outTransfer.extract 0 32)) ≠ ⟨0⟩ := by
                      simpa [retWord] using hretZero
                    exact gemJoinExitBodyCoreTransferReturnTrueSmall hcode hsize hwv hperm
                      hsz68 hwadOk hvatCode hgemCode hdepthLt hretZero hword hlo hmem
                      hread64 hdispatch (gemJoinDecode_exit_ok hsz68) rd1868
                      hcallSlipEvmRaw hcallTransferEvmRaw hAccounts
        · have hdepthEq : I.depth = 1024 := by
            apply Fin.ext
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            omega
          exact gemJoinExitBodyCoreSlipCallDepthLimit hcode hsize hwv hsz68 hwadOk
            hvatCode hdepthEq hdispatch (gemJoinDecode_exit_ok hsz68) hreach hAccounts
  · exact gemJoinExitBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.GemJoin
