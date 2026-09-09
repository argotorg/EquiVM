import Examples.UniswapV2Pair.SkimCommon
import Examples.UniswapV2Pair.SkimSafeTransferCalldata
import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.TransferRoutines
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## EVM trace prefix -/

abbrev skimSafeTransferSignatureWord : UInt256 :=
  ⟨52670383448186445861553817759887498218675746408080920759387454194053457903616⟩

noncomputable def skimSafeTransferMem0 (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0 (balanceOfThisStaticcallMem self o) 64 32

noncomputable def skimSafeTransferMem1 (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0 (skimSafeTransferMem0 self o) 128 32

noncomputable def skimSafeTransferMem2 (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray skimSafeTransferSignatureWord).write 0
    (skimSafeTransferMem1 self o) 160 32

noncomputable def skimSafeTransferMem3
    (self : UInt256) (o : ByteArray) (toWord : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask toWord)).write 0
    (skimSafeTransferMem2 self o) 228 32

noncomputable def skimSafeTransferMem4
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (skimSafeTransferMem3 self o toWord) 260 32

noncomputable def skimSafeTransferMem5
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨68⟩ : UInt256)).write 0
    (skimSafeTransferMem4 self o toWord value) 192 32

noncomputable def skimSafeTransferMem5WritesAfter64
    (toWord value : UInt256) : List (Nat × UInt256) :=
  [(128, (⟨25⟩ : UInt256)),
   (160, skimSafeTransferSignatureWord),
   (228, UInt256.land solcAddrMask toWord),
   (260, value),
   (192, (⟨68⟩ : UInt256))]

noncomputable def skimSafeTransferMem5Writes
    (toWord value : UInt256) : List (Nat × UInt256) :=
  (64, (⟨192⟩ : UInt256)) :: skimSafeTransferMem5WritesAfter64 toWord value

theorem skimSafeTransferMem5_eq_writeCascade
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) :
    skimSafeTransferMem5 self o toWord value =
      writeCascade (balanceOfThisStaticcallMem self o)
        (skimSafeTransferMem5Writes toWord value) := by
  rfl

theorem skimSafeTransferMem5Writes_size (toWord value : UInt256) :
    writeCascadeSize 164 (skimSafeTransferMem5Writes toWord value) = 292 := by
  rfl

theorem skimSafeTransferMem5Writes_gaps (toWord value : UInt256) :
    WriteGapsOk 164 (skimSafeTransferMem5Writes toWord value) := by
  simp [WriteGapsOk, skimSafeTransferMem5Writes, skimSafeTransferMem5WritesAfter64]
  exact lt_usize 36 (by norm_num)

theorem skimSafeTransferMem5WritesAfter64_disjoint64 (toWord value : UInt256) :
    WindowDisjointFromWrites 164 64 32 (skimSafeTransferMem5WritesAfter64 toWord value) := by
  simp [WindowDisjointFromWrites, skimSafeTransferMem5WritesAfter64]
  exact lt_usize 36 (by norm_num)

noncomputable def skimSafeTransferMem6
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨292⟩ : UInt256)).write 0
    (skimSafeTransferMem5 self o toWord value) 64 32

abbrev skimSafeTransferSelectorPatchMask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩) ⟨1⟩

noncomputable def skimSafeTransferWord224
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian ((skimSafeTransferMem6 self o toWord value).readWithPadding 224 32))

noncomputable def skimSafeTransferPatchedSelectorWord
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft transferSelectorWord ⟨224⟩)
    (UInt256.land skimSafeTransferSelectorPatchMask
      (skimSafeTransferWord224 self o toWord value))

noncomputable def skimSafeTransferMem7
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (skimSafeTransferPatchedSelectorWord self o toWord value)).write 0
    (skimSafeTransferMem6 self o toWord value) 224 32

theorem skimSafeTransferMem0_size (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem0 self o).size = 164 := by
  unfold skimSafeTransferMem0
  exact toByteArray_write32_size_of_le _ _ 64 164 164
    (balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize)
    (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]; omega)
    (by norm_num)

theorem skimSafeTransferMem1_size (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem1 self o).size = 164 := by
  unfold skimSafeTransferMem1
  exact toByteArray_write32_size_of_le _ _ 128 164 164
    (skimSafeTransferMem0_size self ho32 hoSize)
    (by rw [skimSafeTransferMem0_size self ho32 hoSize]; omega)
    (by norm_num)

theorem skimSafeTransferMem2_size (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem2 self o).size = 192 := by
  unfold skimSafeTransferMem2
  exact toByteArray_write32_size_of_le _ _ 160 164 192
    (skimSafeTransferMem1_size self ho32 hoSize)
    (by rw [skimSafeTransferMem1_size self ho32 hoSize]; omega)
    (by norm_num)

theorem skimSafeTransferMem0_read64 (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem0 self o).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold skimSafeTransferMem0
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray (⟨192⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨192⟩ : UInt256)).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSafeTransferMem1_read64 (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem1 self o).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold skimSafeTransferMem1
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferMem0_size self ho32 hoSize]; omega) (by omega)]
  exact skimSafeTransferMem0_read64 self ho32 hoSize

theorem skimSafeTransferMem2_read64 (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem2 self o).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold skimSafeTransferMem2 skimSafeTransferMem1 skimSafeTransferMem0
  simpa [writeCascade, Reasoning.Theory.writeWord] using
    writeCascade_read_word_of_head_of_base
      (balanceOfThisStaticcallMem self o) (base := 164) (off := 64) (⟨192⟩ : UInt256)
      [(128, (⟨25⟩ : UInt256)), (160, skimSafeTransferSignatureWord)]
      (balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize)
      (lt_usize 0 (by norm_num))
      (by simp [WindowDisjointFromWrites])

theorem skimSafeTransferMem2_mload64 (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSafeTransferMem2 self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem2 self o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferMem2_size self ho32 hoSize]; decide)
    (by decide +native) (skimSafeTransferMem2_read64 self ho32 hoSize)

theorem skimSafeTransferMem3_size (self : UInt256) {o : ByteArray} (toWord : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem3 self o toWord).size = 260 := by
  unfold skimSafeTransferMem3
  exact toByteArray_write32_size_of_ge _ _ 228 192 260
    (skimSafeTransferMem2_size self ho32 hoSize)
    (by norm_num) (lt_usize 36 (by norm_num)) (by norm_num)

theorem skimSafeTransferMem3_read64 (self : UInt256) {o : ByteArray} (toWord : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem3 self o toWord).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold skimSafeTransferMem3
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask toWord) _ 228 64
      (by rw [skimSafeTransferMem2_size self ho32 hoSize]; omega) (by omega)
      (by rw [skimSafeTransferMem2_size self ho32 hoSize]; exact lt_usize _ (by norm_num))]
  exact skimSafeTransferMem2_read64 self ho32 hoSize

theorem skimSafeTransferMem4_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem4 self o toWord value).size = 292 := by
  unfold skimSafeTransferMem4
  exact toByteArray_write32_size_of_ge _ _ 260 260 292
    (skimSafeTransferMem3_size self toWord ho32 hoSize)
    (by norm_num) (lt_usize 0 (by norm_num)) (by norm_num)

theorem skimSafeTransferMem4_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem4 self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold skimSafeTransferMem4 skimSafeTransferMem3
  change (writeCascade (skimSafeTransferMem2 self o)
      [(228, UInt256.land solcAddrMask toWord), (260, value)]).readWithPadding 64 32 =
    UInt256.toByteArray (⟨192⟩ : UInt256)
  rw [writeCascade_read_preserved_len]
  · exact skimSafeTransferMem2_read64 self ho32 hoSize
  · rw [skimSafeTransferMem2_size self ho32 hoSize]
    simp [WindowDisjointFromWrites]
    exact lt_usize 36 (by norm_num)
  · norm_num
  · norm_num

theorem skimSafeTransferMem4_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSafeTransferMem4 self o toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem4 self o toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSafeTransferMem4_size self toWord value ho32 hoSize]; decide)
    (by decide +native) (skimSafeTransferMem4_read64 self toWord value ho32 hoSize)

theorem skimSafeTransferMem5_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem5 self o toWord value).size = 292 := by
  rw [skimSafeTransferMem5_eq_writeCascade]
  exact safeTransferCalldata_writeCascade_size _ _ 164 292
    (balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize)
    (by
      rw [balanceOfThisStaticcallMem_size_of_size_ge self o ho32 hoSize]
      exact skimSafeTransferMem5Writes_gaps toWord value)
    (skimSafeTransferMem5Writes_size toWord value)

theorem skimSafeTransferMem6_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSafeTransferMem6 self o toWord value).size = 292 := by
  unfold skimSafeTransferMem6
  exact toByteArray_write32_size_of_le _ _ 64 292 292
    (skimSafeTransferMem5_size self toWord value ho32 hoSize)
    (by rw [skimSafeTransferMem5_size self toWord value ho32 hoSize]; omega)
    (by norm_num)

theorem skimSafeTransferMem6_mload224
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥ (skimSafeTransferMem6 self o toWord value).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSafeTransferMem6 self o toWord value).readWithPadding
          (⟨224⟩ : UInt256).toNat 32)))
      = skimSafeTransferWord224 self o toWord value := by
  unfold skimSafeTransferWord224
  exact mloadValue_eq_readWithPadding_of_lt_size _ (UInt256.ofNat 10) ⟨224⟩ 292
    (skimSafeTransferMem6_size self toWord value ho32 hoSize)
    (by decide +native) (by decide +native)

/-- The optimized external wrapper for `skim(address)` accepts canonical calldata and jumps to the
    external skim routine at pc 5080. -/
theorem uniswapSkimX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5080⟩
      [skimToWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1308⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd5080⟩ := RD.uniswapOneAddressExternalMaskAndJump
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) (R := [sel]) rd1308
    uniswap_one_address_external_entry_wf
    (by simpa [skimToWord] using hcanonTo)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [skimToWord] using rd5080⟩

/-- The optimized external wrapper for `skim(address)` masks legacy-address calldata and jumps to
the external skim routine at pc 5080. -/
theorem uniswapSkimX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5080⟩
      [skimToMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1308⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd5080⟩ := RD.uniswapOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) (R := [sel])
    rd1308 uniswap_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [skimToWord, skimToMaskedWord] using rd5080⟩

/-- After the external wrapper has decoded `toWord`, `skim(address)` successfully enters the
Uniswap lock. -/
theorem uniswapSkimX_lockEntered {cA gh bl σ σ₀ A I} {g : Sat256} {sel toWord : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5080⟩ [toWord, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5161⟩
      [toWord, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd5080⟩ := hdecoded
  obtain ⟨_, _, rd5161⟩ := RD.uniswapLockEnterOk
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [toWord, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd5161⟩

/-- Runtime-only `skim(address)` slice from decoded external-wrapper entry through successful lock
entry. -/
theorem uniswapSkimRuntimeLockEntered
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5080⟩
      [toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5161⟩
      [toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  exact uniswapSkimX_lockEntered
    (g := Sat256.ofUInt256 g) hperm hunlocked hdecoded

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice from successful lock entry to the first
`token0.balanceOf(address(this))` code-existence guard. -/
theorem uniswapSkimRuntimeFirstBalanceOfExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord : UInt256}
    (hLock : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5161⟩
      [toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5161⟩ := hLock
  have rd5163 := evm_run rd5161 with [push1 ⟨6⟩]
  obtain ⟨k5164, C5164, rd5164₀⟩ := rd5163.sload (by decide +native) (by evm_ov)
  have rd5164 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5164⟩
      [token0Word, toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5164 C5164 := by
    simpa [σLock, token0Word, uniswapSlotWord] using rd5164₀
  have rd5166 := evm_run rd5164 with [push1 ⟨7⟩]
  obtain ⟨k5167, C5167, rd5167₀⟩ := rd5166.sload (by decide +native) (by evm_ov)
  have rd5167 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5167⟩
      [token1Word, token0Word, toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5167 C5167 := by
    simpa [σLock, token1Word, uniswapSlotWord] using rd5167₀
  have rd5169 := evm_run rd5167 with [push1 ⟨8⟩]
  obtain ⟨k5170, C5170, rd5170₀⟩ := rd5169.sload (by decide +native) (by evm_ov)
  have rd5170 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5170⟩
      [packedWord, token1Word, token0Word, toWord, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5170 C5170 := by
    simpa [σLock, packedWord, uniswapSlotWord] using rd5170₀
  have rd5183 := evm_run rd5170 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd5184 := rd5183.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5189 := evm_run rd5184 with [
    address, push1 ⟨4⟩, dup3, add]
  have rd5190 := rd5189.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5192 := evm_run rd5190 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov)]
  have rd5207₀ := evm_run rd5192 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap5, dup6, and, swap5, swap1, swap4, and, swap3]
  have rd5207 := rd5207₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5207
  have rd5220 := evm_run rd5207 with [
    push2 ⟨5330⟩, swap3, dup6, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5229 := evm_run rd5220 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5257₀ := evm_run rd5229 with [
    dup6, swap2, push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1,
    dup3, add, swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3,
    swap1, sub, add, dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5257₀
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5257₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first `balanceOf` code-existence guard when
`token0` has deployed code, stopping immediately before `GAS; STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallReady
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {toWord : UInt256}
    (rd5257 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5271⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5271⟩ :=
    RD.solcExtcodesizeGuardOk (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest)
      (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5271⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through `GAS`, stopping at the first
`token0.balanceOf(address(this))` `STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {toWord : UInt256}
    (rd5257 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ gasWord k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5272⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨gasWord, _, _, rd5272⟩ :=
    RD.solcExtcodesizeGuardOkGas (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest)
      (by decide +native) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5272⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first opaque
`token0.balanceOf(address(this))` `STATICCALL`, exposing the shared `Θ` result. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ} {gasWord toWord : UInt256}
    (rd5272 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5272⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, toWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        toWord, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, toWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            toWord, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd5273, hoSize⟩ :=
    RD.solcStaticcall rd5272 (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    by simpa [σLock, token0Word, token0Clean, initState] using hΘ,
    by
      simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
        reserve0Word, balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using
        rd5273,
    hoSize⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only first `balanceOf` post-call status guard from the shared `STATICCALL` result.
The continuation stack tail is arbitrary, so canonical and masked `to` words use the same proof. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    {k C : ℕ} {R : List UInt256}
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
    (rd5273 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
      ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨164⟩ :: balanceOfSelectorWord ::
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I) :: R)
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k C)
    (hoSize : o.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    have rdRev :=
      RD.solcCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 hstatus
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) hoSize
        (by simp only [List.length_cons]; omega)
    exact rdRev
  · intro hz hshort
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5291⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
        (by simp only [List.length_cons]; omega)
    have rdRev :=
      RD.uniswapBalanceOfReturnWordDecodeShortReverts
        (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd5291 hshort hoSize
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native)
        (by omega)
    exact rdRev
  · intro hz ho32
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5291⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
        (by simp only [List.length_cons]; omega)
    obtain ⟨k', C', rd5314⟩ :=
      RD.uniswapBalanceOfReturnWordDecodeOk
        (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd5291 ho32 hoSize
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by decide +native) (by decide +native) (by decide +native) (by decide +native)
        (by jump_dest) (by decide +native) (by decide +native) (by decide +native)
        (by omega)
    exact ⟨k', C', rd5314⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only bridge from the decoded first `balanceOf` word into checked-sub. -/
theorem RD.uniswapSkimFirstExcessToSub {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {balance0 reserve0 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5314⟩
      (balance0 :: reserve0 :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (reserve0 :: balance0 :: ret :: R) mem aw rdata acc k' C' := by
  have rd6879ret := evm_run h with [
    swap1, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  have rd6879 := rd6879ret.jump (by decide) (by jump_dest) (by evm_ov)
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd6879
  exact ⟨_, _, by simpa using rd6879⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only bridge from the first successful checked subtraction into the `_safeTransfer`
helper entry. -/
theorem RD.uniswapSkimFirstExcessSuccessToSafeTransferEntry {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {balance0 reserve0 toWord token0 token1 ret sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (reserve0 :: balance0 :: ⟨5325⟩ :: toWord :: token0 :: ⟨5330⟩ ::
        token1 :: token0 :: toWord :: ret :: sel :: [])
      mem aw rdata acc k C)
    (hle : reserve0.toNat ≤ balance0.toNat) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (UInt256.sub balance0 reserve0 :: toWord :: token0 :: ⟨5330⟩ ::
        token1 :: token0 :: toWord :: ret :: sel :: [])
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5325⟩ :=
    RD.uniswapSafeMathSubSuccess h hle (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6370ret := evm_run rd5325 with [jumpdest, push2 ⟨6370⟩]
  have rd6370 := rd6370ret.jump (by decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd6370⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `_safeTransfer` prefix from helper entry through `MLOAD(0x40)`. -/
theorem RD.uniswapSkimSafeTransferEntryToFreePtr {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6370⟩
      (value :: toWord :: token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (balanceOfThisStaticcallMem self o) balanceOfThisStaticcallActiveWords o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6375⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (balanceOfThisStaticcallMem self o) balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rd6375 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide +native)
      mem_cost (balanceOfThisStaticcallMem_mload64_of_size_ge self o ho32 hoSize)
      (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6375⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferFreePtrToMem0 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6375⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (balanceOfThisStaticcallMem self o) balanceOfThisStaticcallActiveWords o acc k C) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6380⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem0 self o) balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rd6380 := evm_run h with [
    dup1, dup3, add, dup3,
    raw mstore 0 (skimSafeTransferMem0 self o) balanceOfThisStaticcallActiveWords
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem0; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6380⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferMem0ToMem1 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6380⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem0 self o) balanceOfThisStaticcallActiveWords o acc k C) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6384⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem1 self o) balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rd6384 := evm_run h with [
    push1 ⟨25⟩, dup2,
    raw mstore 0 (skimSafeTransferMem1 self o) balanceOfThisStaticcallActiveWords
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem1; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6384⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferMem1ToSignatureWord {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6384⟩
      (⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem1 self o) balanceOfThisStaticcallActiveWords o acc k C) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6417⟩
      (skimSafeTransferSignatureWord :: ⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem1 self o) balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rd6417 := h.pushConst skimSafeTransferSignatureWord (width := 32) (op := .PUSH32)
    (by decide +native) (by decide +native) (by evm_ov)
  exact ⟨_, _, by simpa using rd6417⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferSignatureWordToMem2 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6417⟩
      (skimSafeTransferSignatureWord :: ⟨128⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem1 self o) balanceOfThisStaticcallActiveWords o acc k C) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6423⟩
      (⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem2 self o) balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rd6423 := evm_run h with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mstore 0 (skimSafeTransferMem2 self o) balanceOfThisStaticcallActiveWords
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem2; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6423⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferMem2ToRecipientStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6423⟩
      (⟨32⟩ :: ⟨64⟩ :: value :: toWord :: token :: ret ::
        token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem2 self o) balanceOfThisStaticcallActiveWords o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6441⟩
      (solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem3 self o toWord) (UInt256.ofNat 9) o acc k' C' := by
  have rd6425 := evm_run h with [
    dup2,
    raw mload 0 ⟨192⟩ balanceOfThisStaticcallActiveWords
      (by decide +native) mem_cost
      (skimSafeTransferMem2_mload64 self ho32 hoSize)
      (by decide +native) (by evm_ov)]
  have rd6441 := evm_run rd6425 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, dup2, and,
    push1 ⟨36⟩, dup4, add,
    raw mstore 9 (skimSafeTransferMem3 self o toWord) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem3; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6441⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferRecipientStoreToValueStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6441⟩
      (solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem3 self o toWord) (UInt256.ofNat 9) o acc k C) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6449⟩
      (⟨68⟩ :: solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem4 self o toWord value) (UInt256.ofNat 10) o acc k' C' := by
  have rd6449 := evm_run h with [
    push1 ⟨68⟩, dup1, dup4, add, dup7, swap1,
    raw mstore 3 (skimSafeTransferMem4 self o toWord value) (UInt256.ofNat 10)
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem4; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6449⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSafeTransferValueStoreToCopySetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord token token1 ret sel : UInt256}
    {o : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6449⟩
      (⟨68⟩ :: solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem4 self o toWord value) (UInt256.ofNat 10) o acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6466⟩
      (solcAddrMask :: ⟨192⟩ :: ⟨32⟩ :: ⟨64⟩ :: value :: toWord ::
        token :: ret :: token1 :: token :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferMem6 self o toWord value) (UInt256.ofNat 10) o acc k' C' := by
  have rd6451 := evm_run h with [
    dup5,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 10)
      (by decide +native) mem_cost
      (skimSafeTransferMem4_mload64 self toWord value ho32 hoSize)
      (by decide +native) (by evm_ov)]
  have rd6459 := evm_run rd6451 with [
    dup1, dup5, sub, swap1, swap2, add, dup2,
    raw mstore 0 (skimSafeTransferMem5 self o toWord value) (UInt256.ofNat 10)
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem5; rfl) (by decide +native) (by evm_ov)]
  have rd6466 := evm_run rd6459 with [
    push1 ⟨100⟩, swap1, swap3, add, dup5,
    raw mstore 0 (skimSafeTransferMem6 self o toWord value) (UInt256.ofNat 10)
      (by decide +native) mem_cost
      (by unfold skimSafeTransferMem6; rfl) (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6466⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` first `balanceOf` slice for the call-depth limit.

At depth 1024 the `STATICCALL` is not made, pushes status `0`, and the high-level call-success
guard reverts. This theorem is insensitive to the canonical/masked contents of the stack tail. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (rd5272 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5272⟩
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (hdepth : I.depth = 1024)
    (hovStatic : t.length + 1 ≤ 1024)
    (hovGuard : t.length + 5 ≤ 1024) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd5273⟩ :=
    RD.solcStaticcallDepthLimit rd5272 (by decide +native) hdepth
      hovStatic
  have rdRev :=
    RD.solcCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 rfl
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide)
      hovGuard
  simpa using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first `balanceOf` post-call status guard.
When the opaque `STATICCALL` succeeds, control reaches the success path at pc 5291. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5291⟩
          [⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  have hdecoded :=
    uniswapSkimX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hsz36 hsize hcanonTo
      (uniswapReachSkimBody
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
  have hLock :=
    uniswapSkimRuntimeLockEntered
      (g := g) (toWord := skimToWord I) hperm hunlocked hdecoded
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize
      (g := g) (toWord := skimToWord I) hLock
  obtain ⟨_, _, _, rd5272⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
      (g := g) (toWord := skimToWord I) rd5257 htoken0Code
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallMade
      (g := g) (toWord := skimToWord I) rd5272 hdepth
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, ?_, hoSize⟩
  intro hz
  have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hz]
    decide
  obtain ⟨k', C', rd5291⟩ :=
    RD.solcCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5291⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice decoding the first successful `balanceOf` return word. -/
theorem uniswapSkimRuntimeFirstBalanceOfReturnWordDecoded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
          [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, hsucc, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd5291⟩ := hsucc hz
  obtain ⟨k', C', rd5314⟩ :=
    RD.uniswapBalanceOfReturnWordDecodeOk
      (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd5291 ho32 hoSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by jump_dest) (by decide +native) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5314⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice showing that a successful first `balanceOf` call with
short ABI returndata reverts while decoding the return word. -/
theorem uniswapSkimRuntimeFirstBalanceOfReturnWordDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, _k, _C, hΘ, _rd5273, hsucc, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, hoSize⟩
  intro hz hshort
  obtain ⟨_, _, rd5291⟩ := hsucc hz
  have rdRev :=
    RD.uniswapBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd5291 hshort hoSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only first `balanceOf` guard revert once control has reached the `EXTCODESIZE`
guard. This theorem is insensitive to whether the decoded `to` word in the stack tail is canonical
or masked. -/
theorem uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (rd5257 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I) ::
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I) :: R)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  have rdRev :=
    RD.solcExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0NoCode)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native)
      hov
  simpa [σLock, token0Word, token0Clean] using rdRev

/-- After the external wrapper has decoded `toWord`, `skim(address)` reverts when the Uniswap
lock is already held. -/
theorem uniswapSkimX_locked {cA gh bl σ σ₀ A I} {g : Sat256} {sel toWord : UInt256}
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5080⟩ [toWord, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5080⟩ := hdecoded
  exact RD.uniswapLockEnterLocked
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [toWord, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_guard_wf uniswap_lock_revert_tail_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Short-calldata path for `skim(address)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than one ABI word. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapSkimX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapOneAddressExternalShort
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩)
    hreach uniswap_one_address_external_entry_wf hsz4 hsize hshort

end UniswapV2Pair
