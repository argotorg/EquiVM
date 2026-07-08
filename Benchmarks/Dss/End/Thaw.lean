import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `thaw()` transition -/

abbrev endThawConcreteSelector : ByteArray := selectorBytes 0x59 0x20 0x37 0x5c

abbrev endThawEntryPc : UInt256 := ⟨707⟩
abbrev endThawReturnPc : UInt256 := ⟨562⟩
abbrev endThawBodyPc : UInt256 := ⟨4525⟩

abbrev endThawLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

abbrev endThawDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

abbrev endThawVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨1⟩ σ I) solcAddrMask

abbrev endThawVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨4⟩ σ I) solcAddrMask

abbrev endThawVatAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endThawVatWord σ I).toNat

abbrev endThawLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev endThawDebtEvaledRef : EvaledStorageRef :=
  { base := "debt", steps := [] }

abbrev endThawDaiSelectorRaw : UInt256 := ⟨0x3612d9a3⟩
abbrev endThawDaiSelectorWord : UInt256 := ⟨0x6c25b346⟩
abbrev endThawDaiOutPtr : UInt256 := ⟨128⟩
abbrev endThawDaiInSize : UInt256 := ⟨36⟩
abbrev endThawDaiEndPtr : UInt256 := ⟨164⟩

noncomputable def endThawDaiSelectorMem (mem : ByteArray) : ByteArray :=
  (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩).toByteArray.write 0 mem
    endThawDaiOutPtr.toNat 32

noncomputable def endThawDaiCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (endThawVowWord σ I).toByteArray.write 0 (endThawDaiSelectorMem mem)
    (endThawDaiOutPtr + ⟨4⟩).toNat 32

theorem endThawDaiSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endThawDaiSelectorMem mem).size = 160 := by
  unfold endThawDaiSelectorMem
  exact toByteArray_write32_size_of_ge mem (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩)
    endThawDaiOutPtr.toNat 96 160 hmem (by native_decide) (by native_decide)
    (by native_decide)

theorem endThawDaiSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endThawDaiSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endThawDaiSelectorMem
  rw [toByteArray_write_read_below_of_gap (UInt256.shiftLeft endThawDaiSelectorRaw ⟨225⟩)
    mem endThawDaiOutPtr.toNat 64 (by rw [hmem]) (by native_decide)
    (by rw [hmem]; native_decide), hread64]

theorem endThawDaiCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endThawDaiCalldataMem σ I mem).size = 164 := by
  unfold endThawDaiCalldataMem
  exact toByteArray_write32_size_of_le (endThawDaiSelectorMem mem) (endThawVowWord σ I)
    132 160 164 (endThawDaiSelectorMem_size hmem)
    (by rw [endThawDaiSelectorMem_size hmem]; omega) (by omega)

theorem endThawDaiCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endThawDaiCalldataMem σ I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endThawDaiCalldataMem
  change ((endThawVowWord σ I).toByteArray.write 0 (endThawDaiSelectorMem mem) 132
      32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endThawDaiSelectorMem_size hmem]; omega) (by omega),
    endThawDaiSelectorMem_read64 hmem hread64]

theorem endThawVatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endThawVatWord σ I = endThawVatWord τ I := by
  simp [endThawVatWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩]

theorem endThawVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (endThawVatWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (endThawVatWord σ I)
  have htarget : endThawVatWord σ I = endThawVatWord τ I :=
    endThawVatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endThawVatAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endThawVatAddr σ I = AccountAddress.ofUInt256 (endThawVatWord σ I) := by
  simpa [endThawVatAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endThawVatWord σ I)).symm

theorem endThawVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endThawVatWord σ I) (addr := endThawVatAddr σ I)
      (endThawVatAddr_eq_ofUInt256 σ I) hzero

theorem endDecode_thaw {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (thawTransition.params.map Param.name)
      (transitionSignature thawTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endReachThawBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endThawConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endThawEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x5920375c⟩ :=
    endSelWord_eq_of_beq I hsz 0x59 0x20 0x37 0x5c ⟨0x5920375c⟩
      (by native_decide)
      (by simpa [selIs, endThawConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endThawEntryPc 3 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endThawX_entry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endThawEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endThawBodyPc [endThawReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simpa [endThawEntryPc, endThawReturnPc, endThawBodyPc] using
    RD.solcGetterThunk (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (entry := endThawEntryPc) (returnPc := endThawReturnPc) (routine := endThawBodyPc)
      hreach
      (by
        unfold solcGetterEntryWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest)

theorem endThawX_liveNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by native_decide) (by evm_ov)
  have rd4529 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (endThawLiveWord σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawLiveWord, endSlotWord, solcSlotWord] using rd4529raw⟩
  obtain ⟨_, _, rd4529⟩ := rd4529
  have rd4530raw := rd4529.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endThawLiveWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd4530 := rd4530raw
  rw [hzero] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by native_decide) (by evm_ov)
  have rd4534 := rd4533.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4534⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x456e642f7374696c6c2d6c697665⟩) (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f7374696c6c2d6c697665⟩ ⟨144⟩)
    (op := .PUSH14) (width := 14)
    (by simpa using rd4534)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_debtNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd4529zero := rd4529raw
  rw [hliveRaw] at rd4529zero
  obtain ⟨_, _, rd4529⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawBodyPc] using rd4529zero⟩
  have rd4530raw := rd4529.iszero (by native_decide) (by evm_ov)
  have rd4530 := rd4530raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by native_decide) (by evm_ov)
  have rd4595 := rd4533.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4598 := evm_run rd4595 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4599raw⟩ := rd4598.sload (by native_decide) (by evm_ov)
  have rd4599 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4599⟩
        (endThawDebtWord σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawDebtWord, endSlotWord, solcSlotWord] using rd4599raw⟩
  obtain ⟨_, _, rd4599⟩ := rd4599
  have rd4600raw := rd4599.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endThawDebtWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hdebt
  have rd4600 := rd4600raw
  rw [hzero] at rd4600
  have rd4603 := rd4600.push2 ⟨4668⟩ (by native_decide) (by evm_ov)
  have rd4604 := rd4603.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4604⟩) (len := ⟨17⟩)
    (rawWord := ⟨0x456e642f646562742d6e6f742d7a65726f⟩) (shift := ⟨120⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f646562742d6e6f742d7a65726f⟩ ⟨120⟩)
    (op := .PUSH17) (width := 17)
    (by simpa using rd4604)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endThawX_daiNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endThawBodyPc
      [endThawReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4528 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4529raw⟩ := rd4528.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd4529zero := rd4529raw
  rw [hliveRaw] at rd4529zero
  obtain ⟨_, _, rd4529⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4529⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endThawBodyPc] using rd4529zero⟩
  have rd4530raw := rd4529.iszero (by native_decide) (by evm_ov)
  have rd4530 := rd4530raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4530
  have rd4533 := rd4530.push2 ⟨4595⟩ (by native_decide) (by evm_ov)
  have rd4595 := rd4533.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4598 := evm_run rd4595 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4599raw⟩ := rd4598.sload (by native_decide) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd4599zero := rd4599raw
  rw [hdebtRaw] at rd4599zero
  obtain ⟨_, _, rd4599⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4599⟩
        (⟨0⟩ :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd4599zero⟩
  have rd4600raw := rd4599.iszero (by native_decide) (by evm_ov)
  have rd4600 := rd4600raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4600
  have rd4603 := rd4600.push2 ⟨4668⟩ (by native_decide) (by evm_ov)
  have rd4668 := rd4603.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4670 := evm_run rd4668 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4671raw⟩ := rd4670.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4672⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4672⟩
        (endSlotWord ⟨1⟩ σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4671raw⟩
  have rd4675pre := evm_run rd4672 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd4675raw⟩ := rd4675pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4676⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
        (endSlotWord ⟨4⟩ σ I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σ I :: endThawReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4675raw⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endThawDaiCalldataMem σ I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endThawDaiCalldataMem σ I solcFreePtrMem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endThawDaiCalldataMem_size σ I solcFreePtrMem_size]; decide)
      (by decide)
      (endThawDaiCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64)
  have hvatMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨1⟩ σ I) = endThawVatWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
  have hvowMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endSlotWord ⟨4⟩ σ I) = endThawVowWord σ I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by native_decide]
  have rd4737pre := evm_run rd4676 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 endThawDaiSelectorRaw (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endThawDaiSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw mstore 3 (endThawDaiCalldataMem σ I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        rw [hvowMask]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endThawDaiSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd4737 :=
    (by
      simpa [endThawDaiSelectorMem, endThawDaiCalldataMem, endThawDaiOutPtr,
        endThawDaiInSize, endThawDaiEndPtr, endThawDaiSelectorWord, endThawDaiSelectorRaw,
        endThawVatWord, endThawVowWord, endSlotWord, solcSlotWord, solcAddrMask,
        hvatMask, hvowMask, u256_land_comm] using rd4737pre)
  have hcodeSizeGuard := hcodeSize
  rw [← hvatMask] at hcodeSizeGuard
  exact RD.uniswapExtcodesizeGuardMissing (okPc := ⟨4749⟩) rd4737
    hcodeSizeGuard
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalStorageRef_endThaw_live (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      liveRef = .ok endThawLiveEvaledRef := by
  simp [endThawLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_debt (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      debtRef = .ok endThawDebtEvaledRef := by
  simp [endThawDebtEvaledRef, debtRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalStorageRef_endThaw_vat {locals : Store} (_hbase : locals.get? "vat" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      vatRef = .ok ({ base := "vat", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]

theorem evalExpr_endThaw_vat {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨1⟩)
    (hbase := hbase)
    (her := evalStorageRef_endThaw_vat hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨1⟩)

theorem evalExpr_endThaw_live_zero_false (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := liveRef)
      (er := endThawLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [liveRef])
      (her := evalStorageRef_endThaw_live evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem endThawBodyReverts_liveNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hlive
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endThaw_live_zero_false evm0 hliveLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [thawTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (evm := evm0)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage debtRef) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
        [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
          .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
          .require (.binary .ge nowT (.var "deadline")) ] ++
        checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
        checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem evalExpr_endThaw_debt_zero_false (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage debtRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := (∅ : Store) })
      (slot := debtRef)
      (er := endThawDebtEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨11⟩)
      (hbase := by simp [debtRef])
      (her := evalStorageRef_endThaw_debt evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨11⟩)
  have hzero :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply hload
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem endThawBodyReverts_debtNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hbad
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endThaw_debt_zero_false evm0 hdebtLoad
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardDebt)
  simpa [ExecTransitionBody, thawTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endThawBodyReverts_daiNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWord σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (endThawVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (∅ : Store) thawTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawLiveWord, endSlotWord, solcSlotWord] using hlive
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguardLive :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage liveRef) = .ok (.int 0) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := liveRef)
        (er := endThawLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [liveRef])
        (her := evalStorageRef_endThaw_live evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardDebt :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .eq (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.storage debtRef) = .ok (.int 0) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := (∅ : Store) })
        (slot := debtRef)
        (er := endThawDebtEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int 0)
        (hbase := by simp [debtRef])
        (her := evalStorageRef_endThaw_debt evm0)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hdebtLoad] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hreceiver :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.storage vatRef) = .ok (.address (endThawVatAddr σ I)) := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endThawVatAddr, endThawVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endThaw_vat (locals := (∅ : Store)) evm0 (by simp)
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endThawVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endThawVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardDai :
      evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hdaiBlock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false)) .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm0)
        (locals := (∅ : Store)) (receiver := .storage vatRef)
        (retVar := "vatDai") (name := "dai") (sendVal := 0)
        (args := [vowAddr]) (perm := false) hguardDai
  have hdaiWithTail :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        (checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ++
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term
      (s2 :=
          [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
            .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
            .require (.binary .ge nowT (.var "deadline")) ] ++
          checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
          checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ])
      hdaiBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := (∅ : Store) } evm0
        thawTransition.body .reverted := by
    simp only [thawTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdaiWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endThawBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf thawTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endThawConcreteSelector := by
    simpa [endThawSelectorBytes, endThawConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endThawConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some thawTransition :=
    endDispatchThaw hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (thawTransition.params.map Param.name)
        (transitionSignature thawTransition).paramTypes I.calldata = some ∅ :=
    endDecode_thaw hsz4
  have hreach := endReachThawBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  obtain ⟨_, _, hbodyReach⟩ := endThawX_entry hreach
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveCouple : endThawLiveWord σ_evm I = endThawLiveWord σ_solm I := by
    simpa [endThawLiveWord, endSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  by_cases hlive : endThawLiveWord σ_evm I = ⟨0⟩
  · have hliveSolm : endThawLiveWord σ_solm I = ⟨0⟩ := by
      rw [← hliveCouple]
      exact hlive
    have hdebtCouple : endThawDebtWord σ_evm I = endThawDebtWord σ_solm I := by
      simpa [endThawDebtWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebt : endThawDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : endThawDebtWord σ_solm I = ⟨0⟩ := by
        rw [← hdebtCouple]
        exact hdebt
      by_cases hvatCode :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (endThawVatWord σ_evm I) =
            ⟨0⟩
      · have hvatCodeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
              (endThawVatWord σ_solm I) = ⟨0⟩ :=
          endThawVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
        have hbody :
            ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body
              .reverted := by
          simpa [evmSolm] using
            endThawBodyReverts_daiNoCode
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hliveSolm hdebtSolm hvatCodeSolm
        exact (endThawX_daiNoCode (g := Sat256.ofUInt256 g) hlive hdebt hvatCode hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · sorry
    · have hdebtSolm : endThawDebtWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebt (by rw [hdebtCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body .reverted := by
        simpa [evmSolm] using
          endThawBodyReverts_debtNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hliveSolm hdebtSolm
      exact (endThawX_debtNonzero (g := Sat256.ofUInt256 g) hlive hdebt hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hliveSolm : endThawLiveWord σ_solm I ≠ ⟨0⟩ := by
      intro hbad
      exact hlive (by rw [hliveCouple, hbad])
    have hbody :
        ExecTransitionBody config contract evmSolm (∅ : Store) thawTransition.body .reverted := by
      simpa [evmSolm] using
        endThawBodyReverts_liveNonzero
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv hliveSolm
    exact (endThawX_liveNonzero (g := Sat256.ofUInt256 g) hlive hbodyReach)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.End
