import Benchmarks.Dss.Vow.Constructor
import Reasoning.ExternalCall
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Solc
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vow constructor tail

Terminal EVM trace facts for the constructor after the external `vat.hope(flapper)` call.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

macro "ctor_tail_decode" : tactic =>
  `(tactic|
    (rw [Reasoning.Theory.decode_append_left_window
      vowCreationBytecode _ _ (by native_decide) (by native_decide)]
     native_decide))

macro "ctor_tail_jump_dest" : tactic =>
  `(tactic|
    (exact D_J_contains_append_left vowCreationBytecode _ _ (by jump_dest)))

theorem vowCtorHopeCallFailure
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σFinal : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (vat flapper flopper : AccountAddress)
    (rd217 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
        (⟨0⟩ :: rest) mem aw out (createdAccounts', σFinal) k C)
    (hout : out.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨217⟩) (okPc := ⟨233⟩) rd217
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode)
    (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode)
    (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode)
    hout hov

theorem vowCtorHopeCallSuccessToReturnStart
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σFinal : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {mem out : ByteArray} {aw target : UInt256} {k C : ℕ}
    (vat flapper flopper : AccountAddress)
    (rd217 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
        (⟨1⟩ :: vowCtorCallEndPtr :: vowCtorHopeSelectorWord :: target ::
          EVM.word flopper.val :: EVM.word flapper.val :: EVM.word vat.val :: [])
        mem aw out (createdAccounts', σFinal) k C)
    (hperm : I.perm = true) :
    ∃ k' C',
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨246⟩
        [] mem aw out
        (createdAccounts', sstoreAccountMap I.codeOwner σFinal ⟨12⟩ ⟨1⟩) k' C' := by
  obtain ⟨_, _, rd235⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨217⟩) (okPc := ⟨233⟩) rd217
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode) (by ctor_tail_decode)
      (by ctor_tail_decode) (by ctor_tail_jump_dest) (by ctor_tail_decode) (by ctor_tail_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd236 := rd235.pop (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd238 := rd236.push1 ⟨1⟩ (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd240 := rd238.push1 ⟨12⟩ (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd241⟩ := rd240.sstore hperm (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd242 := rd241.pop (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd243 := rd242.pop (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd244 := rd243.pop (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd245 := rd244.pop (by ctor_tail_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd246 := rd245.pop (by ctor_tail_decode)
    (by simp)
  exact ⟨_, _, by simpa using rd246⟩

private theorem vowCreationBytecode_size_tail : vowCreationBytecode.size = 5410 := by
  native_decide

private theorem vowBytecode_size_tail : vowBytecode.size = 5150 := by
  native_decide

theorem vowCtorRuntimeWindow (vat flapper flopper : AccountAddress) :
    (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper).extract 260 5410 =
      vowBytecode := by
  rw [Reasoning.Theory.byteArray_extract_append_left]
  · native_decide
  · rw [vowCreationBytecode_size_tail]

def vowCtorRuntimeMem (vat flapper flopper : AccountAddress) (mem : ByteArray) :
    ByteArray :=
  (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper).write 260 mem 0 5150

theorem vowCtorRuntimeMem_read (vat flapper flopper : AccountAddress) (mem : ByteArray) :
    (vowCtorRuntimeMem vat flapper flopper mem).readWithPadding 0 5150 = vowBytecode := by
  rw [vowCtorRuntimeMem]
  rw [write0_read_back_from_gen
    (src := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper)
    (base := mem) (srcAddr := 260) (len := 5150)]
  · simpa [show 260 + 5150 = 5410 by norm_num] using
      vowCtorRuntimeWindow vat flapper flopper
  · norm_num
  · rw [ByteArray.size_append, vowCreationBytecode_size_tail, vowCtorArgsTail_size]
    norm_num
  · norm_num

theorem vowCtorReturnRuntime
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σFinal : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {mem out : ByteArray} {k C : ℕ}
    (vat flapper flopper : AccountAddress)
    (rd246 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨246⟩
        [] mem (UInt256.ofNat 9) out (createdAccounts', σFinal) k C) :
    RDret (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts', σFinal) vowBytecode := by
  exact evm_run rd246 with [
    raw push2 ⟨5150⟩ (by ctor_tail_decode) (by evm_ov),
    raw dup1 (by ctor_tail_decode) (by evm_ov),
    raw push2 ⟨260⟩ (by ctor_tail_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_tail_decode) (by evm_ov),
    raw codecopy 506 (vowCtorRuntimeMem vat flapper flopper mem) (UInt256.ofNat 161)
      (by ctor_tail_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_tail_decode) (by evm_ov),
    raw ret 0 vowBytecode (by ctor_tail_decode) mem_cost
      (vowCtorRuntimeMem_read vat flapper flopper mem) (by evm_ov)]

theorem vowCtorHopeSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 224) :
    (vowCtorHopeSelectorMem mem).extract 224 228 = vatHopeSelector := by
  unfold vowCtorHopeSelectorMem
  have hgap : 224 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_eq vowCtorHopeSelectorShifted mem 224
    (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (USize.ofNat (224 - mem.size))).size = 224 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' hgap, hmem]
  rw [extract_append_right_window _ _ 224 228 (by rw [hprefix]), hprefix,
    show 224 - 224 = 0 from rfl, show 228 - 224 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem vowCtorHopeCalldataMem_read224_36 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 224) :
    (vowCtorHopeCalldataMem arg mem).readWithPadding 224 36 =
      vatHopeSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 224 36 (by norm_num) (by norm_num)
      (by rw [vowCtorHopeCalldataMem_size arg hmem]), vowCtorHopeCalldataMem,
    write32_eq _ (vowCtorHopeSelectorMem mem) 228 (by rw [toByteArray_size])
      (by rw [vowCtorHopeSelectorMem_size hmem]; omega)]
  have hAsz : ((vowCtorHopeSelectorMem mem).extract 0 228).size = 228 := by
    rw [ByteArray.size_extract, vowCtorHopeSelectorMem_size hmem]
    omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((vowCtorHopeSelectorMem mem).extract 0 228 ++
        arg.toByteArray.extract 0 32).size = 260 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 224 260 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 228 224 228 (by omega), vowCtorHopeSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (260 - 228)) 32 = 32 from by omega, hBfull]

theorem vowCtorHopeEncode_eq (flapper : AccountAddress) {mem : ByteArray}
    (hmem : mem.size = 224) :
    config.externalABI.encode? "hope" [.address flapper] =
      some ((vowCtorHopeCalldataMem (EVM.word flapper.val) mem).readWithPadding
        vowCtorCallOutPtr.toNat vowCtorCallInSize.toNat) := by
  change config.externalABI.encode? "hope" [.address flapper] =
    some ((vowCtorHopeCalldataMem (EVM.word flapper.val) mem).readWithPadding 224 36)
  rw [vowCtorHopeCalldataMem_read224_36 _ hmem]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatHopeSelector, selectorBytes,
    word_toBytesBE_toByteArray_eq_toByteArray]

private theorem evmAddress_accountAddress_tail (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow, AccountAddress.size] using a.isLt)

private theorem setAddressOffset0Word_low_address_tail (old : UInt256) (a : AccountAddress) :
    UInt256.land solcAddrMask (setAddressOffset0Word old (EVM.word a.val)) = EVM.word a.val := by
  apply u256_inj
  rw [u256_land_toNat, setAddressOffset0Word_toNat]
  · rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by native_decide]
    rw [nat_land_comm]
    rw [nat_land_mask_eq_mod]
    have ha : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size)
    rw [ha]
    have hmod : (a.val + old.toNat / 2 ^ 160 * 2 ^ 160) % 2 ^ 160 = a.val := by
      rw [Nat.mul_comm (old.toNat / 2 ^ 160) (2 ^ 160)]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size, EVM.addressModulus, EVM.twoPow] using a.isLt)
    rw [hmod]
    exact Nat.mod_eq_of_lt (lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size))
  · have ha : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide : AccountAddress.size < UInt256.size)
    rw [ha]
    exact a.isLt

private theorem accountAddress_of_word_val_tail (a : AccountAddress) :
    AccountAddress.ofUInt256 (EVM.word a.val) = a := by
  exact accountAddress_roundtrip a

private theorem storageStore_substate_tail (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_sigma0_tail (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_blocks_tail (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_genesisBlockHeader_tail (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem ctorExtCodeSize_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
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

private theorem ctorExtCodeSize_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem RDret.xiResultAcc {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem vowCtorHopeCallDepthLimit
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFinal σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {mem : ByteArray} {k C : ℕ}
    (vat flapper flopper : AccountAddress) (vatStored gasWord : UInt256)
    (rd216 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨216⟩
        [gasWord, UInt256.land solcAddrMask vatStored,
          vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
          vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
          vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
          EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
        mem (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C',
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
        (⟨0⟩ :: vowCtorCallEndPtr :: vowCtorHopeSelectorWord ::
          UInt256.land solcAddrMask vatStored :: EVM.word flopper.val :: EVM.word flapper.val ::
          EVM.word vat.val :: [])
        mem (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k' C' := by
  obtain ⟨k', C', rd217raw⟩ := RD.callDepthLimit rd216 (by ctor_tail_decode) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        vowCtorCallOutPtr.toNat vowCtorCallInSize.toNat)
        vowCtorCallOutPtr.toNat vowCtorCallOutSize.toNat) = UInt256.ofNat 9 := by
    unfold vowCtorCallOutPtr vowCtorCallInSize vowCtorCallOutSize
    native_decide
  have hmin : (min vowCtorCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold vowCtorCallOutSize
    rfl
  have rd217 : RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
      (⟨0⟩ :: vowCtorCallEndPtr :: vowCtorHopeSelectorWord ::
        UInt256.land solcAddrMask vatStored :: EVM.word flopper.val :: EVM.word flapper.val ::
        EVM.word vat.val :: [])
      (ByteArray.empty.write 0 mem vowCtorCallOutPtr.toNat
        (min vowCtorCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k' C' := by
    simpa [haw, vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallInSize,
      vowCtorCallEndPtr] using rd217raw
  rw [hmin, byteArray_write_len_zero] at rd217
  exact ⟨k', C', by simpa using rd217⟩

theorem vowCtorPrefixStateEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evm0e := initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I
    let evm0s := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
    let evm1e := vowCtorAfterWardsState evm0e
    let evm1s := vowCtorAfterWardsState evm0s
    let evm2e := vowCtorAfterVatState evm1e vat
    let evm2s := vowCtorAfterVatState evm1s vat
    let evm3e := vowCtorAfterFlapperState evm2e flapper
    let evm3s := vowCtorAfterFlapperState evm2s flapper
    let evm4e := vowCtorAfterFlopperState evm3e flopper
    let evm4s := vowCtorAfterFlopperState evm3s flopper
    EVMStateEquiv evm4e evm4s := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3e evm3s evm4e evm4s
  have h0 : EVMStateEquiv evm0e evm0s := by
    simpa [evm0e, evm0s] using EVMStateEquiv.initState (g := g) hAccounts
  have h1 : EVMStateEquiv evm1e evm1s := by
    have hslot : wardsSlot (.address I.source) = vowCtorCallerWardsSlot I :=
      vowCtorCallerWardsSlot_eq I
    simpa [evm1e, evm1s, evm0e, evm0s, vowCtorAfterWardsState, initState, hslot]
      using h0.storageStore_codeOwner (vowCtorCallerWardsSlot I)
        (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  have h2 : EVMStateEquiv evm2e evm2s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨1⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨1⟩)
            (EVM.word vat.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word vat.val))
        (h1.storageLoad_codeOwner ⟨1⟩)
    simpa [evm2e, evm2s, vowCtorAfterVatState] using h1.storageStore_codeOwner ⟨1⟩ hval
  have h3 : EVMStateEquiv evm3e evm3s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨2⟩)
            (EVM.word flapper.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word flapper.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word flapper.val))
        (h2.storageLoad_codeOwner ⟨2⟩)
    simpa [evm3e, evm3s, vowCtorAfterFlapperState] using
      h2.storageStore_codeOwner ⟨2⟩ hval
  have h4 : EVMStateEquiv evm4e evm4s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm3e evm3e.executionEnv.codeOwner ⟨3⟩)
            (EVM.word flopper.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm3s evm3s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word flopper.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word flopper.val))
        (h3.storageLoad_codeOwner ⟨3⟩)
    simpa [evm4e, evm4s, vowCtorAfterFlopperState] using
      h3.storageStore_codeOwner ⟨3⟩ hval
  exact h4

theorem vowCtorPrefixAccountMapEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat flapper flopper : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let σWards := sstoreAccountMap I.codeOwner σ_evm (vowCtorCallerWardsSlot I) ⟨1⟩
    let vatStored := setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val)
    let σVat := sstoreAccountMap I.codeOwner σWards ⟨1⟩ vatStored
    let flapperStored :=
      setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val)
    let σFlapper := sstoreAccountMap I.codeOwner σVat ⟨2⟩ flapperStored
    let flopperStored :=
      setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩) (EVM.word flopper.val)
    let σFlopper := sstoreAccountMap I.codeOwner σFlapper ⟨3⟩ flopperStored
    let evm0s :=
      initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := vowCtorAfterWardsState evm0s
    let evm2s := vowCtorAfterVatState evm1s vat
    let evm3s := vowCtorAfterFlapperState evm2s flapper
    let evm4s := vowCtorAfterFlopperState evm3s flopper
    accountMapEquiv σFlopper evm4s.accountMap := by
  intro σWards vatStored σVat flapperStored σFlapper flopperStored σFlopper
    evm0s evm1s evm2s evm3s evm4s
  let evm0e :=
    initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evm1e := vowCtorAfterWardsState evm0e
  let evm2e := vowCtorAfterVatState evm1e vat
  let evm3e := vowCtorAfterFlapperState evm2e flapper
  let evm4e := vowCtorAfterFlopperState evm3e flopper
  have hprefix := vowCtorPrefixStateEquiv (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    vat flapper flopper hAccounts
  have hslot : wardsSlot (.address I.source) = vowCtorCallerWardsSlot I :=
    vowCtorCallerWardsSlot_eq I
  have hmap : accountMapEquiv evm4e.accountMap evm4s.accountMap := by
    simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm0s, evm1s, evm2s, evm3s, evm4s]
      using hprefix.accountMap
  simpa [evm4e, evm3e, evm2e, evm1e, evm0e, σFlopper, flopperStored, σFlapper,
    flapperStored, σVat, vatStored, σWards, vowCtorAfterFlopperState,
    vowCtorAfterFlapperState, vowCtorAfterVatState, vowCtorAfterWardsState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord, hslot] using hmap

set_option maxHeartbeats 0 in
theorem vowConstructorCorrect :
    constructorEquivalence config vowCreationBytecode contract vowBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases vowCtorDeployment_shape hdeploy with ⟨vat, flapper, flopper, hargs, hdeployed⟩
  subst args
  have hcodeTail : I.code = vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper := by
    simpa [hdeployed] using hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · obtain ⟨_, _, rd67⟩ := vowCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat flapper flopper hcodeTail hwv
    obtain ⟨_, _, rd86⟩ := vowCtorWardsStoreReach vat flapper flopper hperm rd67
    let σWards := sstoreAccountMap I.codeOwner σ_evm (vowCtorCallerWardsSlot I) ⟨1⟩
    let vatStored := setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val)
    have rd86' := by
      simpa [σWards] using rd86
    obtain ⟨_, _, rd116⟩ := vowCtorVatStoreReach vat flapper flopper hperm rd86'
    let σVat := sstoreAccountMap I.codeOwner σWards ⟨1⟩ vatStored
    have rd116' := by
      simpa [σVat, vatStored, σWards] using rd116
    obtain ⟨_, _, rd131⟩ :=
      vowCtorFlapperStoreReach vat flapper flopper vatStored hperm rd116'
    let flapperStored := setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩)
      (EVM.word flapper.val)
    let σFlapper := sstoreAccountMap I.codeOwner σVat ⟨2⟩ flapperStored
    have rd131' := by
      simpa [σFlapper, flapperStored, σVat] using rd131
    obtain ⟨_, _, rd147⟩ :=
      vowCtorFlopperStoreReach vat flapper flopper vatStored hperm rd131'
    let flopperStored := setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩)
      (EVM.word flopper.val)
    let σFlopper := sstoreAccountMap I.codeOwner σFlapper ⟨3⟩ flopperStored
    have rd147' := by
      simpa [σFlopper, flopperStored, σFlapper] using rd147
    obtain ⟨_, _, rd201⟩ := vowCtorCallSetupReach vat flapper flopper vatStored rd147'
    let targetWord := UInt256.land solcAddrMask vatStored
    have htargetWord : targetWord = EVM.word vat.val := by
      simpa [targetWord, vatStored] using
        setAddressOffset0Word_low_address_tail (solcSlotWord σWards I ⟨1⟩) vat
    let evm0s :=
      initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := vowCtorAfterWardsState evm0s
    let evm2s := vowCtorAfterVatState evm1s vat
    let evm3s := vowCtorAfterFlapperState evm2s flapper
    let evm4s := vowCtorAfterFlopperState evm3s flopper
    have hAccounts4 : accountMapEquiv σFlopper evm4s.accountMap := by
      simpa [σWards, vatStored, σVat, flapperStored, σFlapper, flopperStored, σFlopper,
        evm0s, evm1s, evm2s, evm3s, evm4s] using
        vowCtorPrefixAccountMapEquiv (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat flapper flopper hAccounts
    by_cases hcodeSize : uniswapExtCodeSizeWord σFlopper targetWord = ⟨0⟩
    · have hrev := vowCtorHopeNoCode vat flapper flopper vatStored
        (by simpa [σFlopper, targetWord] using rd201)
        (by simpa [targetWord] using hcodeSize)
      rcases hrev.xiResult hcodeTail with hOOG | ⟨g', out, hRev⟩
      · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
      · have hcodeSizeSolm : uniswapExtCodeSizeWord evm4s.accountMap targetWord = ⟨0⟩ := by
          have hEq := uniswapExtCodeSizeWord_accountMapEquiv hAccounts4 targetWord
          exact hEq ▸ hcodeSize
        have haddr : vat = AccountAddress.ofUInt256 targetWord := by
          rw [htargetWord, accountAddress_of_word_val_tail]
        have hvatNoCode :
            (UInt256.ofNat ((evm4s.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat =
              0 := by
          simpa [evm4s, State.lookupAccount] using
            ctorExtCodeSize_zero_lookup_code_zero (σ := evm4s.accountMap)
              (target := targetWord) (addr := vat) haddr hcodeSizeSolm
        refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
          (vowCtorSolmExecReverts_noCode
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat flapper flopper hwv (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using hvatNoCode))
          ?_
        exact ctorResultEquiv.revert rfl rfl
    · have hcodeSizeSolmNe : uniswapExtCodeSizeWord evm4s.accountMap targetWord ≠ ⟨0⟩ := by
        intro hzero
        have hEq := uniswapExtCodeSizeWord_accountMapEquiv hAccounts4 targetWord
        exact hcodeSize (hEq.trans hzero)
      have haddr : vat = AccountAddress.ofUInt256 targetWord := by
        rw [htargetWord, accountAddress_of_word_val_tail]
      have hvatCode :
          0 < (UInt256.ofNat ((evm4s.lookupAccount vat).option 0
            (fun acc => acc.code.size))).toNat := by
        simpa [evm4s, State.lookupAccount] using
          ctorExtCodeSize_ne_zero_lookup_code_pos (σ := evm4s.accountMap)
            (target := targetWord) (addr := vat) haddr hcodeSizeSolmNe
      obtain ⟨gasWord, _, _, rd216⟩ := vowCtorHopeCallReady vat flapper flopper vatStored
        (by simpa [σFlopper, targetWord] using rd201) (by simpa [targetWord] using hcodeSize)
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨createdAccountsCall, σCall, z, out, Ain, callGas, _, _, hΘ, rd217, hout⟩ :=
          vowCtorHopePostCall vat flapper flopper vatStored gasWord rd216 hdepth
        let evm0e :=
          initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evm1e := vowCtorAfterWardsState evm0e
        let evm2e := vowCtorAfterVatState evm1e vat
        let evm3e := vowCtorAfterFlapperState evm2e flapper
        let evm4e := vowCtorAfterFlopperState evm3e flopper
        have hAccounts4e : accountMapEquiv evm4e.accountMap evm4s.accountMap := by
          simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm0s, evm1s, evm2s, evm3s, evm4s]
            using (vowCtorPrefixStateEquiv (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) vat flapper flopper hAccounts).accountMap
        have htgt : EVM.address vat = AccountAddress.ofUInt256 targetWord := by
          rw [htargetWord, accountAddress_of_word_val_tail, evmAddress_accountAddress_tail]
        have hslot : wardsSlot (.address I.source) = vowCtorCallerWardsSlot I :=
          vowCtorCallerWardsSlot_eq I
        obtain ⟨gTheta, ATheta, hTheta⟩ := hΘ
        have hdepthNe : evm4e.executionEnv.depth ≠ 1024 := by
          intro hEq
          have hEqI : I.depth = 1024 := by
            simpa [evm4e, evm3e, evm2e, evm1e, evm0e, vowCtorAfterFlopperState,
              vowCtorAfterFlapperState, vowCtorAfterVatState, vowCtorAfterWardsState,
              storageStore_executionEnv, initState] using hEq
          have hnot : ¬ I.depth.val < 1024 := by
            rw [hEqI]
            decide
          exact hnot hdepth
        let evmCallEvm : EVM.State :=
          { evm4e with
            accountMap := σCall
            substate := ATheta
            createdAccounts := createdAccountsCall }
        have hcallEvm :
            typedCallViaEVM config evm4e (EVM.address vat) "hope" 0 [.address flapper]
              (z, evmCallEvm, out) true := by
          refine callCoincides (A_in := Ain) (g'' := gTheta) (callGas := callGas)
            (callPerm := true) (targetWord := targetWord)
            (mem := vowCtorHopeCalldataMem (EVM.word flapper.val)
              (vowCtorWardsHashMem I vat flapper flopper))
            (inOff := vowCtorCallOutPtr) (inSize := vowCtorCallInSize)
            hdepthNe htgt ?_ ?_
          · simpa [vowCtorCallOutPtr, vowCtorCallInSize] using
              (vowCtorHopeEncode_eq flapper
                (vowCtorWardsHashMem_size I vat flapper flopper))
          · simpa [evm4e, evm3e, evm2e, evm1e, evm0e, σFlopper, targetWord,
              evmCallEvm, storageStore_accountMap, storageStore_executionEnv,
              storageStore_createdAccounts, storageStore_sigma0_tail, storageStore_blocks_tail,
              storageStore_genesisBlockHeader_tail, initState, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage, solcSlotWord, hslot, hperm] using hTheta
        obtain ⟨σSolmCall, ASolmCall, hcallSolm, hPostAccounts⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evm4s) hcallEvm hAccounts4e
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState, storageStore_sigma0_tail,
              initState])
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState, storageStore_createdAccounts,
              initState])
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState,
              storageStore_genesisBlockHeader_tail, initState])
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState, storageStore_blocks_tail,
              initState])
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState, storageStore_substate_tail,
              initState])
            (by simp [evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, vowCtorAfterFlopperState, vowCtorAfterFlapperState,
              vowCtorAfterVatState, vowCtorAfterWardsState, storageStore_executionEnv,
              initState])
        let evmHopeSolm : EVM.State :=
          { evm4s with
            accountMap := σSolmCall
            substate := ASolmCall
            createdAccounts := createdAccountsCall }
        cases z
        · have hrev := vowCtorHopeCallFailure vat flapper flopper (by simpa using rd217) hout
            (by simp only [List.length_cons, List.length_nil]; omega)
          rcases hrev.xiResult hcodeTail with hOOG | ⟨g', outRev, hRev⟩
          · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
          · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
              (vowCtorSolmExecReverts_callFailure
                (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmHope := evmHopeSolm) (out := out)
                vat flapper flopper hwv
                (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using hvatCode)
                (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evmHopeSolm] using hcallSolm))
              ?_
            exact ctorResultEquiv.revert rfl rfl
        · obtain ⟨_, _, rd246⟩ :=
            vowCtorHopeCallSuccessToReturnStart vat flapper flopper (by simpa using rd217) hperm
          have hret := vowCtorReturnRuntime vat flapper flopper rd246
          rcases RDret.xiResultAcc hcodeTail hret with hOOG | ⟨g', A', hSuccess⟩
          · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
          · have hcreated :
                createdAccountsCall = (vowCtorAfterLiveState evmHopeSolm).createdAccounts := by
              simp [evmHopeSolm, vowCtorAfterLiveState, storageStore_createdAccounts]
            have hAccountsLive :
                accountMapEquiv (sstoreAccountMap I.codeOwner σCall ⟨12⟩ ⟨1⟩)
                  (vowCtorAfterLiveState evmHopeSolm).accountMap := by
              have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPostAccounts
              simpa [evmHopeSolm, evm4s, evm3s, evm2s, evm1s, evm0s, vowCtorAfterLiveState,
                storageStore_accountMap, storageStore_executionEnv, vowCtorAfterFlopperState,
                vowCtorAfterFlapperState, vowCtorAfterVatState, vowCtorAfterWardsState, initState]
                using hbase
            refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hSuccess)
              (vowCtorSolmExecSuccess
                (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmHope := evmHopeSolm) (out := out) vat flapper flopper hwv
                (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using hvatCode)
                (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evmHopeSolm] using hcallSolm))
              ?_
            exact ctorResultEquiv.success rfl rfl hcreated hAccountsLive rfl
      · have hdepthEq : I.depth = 1024 := by
          apply Fin.ext
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          omega
        obtain ⟨_, _, rd217⟩ :=
          vowCtorHopeCallDepthLimit vat flapper flopper vatStored gasWord rd216 hdepthEq
        have hrev := vowCtorHopeCallFailure vat flapper flopper rd217
          (by native_decide)
          (by simp only [List.length_cons, List.length_nil]; omega)
        rcases hrev.xiResult hcodeTail with hOOG | ⟨g', outRev, hRev⟩
        · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
        · let A_hope := (evm4s.addAccessedAccount (EVM.address vat)).substate
          have hcallDepth :
              typedCallViaEVM config evm4s (EVM.address vat) "hope" 0 [.address flapper]
                (false, { evm4s with substate := A_hope }, ByteArray.empty) true := by
            simpa [A_hope, evm4s, evm3s, evm2s, evm1s, evm0s, storageStore_executionEnv,
              vowCtorAfterFlopperState, vowCtorAfterFlapperState, vowCtorAfterVatState,
              vowCtorAfterWardsState, initState] using
              (callNotMade_depthLimit (cfg := config) (evm := evm4s)
                (tgt := EVM.address vat) (name := "hope") (args := [.address flapper])
                (callPerm := true)
                (calldata :=
                  (vowCtorHopeCalldataMem (EVM.word flapper.val)
                    (vowCtorWardsHashMem I vat flapper flopper)).readWithPadding
                    vowCtorCallOutPtr.toNat vowCtorCallInSize.toNat)
                (vowCtorHopeEncode_eq flapper
                  (vowCtorWardsHashMem_size I vat flapper flopper))
                (by
                  simpa [evm4s, evm3s, evm2s, evm1s, evm0s, storageStore_executionEnv,
                    vowCtorAfterFlopperState, vowCtorAfterFlapperState, vowCtorAfterVatState,
                    vowCtorAfterWardsState, initState] using hdepthEq))
          refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
            (vowCtorSolmExecReverts_callFailure
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmHope := { evm4s with substate := A_hope }) (out := ByteArray.empty)
              vat flapper flopper hwv
              (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using hvatCode)
              (by simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using hcallDepth))
            ?_
          exact ctorResultEquiv.revert rfl rfl
  · have hrd := vowCtorNonpayableRDrev
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat flapper flopper hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (vowCtorSolmExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat flapper flopper hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Vow
