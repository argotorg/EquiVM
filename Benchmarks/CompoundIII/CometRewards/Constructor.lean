import Benchmarks.CompoundIII.CometRewards.Common
import Reasoning.Initcode
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-!
# Compound III CometRewards constructor correctness

The constructor has one `address governor_` argument.  The optimized creation code copies the
single appended ABI word, validates it as a canonical address, stores it into slot 0, then returns
the deployed runtime bytecode.
-/

theorem cometRewardsCreationBytecode_size : cometRewardsCreationBytecode.size = 4207 := by
  native_decide

theorem cometRewardsRuntimeBytecode_size : cometRewardsBytecode.size = 4063 := by
  native_decide

theorem cometRewardsCreation_runtime_window :
    cometRewardsCreationBytecode.extract 144 (144 + 4063) = cometRewardsBytecode := by
  native_decide

noncomputable def cometRewardsCtorArgTail (governor : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word governor)).toByteArray

noncomputable def cometRewardsCtorCode (governor : AccountAddress) : ByteArray :=
  cometRewardsCreationBytecode ++ cometRewardsCtorArgTail governor

theorem cometRewardsCtorArgTail_size (governor : AccountAddress) :
    (cometRewardsCtorArgTail governor).size = 32 := by
  unfold cometRewardsCtorArgTail
  rw [word_toBytesBE_toByteArray_size]

theorem cometRewardsCtorCode_size (governor : AccountAddress) :
    (cometRewardsCtorCode governor).size = 4239 := by
  rw [cometRewardsCtorCode, ByteArray.size_append, cometRewardsCreationBytecode_size,
    cometRewardsCtorArgTail_size]

theorem cometRewardsCreation_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 144) :
    decode (cometRewardsCreationBytecode ++ tail) pc =
      decode cometRewardsCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window cometRewardsCreationBytecode tail pc
    (by rw [cometRewardsCreationBytecode_size]; omega)
    (by rw [cometRewardsCreationBytecode_size]; norm_num)

macro "comet_rewards_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [cometRewardsCreation_decode_append _ _ (by decide)]
      | (unfold cometRewardsCtorCode; rw [cometRewardsCreation_decode_append _ _ (by decide)]);
     native_decide))

macro "comet_rewards_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold cometRewardsCtorCode; apply Reasoning.Theory.D_J_contains_append_left;
          native_decide)))

open Lean in
macro "comet_rewards_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc <- `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc <- `($(acc).jump (by comet_rewards_ctor_decode) $(args[0]!)
                            (by evm_ov))
        | `jumpiT  => acc <- `($(acc).jumpiT (by comet_rewards_ctor_decode) $(args[0]!)
                            $(args[1]!) (by evm_ov))
        | `jumpiNT => acc <- `($(acc).jumpiNT (by comet_rewards_ctor_decode) $(args[0]!)
                            (by evm_ov))
        | _        => acc <- `($(acc).$op $args* (by comet_rewards_ctor_decode)
                            (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem cometRewardsDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    config.selfDeployment cometRewardsCreationBytecode args = some deployedInitcode →
    ∃ governor : AccountAddress,
      args = [.address governor] ∧ deployedInitcode = cometRewardsCtorCode governor := by
  intro h
  cases args with
  | nil =>
      simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
              encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | address governor =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
              exact ⟨governor, rfl, h.symm⟩
          | int i =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bool b =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes bs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl, addr,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

noncomputable def cometRewardsCtorFreePtrMem : ByteArray :=
  (UInt256.toByteArray (⟨160⟩ : UInt256)).write 0 ByteArray.empty 64 32

noncomputable def cometRewardsCtorArgMem (governor : AccountAddress) : ByteArray :=
  (UInt256.toByteArray (EVM.word governor)).write 0 cometRewardsCtorFreePtrMem 128 32

noncomputable def cometRewardsCtorReturnMem (governor : AccountAddress) : ByteArray :=
  (cometRewardsCtorCode governor).write 144 (cometRewardsCtorArgMem governor) 160 4063

theorem write_from_gap_eq (src base : ByteArray) (srcAddr off len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hoff : base.size ≤ off) (hgap : off - base.size < USize.size) :
    src.write srcAddr base off len =
      base ++ ffi.ByteArray.zeroes (USize.ofNat (off - base.size)) ++
        src.extract srcAddr (srcAddr + len) := by
  have hpz : (ffi.ByteArray.zeroes (USize.ofNat (off - base.size))).data.size =
      off - base.size := by
    rw [show (ffi.ByteArray.zeroes (USize.ofNat (off - base.size))).data.size
          = (ffi.ByteArray.zeroes (USize.ofNat (off - base.size))).size from rfl,
        ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' hgap]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (⟨↑(off - base.size)⟩ : USize) = USize.ofNat (off - base.size) from rfl]
  have hDsz :
      (base.data ++ (ffi.ByteArray.zeroes (USize.ofNat (off - base.size))).data).size =
        off := by
    rw [Array.size_append, hpz]
    show base.size + (off - base.size) = off
    omega
  have hcopy : min len (src.size - srcAddr) = len := by omega
  rw [hcopy,
    show min base.size (off + len) - (off + len) = 0 from by omega,
    show (ffi.ByteArray.zeroes (⟨↑(0:ℕ)⟩ : USize)).data = (#[] : Array UInt8) from by
      rw [show (⟨↑(0:ℕ)⟩ : USize) = USize.ofNat 0 from rfl,
          zeroes_zero (n := USize.ofNat 0) (by rw [USize.toNat_ofNat_of_lt' (by omega)])]
      rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show srcAddr + (len + 0) = srcAddr + len from by omega]
  rw [show min (len + 0) (src.data.size - srcAddr) = len from by
    have : src.data.size = src.size := rfl
    omega]
  have htail :
      (base.data ++ (ffi.ByteArray.zeroes (USize.ofNat (off - base.size))).data).extract
          (off + len) = #[] := by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega
  rw [htail, Array.append_empty]

theorem cometRewardsCtorArg_extract (governor : AccountAddress) :
    (cometRewardsCtorCode governor).extract 4207 (4207 + 32) =
      (EVM.Word.toBytesBE (EVM.word governor)).toByteArray := by
  unfold cometRewardsCtorCode cometRewardsCtorArgTail
  exact extract_append_right' cometRewardsCreationBytecode
    (EVM.Word.toBytesBE (EVM.word governor)).toByteArray 4207 (4207 + 32)
    cometRewardsCreationBytecode_size.symm
    (by rw [cometRewardsCreationBytecode_size, word_toBytesBE_toByteArray_size])

theorem cometRewardsCtorArgMem_codecopy (governor : AccountAddress) :
    (cometRewardsCtorCode governor).write 4207 cometRewardsCtorFreePtrMem 128 32 =
      cometRewardsCtorArgMem governor := by
  have hcopy :
      (cometRewardsCtorCode governor).write 4207 cometRewardsCtorFreePtrMem 128 32 =
        cometRewardsCtorFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32) ++
          (cometRewardsCtorCode governor).extract 4207 (4207 + 32) := by
    have hfreeSize : cometRewardsCtorFreePtrMem.size = 96 := by
      unfold cometRewardsCtorFreePtrMem
      native_decide
    simpa [hfreeSize] using write_from_gap_eq (cometRewardsCtorCode governor) cometRewardsCtorFreePtrMem
      4207 128 32 (by decide) (by rw [cometRewardsCtorCode_size])
      (by rw [hfreeSize]; omega)
      (by rw [hfreeSize]; native_decide)
  unfold cometRewardsCtorArgMem
  rw [hcopy, cometRewardsCtorArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [toByteArray_write_eq (EVM.word governor) cometRewardsCtorFreePtrMem 128]
  · have hgap32 : 128 - cometRewardsCtorFreePtrMem.size = 32 := by
      unfold cometRewardsCtorFreePtrMem
      native_decide
    rw [hgap32]
  · unfold cometRewardsCtorFreePtrMem
    native_decide
  · unfold cometRewardsCtorFreePtrMem
    native_decide

theorem cometRewardsCtorFreePtrMem_size : cometRewardsCtorFreePtrMem.size = 96 := by
  unfold cometRewardsCtorFreePtrMem
  native_decide

theorem cometRewardsCtorArgMem_size (governor : AccountAddress) :
    (cometRewardsCtorArgMem governor).size = 160 := by
  unfold cometRewardsCtorArgMem
  rw [toByteArray_write_eq (EVM.word governor) cometRewardsCtorFreePtrMem 128]
  · rw [ByteArray.size_append, ByteArray.size_append, cometRewardsCtorFreePtrMem_size,
      ByteArray_zeroes_size, USize.toNat_ofNat_of_lt' (by native_decide), toByteArray_size]
  · rw [cometRewardsCtorFreePtrMem_size]
    omega
  · rw [cometRewardsCtorFreePtrMem_size]
    native_decide

theorem cometRewardsCtorArgMem_read128 (governor : AccountAddress) :
    (cometRewardsCtorArgMem governor).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word governor) := by
  unfold cometRewardsCtorArgMem
  exact toByteArray_write_read_back_of_gap (EVM.word governor) cometRewardsCtorFreePtrMem 128
    (by rw [cometRewardsCtorFreePtrMem_size]; native_decide)

theorem cometRewardsCtorArgMem_mload128 (governor : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (cometRewardsCtorArgMem governor).size
        ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((cometRewardsCtorArgMem governor).readWithPadding 128 32))) =
      EVM.word governor := by
  exact mloadWordValue_of_readWithPadding
    (mem := cometRewardsCtorArgMem governor) (aw := UInt256.ofNat 5)
    (off := ⟨128⟩) (v := EVM.word governor)
    (by
      have hsz := cometRewardsCtorArgMem_size governor
      have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
      rw [h128, hsz]
      omega)
    (by decide)
    (cometRewardsCtorArgMem_read128 governor)

theorem cometRewardsCtorArgMem_read64 (governor : AccountAddress) :
    (cometRewardsCtorArgMem governor).readWithPadding 64 32 =
      UInt256.toByteArray (⟨160⟩ : UInt256) := by
  unfold cometRewardsCtorArgMem
  rw [toByteArray_write_read_below_of_gap (EVM.word governor) cometRewardsCtorFreePtrMem
    128 64]
  · unfold cometRewardsCtorFreePtrMem
    exact toByteArray_write_read_back_of_gap (⟨160⟩ : UInt256) ByteArray.empty 64
      (by native_decide)
  · rw [cometRewardsCtorFreePtrMem_size]
  · omega
  · rw [cometRewardsCtorFreePtrMem_size]
    native_decide

theorem cometRewardsCtorArgMem_mload64 (governor : AccountAddress) :
    (if (⟨64⟩ : UInt256).toNat ≥ (cometRewardsCtorArgMem governor).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((cometRewardsCtorArgMem governor).readWithPadding 64 32))) =
      (⟨160⟩ : UInt256) := by
  exact mloadWordValue_of_readWithPadding
    (mem := cometRewardsCtorArgMem governor) (aw := UInt256.ofNat 5)
    (off := ⟨64⟩) (v := (⟨160⟩ : UInt256))
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        cometRewardsCtorArgMem_size]
      omega)
    (by decide)
    (cometRewardsCtorArgMem_read64 governor)

theorem cometRewardsCtorReturnMem_codecopy (governor : AccountAddress) :
    (cometRewardsCtorCode governor).write 144 (cometRewardsCtorArgMem governor) 160 4063 =
      cometRewardsCtorReturnMem governor := rfl

theorem cometRewardsCtorReturnMem_read (governor : AccountAddress) :
    (cometRewardsCtorReturnMem governor).readWithPadding 160 4063 = cometRewardsBytecode := by
  unfold cometRewardsCtorReturnMem
  rw [show (160 : Nat) = (cometRewardsCtorArgMem governor).size by
    rw [cometRewardsCtorArgMem_size]]
  rw [readWithPadding_eq_extract' _ (cometRewardsCtorArgMem governor).size 4063
      (by decide) (by decide) (by
      rw [write_end_size_from (cometRewardsCtorCode governor)
        (cometRewardsCtorArgMem governor) 144 4063 (by decide)
        (by rw [cometRewardsCtorCode_size]; omega)]
      )]
  rw [write_end_extract_tail_from (cometRewardsCtorCode governor)
    (cometRewardsCtorArgMem governor) 144 4063 (by decide)
    (by rw [cometRewardsCtorCode_size]; omega)]
  have hleft :
      (cometRewardsCtorCode governor).extract 144 (144 + 4063) =
        cometRewardsCreationBytecode.extract 144 (144 + 4063) := by
    have h := byteArray_extract_append_left cometRewardsCreationBytecode
      (cometRewardsCtorArgTail governor) 144 (144 + 4063)
      (by rw [cometRewardsCreationBytecode_size])
    simpa [cometRewardsCtorCode] using h
  rw [hleft, cometRewardsCreation_runtime_window]

theorem cometRewardsCtorGovernorWord_toNat (governor : AccountAddress) :
    (EVM.word governor).toNat = governor.val := by
  exact ulit_toNat' _ (lt_of_lt_of_le governor.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem cometRewardsCtorGovernor_ofNat (governor : AccountAddress) :
    AccountAddress.ofNat (EVM.word governor).toNat = governor := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [cometRewardsCtorGovernorWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt governor.isLt

theorem cometRewardsCtorGovernorWord_canonical (governor : AccountAddress) :
    (EVM.word governor).toNat < EVM.addressModulus := by
  rw [cometRewardsCtorGovernorWord_toNat]
  simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size]

def cometRewardsCtorStoredWord (σ : AccountMap) (I : ExecutionEnv)
    (governor : AccountAddress) : UInt256 :=
  setAddressOffset0Word
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
    (EVM.word governor)

def cometRewardsCtorPostState (evm : EVM.State) (governor : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (EVM.word governor))

theorem cometRewardsCtorOverflowCheck :
    UInt256.lor
        (UInt256.lt (⟨160⟩ : UInt256) (⟨128⟩ : UInt256))
        (UInt256.gt (⟨160⟩ : UInt256)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) =
      ⟨0⟩ := by
  native_decide

theorem cometRewardsCtorArgRoomCheck :
    UInt256.slt (UInt256.sub (⟨160⟩ : UInt256) ⟨128⟩) ⟨32⟩ = ⟨0⟩ := by
  native_decide

theorem cometRewardsCtorArgEnd :
    (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ := by
  native_decide

theorem cometRewardsCtorRoundedLen :
    UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) ((⟨32⟩ : UInt256) + ⟨31⟩) =
      (⟨32⟩ : UInt256) := by
  native_decide

theorem cometRewardsCtorNewFreePtr :
    (⟨128⟩ : UInt256) + UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
        ((⟨32⟩ : UInt256) + ⟨31⟩) =
      (⟨160⟩ : UInt256) := by
  native_decide

theorem cometRewardsCtorCleanAddressCheck (governor : AccountAddress) :
    UInt256.sub (EVM.word governor)
        (UInt256.land (EVM.word governor) solcAddrMask) = ⟨0⟩ := by
  have hclean := solcAddrMask_clean (cometRewardsCtorGovernorWord_canonical governor)
  rw [hclean]
  exact u256_sub_self _

theorem cometRewardsCtorMaskedGovernor (governor : AccountAddress) :
    UInt256.land (EVM.word governor) solcAddrMask = EVM.word governor := by
  exact solcAddrMask_clean (cometRewardsCtorGovernorWord_canonical governor)

theorem cometRewardsInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = cometRewardsCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (cometRewardsCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (cometRewardsCreationBytecode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd116 := comet_rewards_ctor_run rd0 with [
    push1 ⟨128⟩, callvalue, push2 ⟨116⟩,
    jumpiT hwv (by comet_rewards_ctor_jd),
    jumpdest]
  exact rd116.solcPush1Dup1Revert0
    (by comet_rewards_ctor_decode) (by comet_rewards_ctor_decode)
    (by comet_rewards_ctor_decode) (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (governor : AccountAddress)
    (hcode : I.code = cometRewardsCtorCode governor)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (cometRewardsCtorCode governor) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (cometRewardsCtorStoredWord σ I governor))
      cometRewardsBytecode := by
  have rd0 :
      RD (cometRewardsCtorCode governor) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  let oldGovernorSlot : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let governorStoreWord : UInt256 := cometRewardsCtorStoredWord σ I governor
  have hcodesize : UInt256.ofNat (cometRewardsCtorCode governor).size = (⟨4239⟩ : UInt256) := by
    apply u256_inj
    rw [cometRewardsCtorCode_size]
    native_decide
  have harglen :
      UInt256.sub (UInt256.ofNat (cometRewardsCtorCode governor).size) ⟨4207⟩ =
        (⟨32⟩ : UInt256) := by
    rw [hcodesize]
    native_decide
  have hrounded :
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
          (UInt256.add
            (UInt256.sub (UInt256.ofNat (cometRewardsCtorCode governor).size) ⟨4207⟩)
            ⟨31⟩) =
        (⟨32⟩ : UInt256) := by
    rw [harglen]
    native_decide
  have hnewFree :
      UInt256.add ⟨128⟩
        (UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
          (UInt256.add
            (UInt256.sub (UInt256.ofNat (cometRewardsCtorCode governor).size) ⟨4207⟩)
            ⟨31⟩)) =
        (⟨160⟩ : UInt256) := by
    rw [hrounded]
    native_decide
  have rdBeforeCopy := comet_rewards_ctor_run rd0 with [
    push1 ⟨128⟩, callvalue, push2 ⟨116⟩,
    jumpiNT hwv,
    push1 ⟨31⟩, push2 ⟨4207⟩, codesize, dup2, swap1, sub, swap2,
    dup3, add, push1 ⟨31⟩, not, and, dup4, add, swap2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup4, gt,
    dup5, dup5, lt, lor]
  rw [harglen] at rdBeforeCopy
  rw [cometRewardsCtorNewFreePtr, cometRewardsCtorOverflowCheck] at rdBeforeCopy
  have rdBeforeCodecopy := comet_rewards_ctor_run rdBeforeCopy with [
    push2 ⟨121⟩, jumpiNT (by decide),
    dup1, dup5, swap3, push1 ⟨32⟩, swap5, push1 ⟨64⟩,
    raw mstore 9 cometRewardsCtorFreePtrMem (UInt256.ofNat 3)
      (by comet_rewards_ctor_decode)
      mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold cometRewardsCtorFreePtrMem
        rfl)
      (by decide) (by evm_ov),
    dup4]
  have rdAfterCodecopy := comet_rewards_ctor_run rdBeforeCodecopy with [
    raw codecopy 6 (cometRewardsCtorArgMem governor) (UInt256.ofNat 5)
      (by comet_rewards_ctor_decode)
      mem_cost
      (cometRewardsCtorArgMem_codecopy governor)
      (by decide) (by evm_ov),
    dup2, add, sub, slt]
  rw [cometRewardsCtorArgEnd, cometRewardsCtorArgRoomCheck] at rdAfterCodecopy
  have rdBeforeMload := comet_rewards_ctor_run rdAfterCodecopy with [
    push2 ⟨116⟩, jumpiNT (by decide)]
  have rdBeforeClean := comet_rewards_ctor_run rdBeforeMload with [
    raw mload 0 (EVM.word governor) (UInt256.ofNat 5)
      (by comet_rewards_ctor_decode)
      mem_cost
      (cometRewardsCtorArgMem_mload128 governor)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, swap1,
    dup2, swap1, sub]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    cometRewardsCtorCleanAddressCheck governor] at rdBeforeClean
  rw [cometRewardsCtorMaskedGovernor governor] at rdBeforeClean
  have rdBeforeSload := comet_rewards_ctor_run rdBeforeClean with [
    push2 ⟨116⟩, jumpiNT (by decide), push1 ⟨0⟩, dup1]
  obtain ⟨_, _, rdAfterSload0⟩ := rdBeforeSload.sload
    (by comet_rewards_ctor_decode) (by evm_ov)
  obtain ⟨_, _, rdAfterSload⟩ :
      ∃ k C, RD (cometRewardsCtorCode governor) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨86⟩
        [oldGovernorSlot, ⟨0⟩, EVM.word governor]
        (cometRewardsCtorArgMem governor) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σ) k C := by
    exact ⟨_, _, by simpa [oldGovernorSlot] using rdAfterSload0⟩
  have rdBeforeStore := comet_rewards_ctor_run rdAfterSload with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    swap2, swap1, swap2, lor, swap1]
  have hpacked :
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) oldGovernorSlot)
          (EVM.word governor) =
        governorStoreWord := by
    unfold governorStoreWord cometRewardsCtorStoredWord oldGovernorSlot setAddressOffset0Word
    rw [u256_land_comm (UInt256.lnot solcAddrMask) _, cometRewardsCtorMaskedGovernor governor]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rdBeforeStore
  rw [hpacked] at rdBeforeStore
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm
    (by comet_rewards_ctor_decode) (by evm_ov)
  have rdBeforeReturn := comet_rewards_ctor_run rdAfterStore with [
    push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5)
      (by comet_rewards_ctor_decode)
      mem_cost
      (cometRewardsCtorArgMem_mload64 governor)
      (by decide) (by evm_ov),
    push2 ⟨4063⟩, swap1, dup2, push2 ⟨144⟩, dup3,
    raw codecopy 415 (cometRewardsCtorReturnMem governor) (UInt256.ofNat 132)
      (by comet_rewards_ctor_decode)
      mem_cost
      (cometRewardsCtorReturnMem_codecopy governor)
      (by decide) (by evm_ov)]
  exact rdBeforeReturn.ret 0 cometRewardsBytecode
    (by comet_rewards_ctor_decode)
    mem_cost
    (cometRewardsCtorReturnMem_read governor)
    (by evm_ov)

def cometRewardsCtorLocals (governor : AccountAddress) : Store :=
  Std.HashMap.ofList
    (List.zip (contract.ctor.params.map Param.name) [.address governor])

theorem cometRewardsCtorLocals_get_governorParam (governor : AccountAddress) :
    (cometRewardsCtorLocals governor).get? "governor_" = some (.address governor) := by
  unfold cometRewardsCtorLocals
  simp [contract, constructorDecl]

theorem cometRewardsCtorLocals_get_governorStorage (governor : AccountAddress) :
    (cometRewardsCtorLocals governor).get? "governor" = none := by
  unfold cometRewardsCtorLocals
  simp [contract, constructorDecl]

theorem cometRewardsCtorAssignGovernor (evm : EVM.State) (governor : AccountAddress) :
    assignStorageRef? config
      { contract := contract, locals := cometRewardsCtorLocals governor }
      evm .storage governorRef (.address governor) =
        .ok ({ contract := contract, locals := cometRewardsCtorLocals governor },
          cometRewardsCtorPostState evm governor) := by
  have her : evalStorageRef config
      { contract := contract, locals := cometRewardsCtorLocals governor } evm governorRef =
        .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (fieldLoc ⟨0⟩ 0 20 (by decide) .address) (.address governor) =
        some (cometRewardsCtorPostState evm governor) := by
    have h := storageLocStore_address_offset0 evm ⟨0⟩ (EVM.word governor)
      (cometRewardsCtorGovernorWord_canonical governor)
    rw [cometRewardsCtorGovernor_ofNat] at h
    simpa [cometRewardsCtorPostState, fieldLoc, loc, addressOffset0Loc] using h
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := cometRewardsCtorLocals governor })
    (evm := evm) (evm' := cometRewardsCtorPostState evm governor)
    (slot := governorRef) (er := { base := "governor", steps := [] })
    (ty := .elem .address) (loc := fieldLoc ⟨0⟩ 0 20 (by decide) .address)
    (value := .address governor)
    (cometRewardsCtorLocals_get_governorStorage governor)
    her hty (by rfl) (by trivial) hstore

theorem cometRewardsCtorBodyReturns (evm : EVM.State) (governor : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (cometRewardsCtorLocals governor) contract.ctor.body
      (.returned { contract := contract, locals := cometRewardsCtorLocals governor }
        (cometRewardsCtorPostState evm governor) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [contract, constructorDecl, nonpayable] using
    ((ABlock.start.requireStep (evalCallvalueEq_true (cfg := config)
      (solm := { contract := contract, locals := cometRewardsCtorLocals governor })
      (evm := evm) hwv)).run
      (ExecBlock.consNormal
        (ExecStmt.assign
          (by
            show evalExpr? config
              { contract := contract, locals := cometRewardsCtorLocals governor } evm
                (.var "governor_") = .ok (.address governor)
            simp only [evalExpr?, cometRewardsCtorLocals_get_governorParam,
              EvalResult.ofOption])
          (cometRewardsCtorAssignGovernor evm governor))
        ExecBlock.nil))

theorem cometRewardsSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (governor : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address governor] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := contract, locals := cometRewardsCtorLocals governor }
        (cometRewardsCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          governor)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := cometRewardsCtorLocals governor)
    ?_ rfl ?_ ?_
  · rfl
  · simp [cometRewardsCtorLocals, contract, constructorDecl]
  · exact cometRewardsCtorBodyReturns
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
      governor (by simpa [initState] using hwv)

theorem cometRewardsSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (governor : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address governor]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := cometRewardsCtorLocals governor)
    ?_ rfl ?_ ?_
  · rfl
  · simp [cometRewardsCtorLocals, contract, constructorDecl]
  · exact bodyReverts_nonPayable (cfg := config) (contract := contract)
      (locals := cometRewardsCtorLocals governor) hwv

/-- The optimized creation bytecode refines the Solm constructor specification. -/
theorem cometRewardsConstructorCorrect :
    constructorEquivalence config cometRewardsCreationBytecode contract cometRewardsBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hσ
  rcases cometRewardsDeployment_shape hdeploy with ⟨governor, hargs, hdeployed⟩
  subst args
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hcodeCtor : I.code = cometRewardsCtorCode governor := by
      rw [hcode, hdeployed]
    have hrd := cometRewardsInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) governor hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
            (cometRewardsCtorStoredWord σ_evm I governor) := by
        exact congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (cometRewardsSolmCtorExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          governor hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [cometRewardsCtorPostState, initState, storageStore_createdAccounts]
      · have hOldSlot :
            (σ_evm.find? I.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩)) =
              (σ_solm.find? I.codeOwner |>.option ⟨0⟩
                (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩)) := by
          exact accountMapEquiv_storage_findD hσ I.codeOwner ⟨0⟩ ⟨0⟩
        have hstored :
            cometRewardsCtorStoredWord σ_evm I governor =
              cometRewardsCtorStoredWord σ_solm I governor := by
          simp [cometRewardsCtorStoredWord, hOldSlot]
        simp [cometRewardsCtorPostState, initState, storageStore_accountMap,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
        change accountMapEquiv
          (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
            (cometRewardsCtorStoredWord σ_evm I governor))
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
            (cometRewardsCtorStoredWord σ_solm I governor))
        rw [← hstored]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
          (cometRewardsCtorStoredWord σ_evm I governor) hσ
  · let tail := cometRewardsCtorArgTail governor
    have hcodeTail : I.code = cometRewardsCreationBytecode ++ tail := by
      rw [hcode, hdeployed]
      rfl
    have hrd := cometRewardsInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (cometRewardsSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          governor hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.CompoundIII.CometRewards
