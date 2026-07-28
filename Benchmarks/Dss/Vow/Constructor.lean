import Benchmarks.Dss.Vow.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Reasoning.Memory
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vow constructor correctness

Constructor-specific ABI and initcode facts for the three-address `Vow` deployment path.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-- ABI-encoded constructor arguments appended to `vowCreationBytecode`. -/
def vowCtorArgsTail (vat flapper flopper : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val) ++
    EVM.Word.toBytesBE (EVM.word flapper.val) ++
    EVM.Word.toBytesBE (EVM.word flopper.val)).toByteArray

private theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

private theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [byteArray_toList_eq]
  simp

private theorem byteArray_write_from_ge_eq (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) (hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  have hsrcNonempty : ¬ srcAddr ≥ src.size := by omega
  have hcopy : min len (src.size - srcAddr) = len := by
    rw [Nat.min_eq_left]
    omega
  have hcopyData : min len (src.data.size - srcAddr) = len := by
    rw [show src.data.size = src.size from rfl]
    exact hcopy
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by
    have hle : min base.size (destAddr + len) ≤ destAddr + len := Nat.min_le_right _ _
    omega
  have hDsz :
      (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).size =
        destAddr := by
    rw [Array.size_append]
    have hz :
        (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          destAddr - base.size := by
      rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl,
        ByteArray_zeroes_size]
    rw [hz]
    change base.size + (destAddr - base.size) = destAddr
    omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg hsrcNonempty]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  change (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract 0
          destAddr ++
        (src.data ++
            (ffi.ByteArray.zeroes
              (min base.size (destAddr + len) -
                (destAddr + min len (src.size - srcAddr)))).data).extract
          srcAddr
          (srcAddr +
            (min len (src.size - srcAddr) +
              (min base.size (destAddr + len) -
                (destAddr + min len (src.size - srcAddr))))) ++
        (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr +
            min
              (min len (src.size - srcAddr) +
                (min base.size (destAddr + len) -
                  (destAddr + min len (src.size - srcAddr))))
              ((src.data ++
                    (ffi.ByteArray.zeroes
                      (min base.size (destAddr + len) -
                        (destAddr + min len (src.size - srcAddr)))).data).size -
                srcAddr)) =
      base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data ++
        (src.extract srcAddr (srcAddr + len)).data
  rw [hcopy, htail]
  rw [show (ffi.ByteArray.zeroes 0).data =
      (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show src.data.extract srcAddr (srcAddr + len) =
      (src.extract srcAddr (srcAddr + len)).data from by rw [ByteArray.data_extract]]
  rw [hcopyData]
  rw [show
      (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
        (destAddr + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp only [Array.append_empty]

theorem vowCtorArgsTail_encode (vat flapper flopper : AccountAddress) :
    ABI.encodeABIValues? [addr, addr, addr]
      [.address vat, .address flapper, .address flopper] =
      some (vowCtorArgsTail vat flapper flopper).toList := by
  simp [vowCtorArgsTail, addr, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
    ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, list_toByteArray_toList,
    byteArray_append_toList]

theorem vowCtorDeployment_eq
    (vat flapper flopper : AccountAddress) :
    config.selfDeployment vowCreationBytecode
      [.address vat, .address flapper, .address flopper] =
      some (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment]
  simp [vowCtorArgsTail, addr, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
    ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType]

theorem vowCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment vowCreationBytecode args = some deployedInitcode) :
    ∃ vat flapper flopper : AccountAddress,
      args = [.address vat, .address flapper, .address flopper] ∧
      deployedInitcode = vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
  | cons a rest =>
      cases rest with
      | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
          | cons c rest3 =>
              cases rest3 with
              | cons _ _ =>
                  simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
              | nil =>
                  cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr] at hdeploy
                  rename_i vat
                  cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr] at hdeploy
                  rename_i flapper
                  cases c <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr] at hdeploy
                  rename_i flopper
                  refine ⟨vat, flapper, flopper, rfl, ?_⟩
                  simpa [vowCtorArgsTail, ABI.abiTupleHeadSize?,
                    ABI.staticABIEncodedSize?, ABI.isDynamicABIType] using hdeploy.symm

macro "ctor_decode" : tactic =>
  `(tactic|
    (rw [Reasoning.Theory.decode_append_left_window
      vowCreationBytecode _ _ (by native_decide) (by native_decide)]
     native_decide))

macro "ctor_jump_dest" : tactic =>
  `(tactic|
    (exact D_J_contains_append_left vowCreationBytecode _ _ (by jump_dest)))

theorem vowCtorNonpayableRDrev
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress)
    (hcode : I.code = vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  have rd8 :
      RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := code) hcode
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
  have rd12 :
      RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨12⟩
        [I.weiValue] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, σ) (6 + 2) (26 + 13) := by
    exact (rd8
      |>.push2 ⟨16⟩ (by ctor_decode) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiNT (by ctor_decode) (isZero_eq_zero_of_ne hwv)
        (by simp only [List.length_cons, List.length_nil]; omega))
  simpa [code, show ((⟨8⟩ : UInt256) + UInt256.ofNat 3 + ⟨1⟩) = ⟨12⟩ from by native_decide]
    using
      RD.solcPush1Dup1Revert0 (code := code) (ee := I) (g := g)
        (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) rd12
        (by ctor_decode) (by ctor_decode) (by ctor_decode)
        (by simp only [List.length_cons, List.length_nil]; omega)

def vowCtorCopiedMem (vat flapper flopper : AccountAddress) : ByteArray :=
  (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper).write 5410 solcFreePtrMem 128 96

def vowCtorArgsMem (vat flapper flopper : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨224⟩).write 0 (vowCtorCopiedMem vat flapper flopper) 64 32

theorem vowCtorArgsTail_size (vat flapper flopper : AccountAddress) :
    (vowCtorArgsTail vat flapper flopper).size = 96 := by
  rw [vowCtorArgsTail, list_toByteArray_size]
  simp only [List.length_append]
  have h1 : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have h2 : (EVM.Word.toBytesBE (EVM.word flapper.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word flapper.val)
  have h3 : (EVM.Word.toBytesBE (EVM.word flopper.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word flopper.val)
  omega

private theorem vowCreationBytecode_size : vowCreationBytecode.size = 5410 := by
  native_decide

theorem vowCtorCopiedMem_eq (vat flapper flopper : AccountAddress) :
    vowCtorCopiedMem vat flapper flopper =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        vowCtorArgsTail vat flapper flopper := by
  rw [vowCtorCopiedMem]
  rw [byteArray_write_from_ge_eq]
  · rw [extract_append_right' vowCreationBytecode (vowCtorArgsTail vat flapper flopper)
      5410 (5410 + 96)]
    · rw [solcFreePtrMem_size]
    · native_decide
    · rw [vowCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, vowCtorArgsTail_size]
    native_decide
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

private theorem vowCtorArgsMem_base_size (vat flapper flopper : AccountAddress) :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      vowCtorArgsTail vat flapper flopper).size = 224 := by
  rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size _ (by norm_num), vowCtorArgsTail_size]

theorem vowCtorArgsMem_size (vat flapper flopper : AccountAddress) :
    (vowCtorArgsMem vat flapper flopper).size = 224 := by
  rw [vowCtorArgsMem, vowCtorCopiedMem_eq]
  rw [toByteArray_write32_size_of_le
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      vowCtorArgsTail vat flapper flopper)
    (word := (⟨224⟩ : UInt256)) (off := 64) (baseSize := 224) (finalSize := 224)]
  · exact vowCtorArgsMem_base_size vat flapper flopper
  · rw [vowCtorArgsMem_base_size]
    omega
  · native_decide

private theorem vowCtorArgsTail_extract_first (vat flapper flopper : AccountAddress) :
    (vowCtorArgsTail vat flapper flopper).extract 0 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  simp [vowCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem vowCtorArgsTail_extract_second (vat flapper flopper : AccountAddress) :
    (vowCtorArgsTail vat flapper flopper).extract 32 64 =
      UInt256.toByteArray (EVM.word flapper.val) := by
  simp [vowCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem vowCtorArgsTail_extract_third (vat flapper flopper : AccountAddress) :
    (vowCtorArgsTail vat flapper flopper).extract 64 96 =
      UInt256.toByteArray (EVM.word flopper.val) := by
  simp [vowCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem vowCtorArgsMem_read_word (vat flapper flopper : AccountAddress)
    (start : Nat)
    (hstart : start + 32 ≤ 96)
    (hextract :
      (vowCtorArgsTail vat flapper flopper).extract start (start + 32) =
        UInt256.toByteArray
          (if start = 0 then EVM.word vat.val else
           if start = 32 then EVM.word flapper.val else EVM.word flopper.val)) :
    (vowCtorArgsMem vat flapper flopper).readWithPadding (128 + start) 32 =
      UInt256.toByteArray
          (if start = 0 then EVM.word vat.val else
           if start = 32 then EVM.word flapper.val else EVM.word flopper.val) := by
  rw [vowCtorArgsMem, vowCtorCopiedMem_eq]
  rw [write32_read_above_len
    (src := UInt256.toByteArray (⟨224⟩ : UInt256))
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      vowCtorArgsTail vat flapper flopper)
    (dest := 64) (read := 128 + start) (len := 32)]
  · have hprefix :
        (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
      rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
    rw [readWithPadding_eq_extract'
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        vowCtorArgsTail vat flapper flopper)
      (128 + start) 32 (by norm_num) (by norm_num)
      (by rw [vowCtorArgsMem_base_size]; omega)]
    rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
      (vowCtorArgsTail vat flapper flopper) (128 + start) (128 + start + 32)
      (by rw [hprefix]; omega), hprefix]
    rw [show 128 + start - 128 = start by omega,
      show 128 + start + 32 - 128 = start + 32 by omega]
    exact hextract
  · rw [toByteArray_size]
  · rw [vowCtorArgsMem_base_size]
    omega
  · omega
  · rw [vowCtorArgsMem_base_size]
    omega
  · norm_num
  · norm_num

theorem vowCtorArgsMem_mload_vat (vat flapper flopper : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (vowCtorArgsMem vat flapper flopper).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((vowCtorArgsMem vat flapper flopper).readWithPadding 128 32))) =
      EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [vowCtorArgsMem_size]
    decide
  · decide
  · simpa using
      vowCtorArgsMem_read_word vat flapper flopper 0 (by norm_num)
        (by simpa using vowCtorArgsTail_extract_first vat flapper flopper)

theorem vowCtorArgsMem_mload_flapper (vat flapper flopper : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (vowCtorArgsMem vat flapper flopper).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((vowCtorArgsMem vat flapper flopper).readWithPadding 160 32))) =
      EVM.word flapper.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [vowCtorArgsMem_size]
    decide
  · decide
  · simpa using
      vowCtorArgsMem_read_word vat flapper flopper 32 (by norm_num)
        (by simpa using vowCtorArgsTail_extract_second vat flapper flopper)

theorem vowCtorArgsMem_mload_flopper (vat flapper flopper : AccountAddress) :
    (if (⟨192⟩ : UInt256).toNat ≥ (vowCtorArgsMem vat flapper flopper).size ∨
        (⟨192⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((vowCtorArgsMem vat flapper flopper).readWithPadding 192 32))) =
      EVM.word flopper.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [vowCtorArgsMem_size]
    decide
  · decide
  · simpa using
      vowCtorArgsMem_read_word vat flapper flopper 64 (by norm_num)
        (by simpa using vowCtorArgsTail_extract_third vat flapper flopper)

set_option maxHeartbeats 1000000 in
private theorem vowCtorArgsSizeReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd18 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨26⟩
      [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨18⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k C
    at rd18
  have rd26 := evm_run rd18 with [
    raw push1 ⟨64⟩ (by ctor_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by ctor_decode) mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    raw push2 ⟨5410⟩ (by ctor_decode) (by evm_ov),
    raw codesize (by ctor_decode) (by evm_ov),
    raw sub (by ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [code, ByteArray.size_append, vowCreationBytecode_size, vowCtorArgsTail_size]
      using rd26⟩

set_option maxHeartbeats 1000000 in
private theorem vowCtorArgsCodecopyReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd26 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨26⟩
        [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨32⟩
      [⟨96⟩, ⟨128⟩] (vowCtorCopiedMem vat flapper flopper) (UInt256.ofNat 7)
      ByteArray.empty (createdAccounts, σ) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨26⟩ [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
    (createdAccounts, σ) k C at rd26
  have hcopy : code.write 5410 solcFreePtrMem 128 96 = vowCtorCopiedMem vat flapper flopper := by
    rfl
  have rd32 := evm_run rd26 with [
    raw dup1 (by ctor_decode) (by evm_ov),
    raw push2 ⟨5410⟩ (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 96)) -
        Cₘ (UInt256.ofNat 3))
      (vowCtorCopiedMem vat flapper flopper) (UInt256.ofNat 7)
      (by ctor_decode) mem_cost hcopy (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd32⟩

set_option maxHeartbeats 1000000 in
private theorem vowCtorArgsFreePtrReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd32 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨32⟩
        [⟨96⟩, ⟨128⟩] (vowCtorCopiedMem vat flapper flopper) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨38⟩
      [⟨96⟩, ⟨128⟩] (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
      ByteArray.empty (createdAccounts, σ) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨32⟩ [⟨96⟩, ⟨128⟩] (vowCtorCopiedMem vat flapper flopper) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σ) k C at rd32
  have hmstore :
      (UInt256.toByteArray ⟨224⟩).write 0 (vowCtorCopiedMem vat flapper flopper) 64 32 =
        vowCtorArgsMem vat flapper flopper := by
    rfl
  have rd38 := evm_run rd32 with [
    raw dup2 (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by ctor_decode) (by evm_ov),
    raw mstore 0 (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
      (by ctor_decode) mem_cost hmstore (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd38⟩

set_option maxHeartbeats 1000000 in
private theorem vowCtorArgsGuardReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd38 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨38⟩
        [⟨96⟩, ⟨128⟩] (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨46⟩
      [⟨51⟩, ⟨1⟩, ⟨96⟩, ⟨128⟩]
      (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σ) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨38⟩ [⟨96⟩, ⟨128⟩] (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σ) k C at rd38
  have rd47 := evm_run rd38 with [
    raw push1 ⟨96⟩ (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw lt (by ctor_decode) (by evm_ov),
    raw iszero (by ctor_decode) (by evm_ov),
    raw push2 ⟨51⟩ (by ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [code,
      show ((⟨38⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 3) = ⟨46⟩ from by native_decide,
      show (UInt256.lt (⟨96⟩ : UInt256) ⟨96⟩).isZero = ⟨1⟩ from by native_decide]
      using rd47⟩

private theorem vowCtorArgsCopyReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd18 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨46⟩
      [⟨51⟩, ⟨1⟩, ⟨96⟩, ⟨128⟩]
      (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σ) k' C' := by
  obtain ⟨_, _, rd26⟩ := vowCtorArgsSizeReach vat flapper flopper rd18
  obtain ⟨_, _, rd32⟩ := vowCtorArgsCodecopyReach vat flapper flopper rd26
  obtain ⟨_, _, rd38⟩ := vowCtorArgsFreePtrReach vat flapper flopper rd32
  exact vowCtorArgsGuardReach vat flapper flopper rd38

set_option maxHeartbeats 1000000 in
private theorem vowCtorArgsLoadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (rd51 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨51⟩
        [⟨96⟩, ⟨128⟩] (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨67⟩
      [EVM.word flopper.val, EVM.word flapper.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σ) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨51⟩ [⟨96⟩, ⟨128⟩] (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σ) k C at rd51
  have hmloadVat := vowCtorArgsMem_mload_vat vat flapper flopper
  have hmloadFlapper := vowCtorArgsMem_mload_flapper vat flapper flopper
  have hmloadFlopper := vowCtorArgsMem_mload_flopper vat flapper flopper
  have rd67 := evm_run rd51 with [
    raw jumpdest (by ctor_decode) (by evm_ov),
    raw pop (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 7) (by ctor_decode) mem_cost hmloadVat
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw mload 0 (EVM.word flapper.val) (UInt256.ofNat 7) (by ctor_decode) mem_cost
      hmloadFlapper (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw dup5 (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw mload 0 (EVM.word flopper.val) (UInt256.ofNat 7) (by ctor_decode) mem_cost
      hmloadFlopper (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd67⟩

set_option maxHeartbeats 1000000 in
theorem vowCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress)
    (hcode : I.code = vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨67⟩
      [EVM.word flopper.val, EVM.word flapper.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σ) k C := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  have rd8 :
      RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := code) hcode
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by ctor_decode)
  obtain ⟨k18, C18, rd18⟩ :=
    solcGuardCallvalueZero (code := code) (ctgt := ⟨16⟩) (wC := 2) (opC := .PUSH2)
      rd8 hwv (by decide)
    (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_jump_dest)
  have rd18' :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [code, show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by native_decide]
      using rd18
  obtain ⟨_, _, rd47⟩ := vowCtorArgsCopyReach vat flapper flopper rd18'
  have rd51 := rd47.jumpiT (by ctor_decode) (by decide) (by ctor_jump_dest) (by evm_ov)
  obtain ⟨_, _, rd67⟩ := vowCtorArgsLoadReach vat flapper flopper rd51
  exact ⟨_, _, rd67⟩

abbrev vowCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def vowCtorWardsHashMem (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (vowCtorArgsMem vat flapper flopper)

theorem vowCtorWardsHashMem_size (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    (vowCtorWardsHashMem I vat flapper flopper).size = 224 := by
  have hfirstSize :
      ((UInt256.toByteArray (solcSourceWord I)).write 0
          (vowCtorArgsMem vat flapper flopper) 0 32).size = 224 := by
    exact toByteArray_write32_size_of_le
      (base := vowCtorArgsMem vat flapper flopper) (word := solcSourceWord I)
      (off := 0) (baseSize := 224) (finalSize := 224)
      (vowCtorArgsMem_size vat flapper flopper)
      (by rw [vowCtorArgsMem_size]; omega) (by omega)
  unfold vowCtorWardsHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  exact toByteArray_write32_size_of_le
      (base := (UInt256.toByteArray (solcSourceWord I)).write 0
        (vowCtorArgsMem vat flapper flopper) 0 32)
      (word := (⟨0⟩ : UInt256)) (off := 32) (baseSize := 224) (finalSize := 224)
      hfirstSize (by rw [hfirstSize]; omega) (by omega)

theorem vowCtorWardsHashMem_read0 (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    (vowCtorWardsHashMem I vat flapper flopper).readWithPadding 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold vowCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])]
  · unfold wordAt0Mem
    rw [toByteArray_write32_read_back
      (base := vowCtorArgsMem vat flapper flopper) (word := solcSourceWord I)
      (off := 0) (Nat.zero_le _)]
  · unfold wordAt0Mem
    rw [toByteArray_write32_size_of_le
        (base := vowCtorArgsMem vat flapper flopper) (word := solcSourceWord I)
        (off := 0) (baseSize := 224) (finalSize := 224)]
    · omega
    · exact vowCtorArgsMem_size vat flapper flopper
    · rw [vowCtorArgsMem_size]
      omega
    · omega
  · omega

theorem vowCtorWardsHashMem_read32 (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    (vowCtorWardsHashMem I vat flapper flopper).readWithPadding 32 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold vowCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [toByteArray_write32_read_back]
  unfold wordAt0Mem
  rw [toByteArray_write32_size_of_le
      (base := vowCtorArgsMem vat flapper flopper) (word := solcSourceWord I)
      (off := 0) (baseSize := 224) (finalSize := 224)]
  · omega
  · exact vowCtorArgsMem_size vat flapper flopper
  · rw [vowCtorArgsMem_size]
    omega
  · omega

theorem vowCtorWardsHashMem_read0_64 (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    (vowCtorWardsHashMem I vat flapper flopper).readWithPadding 0 64 =
      UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split _ 0 32 32 (by omega) (by omega)
    (by norm_num) (by norm_num) (by norm_num)]
  · rw [vowCtorWardsHashMem_read0, vowCtorWardsHashMem_read32]
  · rw [vowCtorWardsHashMem_size]
    omega

theorem vowCtorWardsHashSlot (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((vowCtorWardsHashMem I vat flapper flopper).readWithPadding 0 64))) =
      vowCtorCallerWardsSlot I := by
  rw [vowCtorWardsHashMem_read0_64]
  unfold vowCtorCallerWardsSlot solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨0⟩

set_option maxHeartbeats 1000000 in
theorem vowCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd67 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨67⟩
        [EVM.word flopper.val, EVM.word flapper.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σ) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨86⟩
      [⟨1⟩, EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σ (vowCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨67⟩
        [EVM.word flopper.val, EVM.word flapper.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorArgsMem vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σ) k C at rd67
  have rdBeforeHash := evm_run rd67 with [
    raw caller (by ctor_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (vowCtorArgsMem vat flapper flopper))
      (UInt256.ofNat 7) (by ctor_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw mstore 0 (vowCtorWardsHashMem I vat flapper flopper)
      (UInt256.ofNat 7) (by ctor_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup5 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov)]
  have hslot := vowCtorWardsHashSlot I vat flapper flopper
  have rdSlot := rdBeforeHash.keccak256 0 (vowCtorCallerWardsSlot I) (UInt256.ofNat 7)
    (by ctor_decode) mem_cost hslot (by decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov)]
  obtain ⟨k', C', rd86⟩ := rdBeforeStore.sstore hperm (by ctor_decode) (by evm_ov)
  exact ⟨k', C', by simpa [code] using rd86⟩

/-! ## Solm constructor body helpers -/

abbrev vowCtorLocals (vat flapper flopper : AccountAddress) : Store :=
  (((∅ : Store).insert "vat_" (.address vat)).insert "flapper_" (.address flapper)).insert
    "flopper_" (.address flopper)

abbrev vowCtorLocalsHope (vat flapper flopper : AccountAddress) : Store :=
  (vowCtorLocals vat flapper flopper).insert "_hopeRet" .unit

private theorem evalExpr_vowCtorLocalVat {evm : EVM.State}
    (vat flapper flopper : AccountAddress) :
    evalExpr? config { contract := contract, locals := vowCtorLocals vat flapper flopper } evm
      (.var "vat_") = .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [vowCtorLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

private theorem evalExpr_vowCtorLocalFlapper {evm : EVM.State}
    (vat flapper flopper : AccountAddress) :
    evalExpr? config { contract := contract, locals := vowCtorLocals vat flapper flopper } evm
      (.var "flapper_") = .ok (.address flapper) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [vowCtorLocals, store_get_ne _ _ (by decide), store_get_self]

private theorem vowCtorLocals_get_flapper (vat flapper flopper : AccountAddress) :
    (vowCtorLocals vat flapper flopper).get? "flapper_" = some (.address flapper) := by
  rw [vowCtorLocals, store_get_ne _ _ (by decide), store_get_self]

private theorem evalExpr_vowCtorLocalFlopper {evm : EVM.State}
    (vat flapper flopper : AccountAddress) :
    evalExpr? config { contract := contract, locals := vowCtorLocals vat flapper flopper } evm
      (.var "flopper_") = .ok (.address flopper) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [vowCtorLocals, store_get_self]

abbrev vowCtorCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

private theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hval : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt (lt_trans a.isLt hsize)]
  rw [hval]
  exact a.isLt

set_option maxHeartbeats 1000000 in
theorem vowCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) {k C : ℕ}
    (hperm : I.perm = true)
    (rd86 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨86⟩
        [⟨1⟩, EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨116⟩
      [solcAddrMask, UInt256.lnot solcAddrMask,
        setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val),
        EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σWards ⟨1⟩
          (setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val))) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨86⟩
        [⟨1⟩, EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σWards) k C at rd86
  have rd87 := rd86.dup1 (by ctor_decode) (by evm_ov)
  obtain ⟨_, _, rd88⟩ := rd87.sload (by ctor_decode) (by evm_ov)
  have rdBeforeStore := evm_run rd88 with [
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by ctor_decode) (by evm_ov),
    raw shl (by ctor_decode) (by evm_ov),
    raw sub (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw dup8 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by ctor_decode) (by evm_ov),
    raw shl (by ctor_decode) (by evm_ov),
    raw sub (by ctor_decode) (by evm_ov),
    raw not (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw lor (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov)]
  have hload :
      (σWards.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩)) =
        solcSlotWord σWards I ⟨1⟩ := by
    rfl
  rw [hload] at rdBeforeStore
  have hword :
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨1⟩))
          (UInt256.land (EVM.word vat.val) solcAddrMask) =
        setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val) := by
    calc
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨1⟩))
          (UInt256.land (EVM.word vat.val) solcAddrMask) =
          UInt256.lor
            (UInt256.land (solcSlotWord σWards I ⟨1⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (EVM.word vat.val) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σWards I ⟨1⟩)]
      _ = setAddressOffset0Word (solcSlotWord σWards I ⟨1⟩) (EVM.word vat.val) := by
            rfl
  obtain ⟨k', C', rd116⟩ := rdBeforeStore.sstore hperm (by ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [code, solcSlotWord, setAddressOffset0Word, hword,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd116⟩

set_option maxHeartbeats 1000000 in
theorem vowCtorFlapperStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored : UInt256) {k C : ℕ}
    (hperm : I.perm = true)
    (rd116 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨116⟩
        [solcAddrMask, UInt256.lnot solcAddrMask, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨131⟩
      [EVM.word flapper.val, solcAddrMask, UInt256.lnot solcAddrMask, vatStored,
        EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σVat ⟨2⟩
          (setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val)))
      k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨116⟩
        [solcAddrMask, UInt256.lnot solcAddrMask, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σVat) k C at rd116
  have rdBeforeSload := evm_run rd116 with [
    raw push1 ⟨2⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd120⟩ := rdBeforeSload.sload (by ctor_decode) (by evm_ov)
  have rdBeforeStore := evm_run rd120 with [
    raw dup3 (by ctor_decode) (by evm_ov),
    raw dup8 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw dup5 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw lor (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap2 (by ctor_decode) (by evm_ov)]
  have hload :
      (σVat.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        solcSlotWord σVat I ⟨2⟩ := by
    rfl
  rw [hload] at rdBeforeStore
  have hflapperMask : UInt256.land (EVM.word flapper.val) solcAddrMask =
      EVM.word flapper.val := by
    exact solcAddrMask_clean (word_val_addr_canonical flapper)
  have hword :
      UInt256.lor (UInt256.land (EVM.word flapper.val) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)) =
        setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val) := by
    calc
      UInt256.lor (UInt256.land (EVM.word flapper.val) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)) =
          UInt256.lor (UInt256.land (EVM.word flapper.val) solcAddrMask)
            (UInt256.land (solcSlotWord σVat I ⟨2⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σVat I ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (EVM.word flapper.val) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val) := by
            rfl
  obtain ⟨k', C', rd131⟩ := rdBeforeStore.sstore hperm (by ctor_decode) (by evm_ov)
  have hpc131 :
      (⟨116⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨131⟩ := by
    native_decide
  rw [hpc131] at rd131
  have hwordStore :
      UInt256.lor (EVM.word flapper.val)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)) =
        setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val) := by
    calc
      UInt256.lor (EVM.word flapper.val)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)) =
          UInt256.lor (UInt256.land (EVM.word flapper.val) solcAddrMask)
            (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σVat I ⟨2⟩)) := by
            rw [hflapperMask]
      _ = setAddressOffset0Word (solcSlotWord σVat I ⟨2⟩) (EVM.word flapper.val) := hword
  exact ⟨k', C', by
    simpa [code, solcSlotWord, setAddressOffset0Word, hwordStore, hflapperMask,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd131⟩

set_option maxHeartbeats 1000000 in
theorem vowCtorFlopperStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFlapper σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored : UInt256) {k C : ℕ}
    (hperm : I.perm = true)
    (rd131 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨131⟩
        [EVM.word flapper.val, solcAddrMask, UInt256.lnot solcAddrMask, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFlapper) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨147⟩
      [solcAddrMask, EVM.word flapper.val, vatStored,
        EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
      (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σFlapper ⟨3⟩
          (setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩) (EVM.word flopper.val)))
      k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨131⟩
        [EVM.word flapper.val, solcAddrMask, UInt256.lnot solcAddrMask, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFlapper) k C at rd131
  have rdBeforeSload := evm_run rd131 with [
    raw push1 ⟨3⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd135⟩ := rdBeforeSload.sload (by ctor_decode) (by evm_ov)
  have rdBeforeStore := evm_run rd135 with [
    raw dup4 (by ctor_decode) (by evm_ov),
    raw dup8 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw swap5 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw lor (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov)]
  have hload :
      (σFlapper.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
        solcSlotWord σFlapper I ⟨3⟩ := by
    rfl
  rw [hload] at rdBeforeStore
  have hword :
      UInt256.lor (UInt256.land (EVM.word flopper.val) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σFlapper I ⟨3⟩)) =
        setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩) (EVM.word flopper.val) := by
    calc
      UInt256.lor (UInt256.land (EVM.word flopper.val) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σFlapper I ⟨3⟩)) =
          UInt256.lor (UInt256.land (EVM.word flopper.val) solcAddrMask)
            (UInt256.land (solcSlotWord σFlapper I ⟨3⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σFlapper I ⟨3⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σFlapper I ⟨3⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (EVM.word flopper.val) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩) (EVM.word flopper.val) := by
            rfl
  obtain ⟨k', C', rd147⟩ := rdBeforeStore.sstore hperm (by ctor_decode) (by evm_ov)
  have hpc147 :
      (⟨131⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨147⟩ := by
    native_decide
  rw [hpc147] at rd147
  have hwordStore :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σFlapper I ⟨3⟩))
          (UInt256.land (EVM.word flopper.val) solcAddrMask) =
        setAddressOffset0Word (solcSlotWord σFlapper I ⟨3⟩) (EVM.word flopper.val) := by
    rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σFlapper I ⟨3⟩)]
    rfl
  exact ⟨k', C', by
    simpa [code, solcSlotWord, setAddressOffset0Word, hwordStore,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd147⟩

abbrev vowCtorHopeSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨686590961⟩ ⟨226⟩

abbrev vowCtorHopeSelectorWord : UInt256 :=
  ⟨2746363844⟩

abbrev vowCtorCallOutPtr : UInt256 :=
  ⟨224⟩

abbrev vowCtorCallOutSize : UInt256 :=
  ⟨0⟩

abbrev vowCtorCallInSize : UInt256 :=
  UInt256.add (UInt256.sub vowCtorCallOutPtr vowCtorCallOutPtr) ⟨36⟩

abbrev vowCtorCallEndPtr : UInt256 :=
  UInt256.add vowCtorCallOutPtr ⟨36⟩

noncomputable def vowCtorHopeSelectorMem (mem : ByteArray) : ByteArray :=
  vowCtorHopeSelectorShifted.toByteArray.write 0 mem 224 32

noncomputable def vowCtorHopeCalldataMem (arg : UInt256) (mem : ByteArray) : ByteArray :=
  arg.toByteArray.write 0 (vowCtorHopeSelectorMem mem) 228 32

theorem vowCtorHopeSelectorMem_size {mem : ByteArray} (hmem : mem.size = 224) :
    (vowCtorHopeSelectorMem mem).size = 256 := by
  unfold vowCtorHopeSelectorMem
  exact toByteArray_write32_size_of_ge mem vowCtorHopeSelectorShifted 224 224 256 hmem
    (by omega) (by native_decide) (by omega)

theorem vowCtorHopeCalldataMem_size (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 224) :
    (vowCtorHopeCalldataMem arg mem).size = 260 := by
  unfold vowCtorHopeCalldataMem
  exact toByteArray_write32_size_of_le (vowCtorHopeSelectorMem mem) arg 228 256 260
    (vowCtorHopeSelectorMem_size hmem)
    (by rw [vowCtorHopeSelectorMem_size hmem]; omega)
    (by omega)

theorem vowCtorWardsHashMem_read64 (I : ExecutionEnv) (vat flapper flopper : AccountAddress) :
    (vowCtorWardsHashMem I vat flapper flopper).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold vowCtorWardsHashMem twoWordHashMem wordAt32Mem
  have h0size : (wordAt0Mem (solcSourceWord I) (vowCtorArgsMem vat flapper flopper)).size =
      224 := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le (vowCtorArgsMem vat flapper flopper)
      (solcSourceWord I) 0 224 224 (vowCtorArgsMem_size vat flapper flopper)
      (by rw [vowCtorArgsMem_size]; omega) (by omega)
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [h0size]; omega) (by omega) (by rw [h0size]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [vowCtorArgsMem_size]; omega) (by omega)
      (by rw [vowCtorArgsMem_size]; omega)]
  rw [vowCtorArgsMem]
  exact toByteArray_write32_read_back (vowCtorCopiedMem vat flapper flopper) ⟨224⟩ 64
    (by rw [vowCtorCopiedMem_eq, vowCtorArgsMem_base_size]; omega)

theorem vowCtorHopeSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 224)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩) :
    (vowCtorHopeSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
  unfold vowCtorHopeSelectorMem
  rw [write32_read_below _ _ 224 64 (by rw [toByteArray_size])
    (by simpa [hmem]) (by omega)]
  exact hread64

theorem vowCtorHopeCalldataMem_read64 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 224)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩) :
    (vowCtorHopeCalldataMem arg mem).readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
  unfold vowCtorHopeCalldataMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
    (by rw [vowCtorHopeSelectorMem_size hmem]; omega) (by omega)]
  exact vowCtorHopeSelectorMem_read64 hmem hread64

set_option maxHeartbeats 2000000 in
theorem vowCtorCallSetupReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFinal σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored : UInt256) {k C : ℕ}
    (rd147 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨147⟩
        [solcAddrMask, EVM.word flapper.val, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFinal) k C) :
    ∃ k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨201⟩
      [UInt256.land solcAddrMask vatStored, UInt256.land solcAddrMask vatStored,
        vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
        vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
        vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
        EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
      (vowCtorHopeCalldataMem (EVM.word flapper.val)
        (vowCtorWardsHashMem I vat flapper flopper))
      (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k' C' := by
  let code := vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨147⟩
        [solcAddrMask, EVM.word flapper.val, vatStored,
          EVM.word flopper.val, EVM.word flapper.val, ⟨0⟩, EVM.word vat.val, ⟨64⟩]
        (vowCtorWardsHashMem I vat flapper flopper) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFinal) k C at rd147
  have hmem0 : (vowCtorWardsHashMem I vat flapper flopper).size = 224 :=
    vowCtorWardsHashMem_size I vat flapper flopper
  have hread64 := vowCtorWardsHashMem_read64 I vat flapper flopper
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (vowCtorWardsHashMem I vat flapper flopper).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vowCtorWardsHashMem I vat flapper flopper).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨224⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7) (v := (⟨224⟩ : UInt256))
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rw [hmem0]; omega)
      (by decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread64)
  have hcallMemSize :
      (vowCtorHopeCalldataMem (EVM.word flapper.val)
        (vowCtorWardsHashMem I vat flapper flopper)).size = 260 :=
    vowCtorHopeCalldataMem_size _ hmem0
  have hcallMemRead64 :
      (vowCtorHopeCalldataMem (EVM.word flapper.val)
        (vowCtorWardsHashMem I vat flapper flopper)).readWithPadding 64 32 =
          UInt256.toByteArray ⟨224⟩ :=
    vowCtorHopeCalldataMem_read64 _ hmem0 hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (vowCtorHopeCalldataMem (EVM.word flapper.val)
              (vowCtorWardsHashMem I vat flapper flopper)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vowCtorHopeCalldataMem (EVM.word flapper.val)
            (vowCtorWardsHashMem I vat flapper flopper)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨224⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 9) (v := (⟨224⟩ : UInt256))
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rw [hcallMemSize]; omega)
      (by decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hcallMemRead64)
  have rd201 := evm_run rd147 with [
    raw dup8 (by ctor_decode) (by evm_ov),
    raw mload 0 ⟨224⟩ (UInt256.ofNat 7) (by ctor_decode) mem_cost hmload64
      (by decide) (by evm_ov),
    raw push4 ⟨686590961⟩ (by ctor_decode) (by evm_ov),
    raw push1 ⟨226⟩ (by ctor_decode) (by evm_ov),
    raw shl (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw mstore 3 (vowCtorHopeSelectorMem (vowCtorWardsHashMem I vat flapper flopper))
      (UInt256.ofNat 8) (by ctor_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw mstore 3 (vowCtorHopeCalldataMem (EVM.word flapper.val)
        (vowCtorWardsHashMem I vat flapper flopper))
      (UInt256.ofNat 9) (by ctor_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap7 (by ctor_decode) (by evm_ov),
    raw mload 0 ⟨224⟩ (UInt256.ofNat 9) (by ctor_decode) mem_cost hmload64Call
      (by decide) (by evm_ov),
    raw swap6 (by ctor_decode) (by evm_ov),
    raw swap7 (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw swap6 (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw swap5 (by ctor_decode) (by evm_ov),
    raw swap2 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw and (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw push4 vowCtorHopeSelectorWord (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw swap4 (by ctor_decode) (by evm_ov),
    raw swap3 (by ctor_decode) (by evm_ov),
    raw dup3 (by ctor_decode) (by evm_ov),
    raw swap1 (by ctor_decode) (by evm_ov),
    raw sub (by ctor_decode) (by evm_ov),
    raw add (by ctor_decode) (by evm_ov),
    raw dup2 (by ctor_decode) (by evm_ov),
    raw dup4 (by ctor_decode) (by evm_ov),
    raw dup8 (by ctor_decode) (by evm_ov),
    raw dup1 (by ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [code, vowCtorHopeSelectorShifted, vowCtorHopeSelectorWord,
      vowCtorHopeSelectorMem, vowCtorHopeCalldataMem,
      vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallInSize, vowCtorCallEndPtr,
      solcAddrMask] using rd201⟩

theorem vowCtorHopeNoCode
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFinal σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored : UInt256) {k C : ℕ}
    (rd201 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨201⟩
        [UInt256.land solcAddrMask vatStored, UInt256.land solcAddrMask vatStored,
          vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
          vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
          vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
          EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
        (vowCtorHopeCalldataMem (EVM.word flapper.val)
          (vowCtorWardsHashMem I vat flapper flopper))
        (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σFinal (UInt256.land solcAddrMask vatStored) =
        ⟨0⟩) :
    RDrev (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨201⟩) (okPc := ⟨213⟩) rd201
    hcodeSize
    (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode)
    (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode)
    (by ctor_decode) (by simp)

theorem vowCtorHopeCallReady
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFinal σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored : UInt256) {k C : ℕ}
    (rd201 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨201⟩
        [UInt256.land solcAddrMask vatStored, UInt256.land solcAddrMask vatStored,
          vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
          vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
          vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
          EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
        (vowCtorHopeCalldataMem (EVM.word flapper.val)
          (vowCtorWardsHashMem I vat flapper flopper))
        (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σFinal (UInt256.land solcAddrMask vatStored) ≠
        ⟨0⟩) :
    ∃ gasWord k' C', RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨216⟩
      [gasWord, UInt256.land solcAddrMask vatStored,
        vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
        vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
        vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
        EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
      (vowCtorHopeCalldataMem (EVM.word flapper.val)
        (vowCtorWardsHashMem I vat flapper flopper))
      (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k' C' := by
  obtain ⟨gasWord, k', C', rd216⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨201⟩) (okPc := ⟨213⟩) rd201
      hcodeSize
      (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by ctor_jump_dest) (by ctor_decode)
      (by ctor_decode) (by ctor_decode) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd216⟩

theorem vowCtorHopePostCall
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σFinal σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat flapper flopper : AccountAddress) (vatStored gasWord : UInt256) {k C : ℕ}
    (rd216 :
      RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨216⟩
        [gasWord, UInt256.land solcAddrMask vatStored,
          vowCtorCallOutSize, vowCtorCallOutPtr, vowCtorCallInSize,
          vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallEndPtr,
          vowCtorHopeSelectorWord, UInt256.land solcAddrMask vatStored,
          EVM.word flopper.val, EVM.word flapper.val, EVM.word vat.val]
        (vowCtorHopeCalldataMem (EVM.word flapper.val)
          (vowCtorWardsHashMem I vat flapper flopper))
        (UInt256.ofNat 9) ByteArray.empty (createdAccounts, σFinal) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (createdAccounts' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (createdAccounts', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes
          createdAccounts (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).genesisBlockHeader
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).blocks σFinal
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (UInt256.land solcAddrMask vatStored))
          (toExecute σFinal (AccountAddress.ofUInt256 (UInt256.land solcAddrMask vatStored)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((vowCtorHopeCalldataMem (EVM.word flapper.val)
            (vowCtorWardsHashMem I vat flapper flopper)).readWithPadding
            vowCtorCallOutPtr.toNat vowCtorCallInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: vowCtorCallEndPtr :: vowCtorHopeSelectorWord ::
            UInt256.land solcAddrMask vatStored :: EVM.word flopper.val :: EVM.word flapper.val ::
            EVM.word vat.val :: [])
          (vowCtorHopeCalldataMem (EVM.word flapper.val)
            (vowCtorWardsHashMem I vat flapper flopper))
          (UInt256.ofNat 9) out (createdAccounts', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨createdAccounts', σ', z, out, Ain, callGas, k', C', hΘ, rd217raw, hout⟩ :=
    RD.call rd216 (by ctor_decode) hdepth (by evm_ov)
  refine ⟨createdAccounts', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          vowCtorCallOutPtr.toNat vowCtorCallInSize.toNat)
          vowCtorCallOutPtr.toNat vowCtorCallOutSize.toNat) = UInt256.ofNat 9 := by
      unfold vowCtorCallOutPtr vowCtorCallInSize vowCtorCallOutSize
      native_decide
    have hmin : (min vowCtorCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold vowCtorCallOutSize
      rfl
    have rd217 : RD (vowCreationBytecode ++ vowCtorArgsTail vat flapper flopper) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨217⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: vowCtorCallEndPtr :: vowCtorHopeSelectorWord ::
          UInt256.land solcAddrMask vatStored :: EVM.word flopper.val :: EVM.word flapper.val ::
          EVM.word vat.val :: [])
        (out.write 0 (vowCtorHopeCalldataMem (EVM.word flapper.val)
          (vowCtorWardsHashMem I vat flapper flopper)) vowCtorCallOutPtr.toNat
          (min vowCtorCallOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (createdAccounts', σ') k' C' := by
      simpa [haw, vowCtorCallOutPtr, vowCtorCallOutSize, vowCtorCallInSize,
        vowCtorCallEndPtr] using rd217raw
    rw [hmin, byteArray_write_len_zero] at rd217
    simpa using rd217

theorem vowCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = vowCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot vowCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem vowCtorCallerWardsEvaledRef_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store} :
    evalStorageRef config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (vowCtorCallerWardsEvaledRef I) := by
  simp [vowCtorCallerWardsEvaledRef, wardsRef, sender, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, envValue, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, pure, bind, initState]

theorem assign_vowCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm
      (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

private theorem assign_vowCtorAddressStorage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot : UInt256) (addrValue : AccountAddress)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address addrValue : Value) =
        .address (AccountAddress.ofNat (EVM.word addrValue.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  have hstore :
      storageLocStore evm (addrLoc slot)
          (.address (AccountAddress.ofNat (EVM.word addrValue.val).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm slot (EVM.word addrValue.val)
        (word_val_addr_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := hstore)

theorem assign_vowCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
        (EVM.word vat.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_vowCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨1⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_vowCtorFlapperStorage (evm : EVM.State) (locals : Store)
    (flapper : AccountAddress) (hbase : locals.get? "flapper" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (EVM.word flapper.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage flapperRef (.address flapper) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_vowCtorAddressStorage evm locals flapperRef { base := "flapper", steps := [] }
    ⟨2⟩ flapper
    (by simpa [flapperRef] using hbase)
    (by simp [flapperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_vowCtorFlopperStorage (evm : EVM.State) (locals : Store)
    (flopper : AccountAddress) (hbase : locals.get? "flopper" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        (EVM.word flopper.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage flopperRef (.address flopper) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_vowCtorAddressStorage evm locals flopperRef { base := "flopper", steps := [] }
    ⟨3⟩ flopper
    (by simpa [flopperRef] using hbase)
    (by simp [flopperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_vowCtorLiveStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "live" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨12⟩ ⟨1⟩
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm liveRef =
        .ok { base := "live", steps := [] } := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore : storageLocStore evm (wordLoc ⟨12⟩) (.int 1) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨12⟩ ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨12⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

abbrev vowCtorVatAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask).toNat

theorem evalExpr_vowCtorVatStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (vowCtorVatAddressOf evm)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 _ ⟨1⟩)
  · exact hbase
  · simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExpr_vowCtorVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_vowCtorVatCodeGuard_false {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExprs_vowCtorHopeArgs (evm : EVM.State) {locals : Store}
    {flapper : AccountAddress}
    (hflapper : locals.get? "flapper_" = some (.address flapper)) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "flapper_"] =
      .ok [.address flapper] := by
  have hflapperEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "flapper_") =
        .ok (.address flapper) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "flapper_") =
      .ok (.address flapper)
    rw [hflapper]
    rfl
  simp [evalExprs?, hflapperEval, EvalResult.bind, bind, pure]

theorem vowExternalABI_decode_hope_ctor (out : ByteArray) :
    config.externalABI.decode? "hope" out = some ([] : List Solm.Value) := by
  simp [config, vowExternalABI, decodeVoid?]

abbrev vowCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev vowCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (EVM.word vat.val))

abbrev vowCtorAfterFlapperState (evm : EVM.State) (flapper : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word flapper.val))

abbrev vowCtorAfterFlopperState (evm : EVM.State) (flopper : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word flopper.val))

abbrev vowCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨12⟩ ⟨1⟩

theorem vowCtorBodyPrefixToHope
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat flapper flopper : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := vowCtorLocals vat flapper flopper
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := vowCtorAfterWardsState evm0
    let evm2 := vowCtorAfterVatState evm1 vat
    let evm3 := vowCtorAfterFlapperState evm2 flapper
    let evm4 := vowCtorAfterFlopperState evm3 flopper
    ExecBlock config { contract := contract, locals := locals } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage flapperRef (.var "flapper_"),
        .assign .storage flopperRef (.var "flopper_") ]
      (.ok { contract := contract, locals := locals } evm4) := by
  intro locals evm0 evm1 evm2 evm3 evm4
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, vowCtorAfterWardsState] using
      assign_vowCtorWardsCaller evm0 (locals := locals) (by simp [locals, vowCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, vowCtorAfterVatState] using
      assign_vowCtorVatStorage evm1 locals vat (by simp [locals, vowCtorLocals])
  have hassignFlapper :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage flapperRef (.address flapper) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, vowCtorAfterFlapperState] using
      assign_vowCtorFlapperStorage evm2 locals flapper (by simp [locals, vowCtorLocals])
  have hassignFlopper :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage flopperRef (.address flopper) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, vowCtorAfterFlopperState] using
      assign_vowCtorFlopperStorage evm3 locals flopper (by simp [locals, vowCtorLocals])
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_vowCtorLocalVat (evm := evm1) vat flapper flopper
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignFlapper) ?_
  · simpa [locals] using evalExpr_vowCtorLocalFlapper (evm := evm2) vat flapper flopper
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignFlopper) ExecBlock.nil
  · simpa [locals] using evalExpr_vowCtorLocalFlopper (evm := evm3) vat flapper flopper

theorem vowCtorSolmExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat flapper flopper : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address vat, .address flapper, .address flopper]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := vowCtorLocals vat flapper flopper)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := vowCtorLocals vat flapper flopper) hwv

theorem vowCtorSolmExecReverts_noCode
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat flapper flopper : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatNoCode :
      let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := vowCtorAfterWardsState evm0
      let evm2 := vowCtorAfterVatState evm1 vat
      let evm3 := vowCtorAfterFlapperState evm2 flapper
      let evm4 := vowCtorAfterFlopperState evm3 flopper
      (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat = 0) :
    solmCtorExec config contract [.address vat, .address flapper, .address flopper]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  let locals := vowCtorLocals vat flapper flopper
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
  let evm1 := vowCtorAfterWardsState evm0
  let evm2 := vowCtorAfterVatState evm1 vat
  let evm3 := vowCtorAfterFlapperState evm2 flapper
  let evm4 := vowCtorAfterFlopperState evm3 flopper
  refine solmCtorExec.intro (evmState := evm0) (argsStore := locals) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · refine ExecFuncBody.execBlockRevert ?_
    have hprefix := vowCtorBodyPrefixToHope
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat flapper flopper hwv
    have hvat :
        evalExpr? config { contract := contract, locals := locals } evm4 (.var "vat_") =
          .ok (.address vat) := by
      simpa [locals] using evalExpr_vowCtorLocalVat (evm := evm4) vat flapper flopper
    have hguard :
        evalExpr? config { contract := contract, locals := locals } evm4
          (.binary .gt (.extCodeSize (.var "vat_")) (.intLit 0)) = .ok (.bool false) := by
      have hcode0 :
          (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat =
            0 := by
        simpa [evm0, evm1, evm2, evm3, evm4] using hvatNoCode
      simpa [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode0]
    have htail :
        ExecBlock config { contract := contract, locals := locals } evm4
          (checkedExternalCallStmts (.var "vat_") "hope" (.intLit 0)
              [.var "flapper_"] "_hopeRet" ++
            [ .assign .storage liveRef (.intLit 1) ])
          .reverted := by
      simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
      exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    simpa [ExecTransitionBody, contract, constructorDecl, nonpayable, checkedExternalCallStmts,
      locals, evm0, evm1, evm2, evm3, evm4, List.cons_append, List.nil_append] using
     .execBlock_append hprefix htail

theorem vowCtorSolmExecReverts_callFailure
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evmHope : EVM.State} {out : ByteArray}
    (vat flapper flopper : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := vowCtorAfterWardsState evm0
      let evm2 := vowCtorAfterVatState evm1 vat
      let evm3 := vowCtorAfterFlapperState evm2 flapper
      let evm4 := vowCtorAfterFlopperState evm3 flopper
      0 < (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := vowCtorAfterWardsState evm0
      let evm2 := vowCtorAfterVatState evm1 vat
      let evm3 := vowCtorAfterFlapperState evm2 flapper
      let evm4 := vowCtorAfterFlopperState evm3 flopper
      typedCallViaEVM config evm4 (EVM.address vat) "hope" 0
        [.address flapper] (false, evmHope, out) true) :
    solmCtorExec config contract [.address vat, .address flapper, .address flopper]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  let locals := vowCtorLocals vat flapper flopper
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
  let evm1 := vowCtorAfterWardsState evm0
  let evm2 := vowCtorAfterVatState evm1 vat
  let evm3 := vowCtorAfterFlapperState evm2 flapper
  let evm4 := vowCtorAfterFlopperState evm3 flopper
  refine solmCtorExec.intro (evmState := evm0) (argsStore := locals) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · refine ExecFuncBody.execBlockRevert ?_
    have hprefix := vowCtorBodyPrefixToHope
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat flapper flopper hwv
    have hvat :
        evalExpr? config { contract := contract, locals := locals } evm4 (.var "vat_") =
          .ok (.address vat) := by
      simpa [locals] using evalExpr_vowCtorLocalVat (evm := evm4) vat flapper flopper
    have hguard :
        evalExpr? config { contract := contract, locals := locals } evm4
          (.binary .gt (.extCodeSize (.var "vat_")) (.intLit 0)) = .ok (.bool true) := by
      have hcodePos :
          0 <
            (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat :=
        by simpa [evm0, evm1, evm2, evm3, evm4] using hvatCode
      simpa [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcodePos]
    have hargs :
        evalExprs? config { contract := contract, locals := locals } evm4 [.var "flapper_"] =
          .ok [.address flapper] := by
      simpa [locals] using evalExprs_vowCtorHopeArgs evm4
        (locals := vowCtorLocals vat flapper flopper)
        (vowCtorLocals_get_flapper vat flapper flopper)
    have htail :
        ExecBlock config { contract := contract, locals := locals } evm4
          (checkedExternalCallStmts (.var "vat_") "hope" (.intLit 0)
              [.var "flapper_"] "_hopeRet" ++
            [ .assign .storage liveRef (.intLit 1) ])
          .reverted := by
      simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
      refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
      exact ExecBlock.consRevert
        (ExecStmt.externalCallFailure (sendVal := 0) hvat (by simp [evalExpr?, pure]) hargs
          (by simpa [evm0, evm1, evm2, evm3, evm4] using hcall))
    simpa [ExecTransitionBody, contract, constructorDecl, nonpayable, checkedExternalCallStmts,
      locals, evm0, evm1, evm2, evm3, evm4, List.cons_append, List.nil_append] using
     .execBlock_append hprefix htail

theorem vowCtorSolmExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evmHope : EVM.State} {out : ByteArray}
    (vat flapper flopper : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := vowCtorAfterWardsState evm0
      let evm2 := vowCtorAfterVatState evm1 vat
      let evm3 := vowCtorAfterFlapperState evm2 flapper
      let evm4 := vowCtorAfterFlopperState evm3 flopper
      0 < (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := vowCtorAfterWardsState evm0
      let evm2 := vowCtorAfterVatState evm1 vat
      let evm3 := vowCtorAfterFlapperState evm2 flapper
      let evm4 := vowCtorAfterFlopperState evm3 flopper
      typedCallViaEVM config evm4 (EVM.address vat) "hope" 0
        [.address flapper] (true, evmHope, out) true) :
    solmCtorExec config contract [.address vat, .address flapper, .address flopper]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := vowCtorLocalsHope vat flapper flopper }
        (vowCtorAfterLiveState evmHope) none) := by
  let locals := vowCtorLocals vat flapper flopper
  let localsHope := vowCtorLocalsHope vat flapper flopper
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
  let evm1 := vowCtorAfterWardsState evm0
  let evm2 := vowCtorAfterVatState evm1 vat
  let evm3 := vowCtorAfterFlapperState evm2 flapper
  let evm4 := vowCtorAfterFlopperState evm3 flopper
  let evm5 := vowCtorAfterLiveState evmHope
  refine solmCtorExec.intro (evmState := evm0) (argsStore := locals) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · refine ?_
    have hprefix := vowCtorBodyPrefixToHope
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat flapper flopper hwv
    have hvat :
        evalExpr? config { contract := contract, locals := locals } evm4 (.var "vat_") =
          .ok (.address vat) := by
      simpa [locals] using evalExpr_vowCtorLocalVat (evm := evm4) vat flapper flopper
    have hguard :
        evalExpr? config { contract := contract, locals := locals } evm4
          (.binary .gt (.extCodeSize (.var "vat_")) (.intLit 0)) = .ok (.bool true) := by
      have hcodePos :
          0 <
            (UInt256.ofNat ((evm4.lookupAccount vat).option 0 (fun acc => acc.code.size))).toNat :=
        by simpa [evm0, evm1, evm2, evm3, evm4] using hvatCode
      simpa [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcodePos]
    have hargs :
        evalExprs? config { contract := contract, locals := locals } evm4 [.var "flapper_"] =
          .ok [.address flapper] := by
      simpa [locals] using evalExprs_vowCtorHopeArgs evm4
        (locals := vowCtorLocals vat flapper flopper)
        (vowCtorLocals_get_flapper vat flapper flopper)
    have hcallStmt :
        ExecStmt config { contract := contract, locals := locals } evm4
          (.externalCall (.var "vat_") "hope" (.intLit 0) [.var "flapper_"] "_hopeRet")
          (.ok { contract := contract, locals := localsHope } evmHope) := by
      simpa [locals, localsHope, vowCtorLocalsHope, collapseReturns, config, vowExternalABI,
        decodeVoid?] using
          ExecStmt.externalCallSuccess (sendVal := 0) hvat (by simp [evalExpr?, pure]) hargs
            (by simpa [evm0, evm1, evm2, evm3, evm4] using hcall)
            (vowExternalABI_decode_hope_ctor out)
    have hassignLive :
        assignStorageRef? config { contract := contract, locals := localsHope } evmHope
          .storage liveRef (.int 1) =
            .ok ({ contract := contract, locals := localsHope }, evm5) := by
      simpa [evm5, vowCtorAfterLiveState] using
        assign_vowCtorLiveStorage evmHope (locals := localsHope)
          (by simp [localsHope, vowCtorLocalsHope, vowCtorLocals])
    have htail :
        ExecBlock config { contract := contract, locals := locals } evm4
          (checkedExternalCallStmts (.var "vat_") "hope" (.intLit 0)
              [.var "flapper_"] "_hopeRet" ++
            [ .assign .storage liveRef (.intLit 1) ])
          (.ok { contract := contract, locals := localsHope } evm5) := by
      simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
      refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
      refine ExecBlock.consNormal hcallStmt ?_
      exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive)
        ExecBlock.nil
    have hblock :
        ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
          (.ok { contract := contract, locals := localsHope } evm5) := by
      simpa [constructorDecl, nonpayable, checkedExternalCallStmts, locals, evm0, evm1, evm2,
        evm3, evm4, evm5, List.cons_append, List.nil_append] using
       .execBlock_append hprefix htail
    simpa [ExecTransitionBody, contract, constructorDecl, locals, localsHope, evm0, evm5] using
      ExecFuncBody.execBlockOK hblock

end Benchmarks.Dss.Vow
