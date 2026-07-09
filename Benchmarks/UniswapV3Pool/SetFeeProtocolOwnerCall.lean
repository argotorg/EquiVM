import Benchmarks.UniswapV3Pool.ImmutableGetters
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem setFeeProtocolExternalABIEncodeOwner {v : PoolImmutables} :
    (config v).externalABI.encode? "owner" [] = some ownerSelector := by
  simp [config, poolExternalABI]

abbrev setFeeProtocolOwnerSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨2376452955⟩ ⟨224⟩

abbrev setFeeProtocolOwnerCallMem : ByteArray :=
  (UInt256.toByteArray setFeeProtocolOwnerSelectorWord).write 0 solcFreePtrMem 128 32

abbrev setFeeProtocolFactoryWord (v : PoolImmutables) : UInt256 :=
  EVM.Word.ofNat v.factory.toNat

theorem setFeeProtocolFactoryAddress_eq (v : PoolImmutables) :
    AccountAddress.ofUInt256 (setFeeProtocolFactoryWord v) =
      AccountAddress.ofNat v.factory.toNat := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat, setFeeProtocolFactoryWord,
    accountAddressWord_toNat]

theorem setFeeProtocolFactoryMask_eq_solcAddrMask :
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
  native_decide

theorem setFeeProtocolFactoryTarget_eq (v : PoolImmutables) :
    UInt256.land (setFeeProtocolFactoryWord v)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
      setFeeProtocolFactoryWord v := by
  rw [setFeeProtocolFactoryMask_eq_solcAddrMask]
  apply solcAddrMask_clean
  rw [setFeeProtocolFactoryWord, accountAddressWord_toNat]
  change v.factory.toNat < EVM.twoPow 160
  simp [EVM.twoPow, AccountAddress.size]

theorem setFeeProtocolOwnerSelectorWord_extract :
    (UInt256.toByteArray setFeeProtocolOwnerSelectorWord).extract 0 4 = ownerSelector := by
  native_decide

theorem setFeeProtocolOwnerCallMem_read_selector :
    setFeeProtocolOwnerCallMem.readWithPadding 128 4 = ownerSelector := by
  rw [setFeeProtocolOwnerCallMem]
  rw [toByteArray_write_read_window_of_gap
    (b := setFeeProtocolOwnerSelectorWord) (mem := solcFreePtrMem)
    (off := 128) (start := 0) (len := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [solcFreePtrMem_size]; native_decide)]
  exact setFeeProtocolOwnerSelectorWord_extract

theorem setFeeProtocolOwnerCallMem_encode_owner {v : PoolImmutables} :
    (config v).externalABI.encode? "owner" [] =
      some (setFeeProtocolOwnerCallMem.readWithPadding 128 4) := by
  rw [setFeeProtocolOwnerCallMem_read_selector]
  exact setFeeProtocolExternalABIEncodeOwner

theorem setFeeProtocolOwnerCallMem_read64 :
    setFeeProtocolOwnerCallMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [setFeeProtocolOwnerCallMem]
  rw [toByteArray_write_read_below_of_gap
    (b := setFeeProtocolOwnerSelectorWord) (mem := solcFreePtrMem)
    (off := 128) (read := 64)
    (by rw [solcFreePtrMem_size])
    (by norm_num)
    (by rw [solcFreePtrMem_size]; native_decide)]
  exact solcFreePtrMem_read64

theorem setFeeProtocolOwnerCallMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ setFeeProtocolOwnerCallMem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat
          (fromByteArrayBigEndian (setFeeProtocolOwnerCallMem.readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadWordValue_of_readWithPadding (mem := setFeeProtocolOwnerCallMem)
    (aw := UInt256.ofNat 5) (off := ⟨64⟩) (v := ⟨128⟩)
      (by rw [setFeeProtocolOwnerCallMem]; native_decide)
      (by native_decide)
      setFeeProtocolOwnerCallMem_read64
  
theorem setFeeProtocolOwnerCallMem_size :
    setFeeProtocolOwnerCallMem.size = 160 := by
  native_decide

abbrev setFeeProtocolOwnerStaticcallMem (o : ByteArray) : ByteArray :=
  o.write 0 setFeeProtocolOwnerCallMem 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

abbrev setFeeProtocolOwnerStaticcallActiveWords : UInt256 :=
  UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat 128 4) 128 32)

theorem setFeeProtocolOwnerStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hshort hhi

theorem setFeeProtocolOwnerStaticcallWriteLen_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  simpa using
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi

theorem setFeeProtocolOwnerStaticcallMem_size_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (setFeeProtocolOwnerStaticcallMem o).size = 160 := by
  unfold setFeeProtocolOwnerStaticcallMem
  rw [setFeeProtocolOwnerStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_eq _ _ _ hlo (by rw [setFeeProtocolOwnerCallMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, setFeeProtocolOwnerCallMem_size]
  omega

theorem setFeeProtocolOwnerStaticcallMem_size_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (setFeeProtocolOwnerStaticcallMem o).size = 160 := by
  unfold setFeeProtocolOwnerStaticcallMem
  rw [setFeeProtocolOwnerStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact setFeeProtocolOwnerCallMem_size
  · rw [write_eq_gen _ _ 128 o.size hzero le_rfl
      (by rw [setFeeProtocolOwnerCallMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, setFeeProtocolOwnerCallMem_size]
    omega

theorem setFeeProtocolOwnerStaticcallMem_read64_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (setFeeProtocolOwnerStaticcallMem o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setFeeProtocolOwnerStaticcallMem
  rw [setFeeProtocolOwnerStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact setFeeProtocolOwnerCallMem_read64
  · rw [write_read_below_gen _ _ 128 o.size 64 hzero le_rfl
      (by rw [setFeeProtocolOwnerCallMem_size]; omega) (by omega)]
    exact setFeeProtocolOwnerCallMem_read64
  
theorem setFeeProtocolOwnerStaticcallMem_read64_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (setFeeProtocolOwnerStaticcallMem o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setFeeProtocolOwnerStaticcallMem
  rw [setFeeProtocolOwnerStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_read_below _ _ 128 64 hlo (by rw [setFeeProtocolOwnerCallMem_size]; omega)
    (by omega)]
  exact setFeeProtocolOwnerCallMem_read64

theorem setFeeProtocolOwnerStaticcallMem_mload64_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setFeeProtocolOwnerStaticcallMem o).size
        ∨ (⟨64⟩ : UInt256) ≥ setFeeProtocolOwnerStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setFeeProtocolOwnerStaticcallMem o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
      (by rw [setFeeProtocolOwnerStaticcallMem_size_of_size_lt o hshort hhi]; decide)
      (by decide)
      (setFeeProtocolOwnerStaticcallMem_read64_of_size_lt o hshort hhi)
  
theorem setFeeProtocolOwnerStaticcallMem_mload64_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setFeeProtocolOwnerStaticcallMem o).size
        ∨ (⟨64⟩ : UInt256) ≥ setFeeProtocolOwnerStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setFeeProtocolOwnerStaticcallMem o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [setFeeProtocolOwnerStaticcallMem_size_of_size_ge o hlo hhi]; decide)
    (by decide)
    (setFeeProtocolOwnerStaticcallMem_read64_of_size_ge o hlo hhi)

theorem setFeeProtocolOwnerStaticcallMem_read128_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (setFeeProtocolOwnerStaticcallMem o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold setFeeProtocolOwnerStaticcallMem
  rw [setFeeProtocolOwnerStaticcallWriteLen_of_size_ge o hlo hhi]
  exact write32_read_back _ _ 128 hlo (by rw [setFeeProtocolOwnerCallMem_size]; omega)

theorem setFeeProtocolOwnerStaticcallMem_mload128_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setFeeProtocolOwnerStaticcallMem o).size
        ∨ (⟨128⟩ : UInt256) ≥ setFeeProtocolOwnerStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setFeeProtocolOwnerStaticcallMem o).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      setFeeProtocolOwnerStaticcallMem_read128_of_size_ge o hlo hhi]
  · rw [not_or]
    constructor
    · rw [setFeeProtocolOwnerStaticcallMem_size_of_size_ge o hlo hhi]
      decide
    · decide

theorem uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 8208 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 8315) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 8829) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 2 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 1) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 1 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 1)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x60 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x60 : UInt8) >>= parseInstr) = some (.Push .PUSH1) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH1,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) =
    some (Operation.Push Operation.POp.PUSH1, some (n, 1))
  rw [hextract, hval]

theorem uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 3 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 2) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 2 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 2)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x61 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x61 : UInt8) >>= parseInstr) = some (.Push .PUSH2) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH2,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 2)), 2)) =
    some (Operation.Push Operation.POp.PUSH2, some (n, 2))
  rw [hextract, hval]

theorem uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush4 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 5 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 5 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x63)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 4)) = n) :
    decode code pc = some (.Push .PUSH4, some (n, 4)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 4) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 4) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 4 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 4)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x63 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x63 : UInt8) >>= parseInstr) = some (.Push .PUSH4) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH4,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 4)), 4)) =
    some (Operation.Push Operation.POp.PUSH4, some (n, 4))
  rw [hextract, hval]

theorem uniswapV3PoolSetFeeProtocolOwnerCallSetup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8290⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8348⟩
      (setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨128⟩ :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  have hd8347 : decode code ⟨8347⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8347⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8314 :
      decode code ⟨8314⟩ =
        some (.Push .PUSH32, some (setFeeProtocolFactoryWord v, 32)) := by
    simpa [setFeeProtocolFactoryWord] using
      uniswapV3PoolFactoryConstDecode8314 (v := v) (code := code) hpatch
  have rd8348Pre := evm_run h with [
    raw push1 ⟨64⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8290⟩)
        (n := ⟨64⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by omega),
    raw dup1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8292⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by omega),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8293⟩) (byte := 0x51)
        (op := .MLOAD) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      mem_cost solcFreePtrMem_mload64 (by decide)
      (by simp only [List.length_cons]; omega),
    raw push4 ⟨2376452955⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush4 (pc := ⟨8294⟩)
        (n := ⟨2376452955⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 5)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw push1 ⟨224⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8299⟩)
        (n := ⟨224⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw shl (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8301⟩) (byte := 0x1b)
        (op := .SHL) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw dup2 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8302⟩) (byte := 0x81)
        (op := .DUP2) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw mstore 6 setFeeProtocolOwnerCallMem (UInt256.ofNat 5) (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8303⟩) (byte := 0x52)
        (op := .MSTORE) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      mem_cost (by rfl) (by decide) (by simp only [List.length_cons]; omega),
    raw swap1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8304⟩) (byte := 0x90)
        (op := .SWAP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by omega),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8305⟩) (byte := 0x51)
        (op := .MLOAD) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      mem_cost setFeeProtocolOwnerCallMem_mload64 (by decide)
      (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8306⟩)
        (n := ⟨1⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8308⟩)
        (n := ⟨1⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw push1 ⟨160⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8310⟩)
        (n := ⟨160⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw shl (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8312⟩) (byte := 0x1b)
        (op := .SHL) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw sub (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8313⟩) (byte := 0x03)
        (op := .SUB) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointBeforeFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw pushConst (setFeeProtocolFactoryWord v)
      (show Operation.POp.PUSH32 ≠ .PUSH0 by native_decide)
      hd8314
      (by simp only [List.length_cons]; omega),
    raw and (by simpa using hd8347) (by simp only [List.length_cons]; omega)]
  rw [setFeeProtocolFactoryTarget_eq v] at rd8348Pre
  exact ⟨_, _, rd8348Pre⟩

theorem uniswapV3PoolSetFeeProtocolOwnerCallGuardSetup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8348⟩
      (setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨128⟩ :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8373⟩
      (setFeeProtocolFactoryWord v :: setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  have rd8373 := evm_run h with [
    raw swap2 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8348⟩) (byte := 0x91)
        (op := .SWAP2) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by omega),
    raw push4 ⟨2376452955⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush4 (pc := ⟨8349⟩)
        (n := ⟨2376452955⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 5)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw swap2 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8354⟩) (byte := 0x91)
        (op := .SWAP2) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw push1 ⟨4⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8355⟩)
        (n := ⟨4⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw dup1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8357⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw dup4 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8358⟩) (byte := 0x83)
        (op := .DUP4) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw add (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8359⟩) (byte := 0x01)
        (op := .ADD) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw swap3 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8360⟩) (byte := 0x92)
        (op := .SWAP3) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw push1 ⟨32⟩ (by
      exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8361⟩)
        (n := ⟨32⟩) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide)) (by simp only [List.length_cons]; omega),
    raw swap3 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8363⟩) (byte := 0x92)
        (op := .SWAP3) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw swap2 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8364⟩) (byte := 0x91)
        (op := .SWAP2) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw swap1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8365⟩) (byte := 0x90)
        (op := .SWAP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw dup3 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8366⟩) (byte := 0x82)
        (op := .DUP3) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw swap1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8367⟩) (byte := 0x90)
        (op := .SWAP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw sub (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8368⟩) (byte := 0x03)
        (op := .SUB) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw add (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8369⟩) (byte := 0x01)
        (op := .ADD) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw dup2 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8370⟩) (byte := 0x81)
        (op := .DUP2) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega),
    raw dup7 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8371⟩) (byte := 0x86)
        (op := .DUP7) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by omega),
    raw dup1 (by
      refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8372⟩) (byte := 0x80)
        (op := .DUP1) hpatch (by native_decide)
        (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
          (by native_decide) (by native_decide))
        (by native_decide) (by native_decide) (by native_decide))
      (by simp only [List.length_cons]; omega)]
  exact ⟨_, _, rd8373⟩

private theorem uniswapV3PoolPatchPreservesJumpDest8385 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8385⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8405 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8405⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8427 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8427⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8449 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8449⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8385 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8385⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8385

theorem uniswapV3PoolJumpDestPatched8405 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8405⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8405

theorem uniswapV3PoolJumpDestPatched8427 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8427⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8427

theorem uniswapV3PoolJumpDestPatched8449 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8449⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8449

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerExtcodesizeMissingReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8373⟩
      (setFeeProtocolFactoryWord v :: setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (setFeeProtocolFactoryWord v) = ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    RDrev code g s0 := by
  have hd8373 : decode code ⟨8373⟩ = some (.EXTCODESIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8373⟩) (byte := 0x3b)
      (op := .EXTCODESIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8374 : decode code ⟨8374⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8374⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8375 : decode code ⟨8375⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8375⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8376 : decode code ⟨8376⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8376⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8377 : decode code ⟨8377⟩ = some (.Push .PUSH2, some (⟨8385⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8377⟩)
      (n := ⟨8385⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8380 : decode code ⟨8380⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8380⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8381 : decode code ⟨8381⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8381⟩)
      (n := ⟨0⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8383 : decode code ⟨8383⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8383⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8384 : decode code ⟨8384⟩ = some (.REVERT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8384⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨8373⟩) (okPc := ⟨8385⟩) h
    hcodeSize hd8373 (by simpa using hd8374) (by simpa using hd8375)
    (by simpa using hd8376) (by simpa using hd8377) (by simpa using hd8380)
    (by simpa using hd8381) (by simpa using hd8383) (by simpa using hd8384)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerStaticcallMade {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8373⟩
      (setFeeProtocolFactoryWord v :: setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (setFeeProtocolFactoryWord v) ≠ ⟨0⟩)
    (hdepth : ee.depth.val < 1024)
    (hov : R.length + 11 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (setFeeProtocolFactoryWord v))
          (toExecute σ (AccountAddress.ofUInt256 (setFeeProtocolFactoryWord v)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          (setFeeProtocolOwnerCallMem.readWithPadding 128 4) (ee.depth + 1) ee.header false)
      ∧ RD code ee g s0 ⟨8389⟩
          ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: ⟨2376452955⟩ ::
            setFeeProtocolFactoryWord v :: R)
          (setFeeProtocolOwnerStaticcallMem o) setFeeProtocolOwnerStaticcallActiveWords o
          (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  have hd8373 : decode code ⟨8373⟩ = some (.EXTCODESIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8373⟩) (byte := 0x3b)
      (op := .EXTCODESIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8374 : decode code ⟨8374⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8374⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8375 : decode code ⟨8375⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8375⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8376 : decode code ⟨8376⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8376⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8377 : decode code ⟨8377⟩ = some (.Push .PUSH2, some (⟨8385⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8377⟩)
      (n := ⟨8385⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8380 : decode code ⟨8380⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8380⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8385 : decode code ⟨8385⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8385⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8386 : decode code ⟨8386⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8386⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8387 : decode code ⟨8387⟩ = some (.GAS, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8387⟩) (byte := 0x5a)
      (op := .GAS) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8388 : decode code ⟨8388⟩ = some (.STATICCALL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8388⟩) (byte := 0xfa)
      (op := .STATICCALL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨gasWord, kGas, CGas, rd8388⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨8373⟩) (okPc := ⟨8385⟩) h hcodeSize
      hd8373 (by simpa using hd8374) (by simpa using hd8375) (by simpa using hd8376)
      (by simpa using hd8377) (by simpa using hd8380)
      (uniswapV3PoolJumpDestPatched8385 hpatch) (by simpa using hd8385)
      (by simpa using hd8386) (by simpa using hd8387)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd8389, hoSize⟩ :=
    RD.uniswapStaticcall rd8388 (by simpa using hd8388) hdepth
      (by simp only [List.length_cons]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    hΘ,
    by
      simpa [setFeeProtocolOwnerStaticcallMem, setFeeProtocolOwnerStaticcallActiveWords]
        using rd8389,
    hoSize⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerTypedStaticcallMade {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hs0Genesis : s0.genesisBlockHeader = gh)
    (hs0Blocks : s0.blocks = bl)
    (hs0Original : s0.σ₀ = σ₀)
    (h : RD code I g s0 ⟨8373⟩
      (setFeeProtocolFactoryWord v :: setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (setFeeProtocolFactoryWord v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 11 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨8389⟩
          ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: ⟨2376452955⟩ ::
            setFeeProtocolFactoryWord v :: R)
          (setFeeProtocolOwnerStaticcallMem o) setFeeProtocolOwnerStaticcallActiveWords o
          (cA', σ') k' C'
      ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
          (EVM.address (AccountAddress.ofNat v.factory.toNat)) "owner" 0 []
          (z,
            { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' },
            o) false
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd8389, hoSize⟩ :=
    uniswapV3PoolSetFeeProtocolOwnerStaticcallMade (v := v) (code := code)
      (ee := I) (g := g) (s0 := s0)
      (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hcodeSize hdepth hov
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k', C', rd8389, ?_, hoSize⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := setFeeProtocolFactoryWord v)
    (mem := setFeeProtocolOwnerCallMem) (inOff := ⟨128⟩) (inSize := ⟨4⟩)
    (fun hdepthEq =>
      absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from hdepthEq]
        decide))
    (by
      have hAddressId (a : AccountAddress) : EVM.address a = a := by
        apply Fin.ext
        show ↑a % EVM.twoPow 160 = ↑a
        rw [Nat.mod_eq_of_lt]
        exact a.isLt
      rw [setFeeProtocolFactoryAddress_eq]
      exact hAddressId (AccountAddress.ofNat v.factory.toNat))
    (setFeeProtocolOwnerCallMem_encode_owner (v := v))
    (by simpa [initState, hs0Genesis, hs0Blocks, hs0Original] using hΘ)

theorem uniswapV3PoolSetFeeProtocolOwnerStaticcallStatusGuard {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {o mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {z : Bool}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8389⟩
      ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: ⟨2376452955⟩ ::
        setFeeProtocolFactoryWord v :: R)
      mem aw o acc k C)
    (hoSize : o.size < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    (z = true →
      ∃ k' C', RD code ee g s0 ⟨8407⟩
        (⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
        mem aw o acc k' C') ∧
    (z = false → RDrev code g s0) := by
  have hd8389 : decode code ⟨8389⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8389⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8390 : decode code ⟨8390⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8390⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8391 : decode code ⟨8391⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8391⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8392 : decode code ⟨8392⟩ = some (.Push .PUSH2, some (⟨8405⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8392⟩)
      (n := ⟨8405⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8395 : decode code ⟨8395⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8395⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8396 : decode code ⟨8396⟩ = some (.RETURNDATASIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8396⟩) (byte := 0x3d)
      (op := .RETURNDATASIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8397 : decode code ⟨8397⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8397⟩)
      (n := ⟨0⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8399 : decode code ⟨8399⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8399⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8400 : decode code ⟨8400⟩ = some (.RETURNDATACOPY, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8400⟩) (byte := 0x3e)
      (op := .RETURNDATACOPY) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8401 : decode code ⟨8401⟩ = some (.RETURNDATASIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8401⟩) (byte := 0x3d)
      (op := .RETURNDATASIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8402 : decode code ⟨8402⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8402⟩)
      (n := ⟨0⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8404 : decode code ⟨8404⟩ = some (.REVERT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8404⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8405 : decode code ⟨8405⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8405⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8406 : decode code ⟨8406⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8406⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  constructor
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    exact RD.uniswapCallSuccessGuardOk (pc := ⟨8389⟩) (okPc := ⟨8405⟩) h hstatus
      hd8389 (by simpa using hd8390) (by simpa using hd8391) (by simpa using hd8392)
      (by simpa using hd8395) (uniswapV3PoolJumpDestPatched8405 hpatch)
      (by simpa using hd8405) (by simpa using hd8406)
      (by simp only [List.length_cons]; omega)
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      rw [hz]
      rfl
    refine RD.uniswapCallSuccessGuardMissing (pc := ⟨8389⟩) (okPc := ⟨8405⟩) h hstatus
      hd8389 (by simpa using hd8390) (by simpa using hd8391) (by simpa using hd8392)
      (by simpa using hd8395) (by simpa using hd8396) (by simpa using hd8397)
      (by simpa using hd8399) (by simpa using hd8400) (by simpa using hd8401)
      (by simpa using hd8402) (by simpa using hd8404) ?_ ?_
    · exact hoSize
    · simp only [List.length_cons]
      omega
  
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerReturnDecodeShortReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8407⟩
      (⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      (setFeeProtocolOwnerStaticcallMem o) setFeeProtocolOwnerStaticcallActiveWords o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have hd8407 : decode code ⟨8407⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8407⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8408 : decode code ⟨8408⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8408⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8409 : decode code ⟨8409⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8409⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8410 : decode code ⟨8410⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8410⟩)
      (n := ⟨64⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8412 : decode code ⟨8412⟩ = some (.MLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8412⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8413 : decode code ⟨8413⟩ = some (.RETURNDATASIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8413⟩) (byte := 0x3d)
      (op := .RETURNDATASIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8414 : decode code ⟨8414⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8414⟩)
      (n := ⟨32⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8416 : decode code ⟨8416⟩ = some (.DUP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8416⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8417 : decode code ⟨8417⟩ = some (.LT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8417⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8418 : decode code ⟨8418⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8418⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8419 : decode code ⟨8419⟩ = some (.Push .PUSH2, some (⟨8427⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8419⟩)
      (n := ⟨8427⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8422 : decode code ⟨8422⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8422⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8423 : decode code ⟨8423⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8423⟩)
      (n := ⟨0⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8425 : decode code ⟨8425⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8425⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8426 : decode code ⟨8426⟩ = some (.REVERT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8426⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  exact RD.solcUint256ReturnWordDecodeShortReverts h hshort hhi
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    (by native_decide)
    (setFeeProtocolOwnerStaticcallMem_mload64_of_size_lt o hshort hhi)
    hd8407
    (by simpa [show (⟨8407⟩ : UInt256) + ⟨1⟩ = ⟨8408⟩ by native_decide] using hd8408)
    (by simpa [show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨8409⟩ by native_decide]
      using hd8409)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8410⟩ by native_decide]
      using hd8410)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 =
          ⟨8412⟩ by native_decide]
      using hd8412)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ =
          ⟨8413⟩ by native_decide]
      using hd8413)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ = ⟨8414⟩ by native_decide]
      using hd8414)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 = ⟨8416⟩ by native_decide]
      using hd8416)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨8417⟩ by native_decide]
      using hd8417)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨8418⟩ by native_decide]
      using hd8418)
    (by simpa [
        show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8419⟩ by native_decide]
      using hd8419)
    (by simpa [
        show ((⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3 =
          ⟨8422⟩ by native_decide]
      using hd8422)
    (by simpa [
        show (((⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
              ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) +
            UInt256.ofNat 3) + ⟨1⟩ = ⟨8423⟩ by native_decide]
      using hd8423)
    (by simpa [
        show ((((⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
                ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) +
              UInt256.ofNat 3) + ⟨1⟩) + UInt256.ofNat 2 = ⟨8425⟩ by native_decide]
      using hd8425)
      (by simpa [
          show (((((⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
                    ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) +
                  UInt256.ofNat 3) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩ =
            ⟨8426⟩ by native_decide]
        using hd8426)
      hov
  
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerReturnDecodeOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8407⟩
      (⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      (setFeeProtocolOwnerStaticcallMem o) setFeeProtocolOwnerStaticcallActiveWords o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8430⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
      (setFeeProtocolOwnerStaticcallMem o) setFeeProtocolOwnerStaticcallActiveWords o acc k' C' := by
  have hd8407 : decode code ⟨8407⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8407⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8408 : decode code ⟨8408⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8408⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8409 : decode code ⟨8409⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8409⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8410 : decode code ⟨8410⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8410⟩)
      (n := ⟨64⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8412 : decode code ⟨8412⟩ = some (.MLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8412⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8413 : decode code ⟨8413⟩ = some (.RETURNDATASIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8413⟩) (byte := 0x3d)
      (op := .RETURNDATASIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8414 : decode code ⟨8414⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8414⟩)
      (n := ⟨32⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8416 : decode code ⟨8416⟩ = some (.DUP2, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8416⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8417 : decode code ⟨8417⟩ = some (.LT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8417⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8418 : decode code ⟨8418⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8418⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8419 : decode code ⟨8419⟩ = some (.Push .PUSH2, some (⟨8427⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8419⟩)
      (n := ⟨8427⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8422 : decode code ⟨8422⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8422⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8427 : decode code ⟨8427⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8427⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8428 : decode code ⟨8428⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8428⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8429 : decode code ⟨8429⟩ = some (.MLOAD, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8429⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  simpa [show (⟨8427⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8430⟩ by native_decide]
    using RD.solcUint256ReturnWordDecodeOk h hlo hhi
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      (setFeeProtocolOwnerStaticcallMem_mload64_of_size_ge o hlo hhi)
      (setFeeProtocolOwnerStaticcallMem_mload128_of_size_ge o hlo hhi)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
        native_decide)
      (by native_decide)
      hd8407
      (by simpa [show (⟨8407⟩ : UInt256) + ⟨1⟩ = ⟨8408⟩ by native_decide] using hd8408)
      (by simpa [show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨8409⟩ by native_decide]
        using hd8409)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8410⟩ by native_decide]
        using hd8410)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 =
            ⟨8412⟩ by native_decide]
        using hd8412)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ =
            ⟨8413⟩ by native_decide]
        using hd8413)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ = ⟨8414⟩ by native_decide]
        using hd8414)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 2 = ⟨8416⟩ by native_decide]
        using hd8416)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨8417⟩ by native_decide]
        using hd8417)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ = ⟨8418⟩ by native_decide]
        using hd8418)
      (by simpa [
          show (⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
            ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8419⟩ by native_decide]
        using hd8419)
      (by simpa [
          show ((⟨8407⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
              ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3 =
            ⟨8422⟩ by native_decide]
        using hd8422)
      (uniswapV3PoolJumpDestPatched8427 hpatch)
      hd8427
      (by simpa [show (⟨8427⟩ : UInt256) + ⟨1⟩ = ⟨8428⟩ by native_decide] using hd8428)
      (by simpa [show (⟨8427⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨8429⟩ by native_decide]
        using hd8429)
      hov

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerCallerGuardOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {owner : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8430⟩ (owner :: R) mem aw rdata acc k C)
    (hcaller : UInt256.land solcAddrMask owner = solcSourceWord ee)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8449⟩ R mem aw rdata acc k' C' := by
  have hd8430 : decode code ⟨8430⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8430⟩)
      (n := ⟨1⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8432 : decode code ⟨8432⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8432⟩)
      (n := ⟨1⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8434 : decode code ⟨8434⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8434⟩)
      (n := ⟨160⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8436 : decode code ⟨8436⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8436⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8437 : decode code ⟨8437⟩ = some (.SUB, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8437⟩) (byte := 0x03)
      (op := .SUB) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8438 : decode code ⟨8438⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8438⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8439 : decode code ⟨8439⟩ = some (.CALLER, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8439⟩) (byte := 0x33)
      (op := .CALLER) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8440 : decode code ⟨8440⟩ = some (.EQ, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8440⟩) (byte := 0x14)
      (op := .EQ) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8441 : decode code ⟨8441⟩ = some (.Push .PUSH2, some (⟨8449⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8441⟩)
      (n := ⟨8449⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8444 : decode code ⟨8444⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8444⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    exact setFeeProtocolFactoryMask_eq_solcAddrMask
  have heq :
      UInt256.eq (solcSourceWord ee) (UInt256.land solcAddrMask owner) ≠ ⟨0⟩ := by
    rw [hcaller, u256_eq_refl]
    decide
  have rd8444 := evm_run h with [
    raw push1 ⟨1⟩ hd8430 (by evm_ov),
    raw push1 ⟨1⟩ hd8432 (by evm_ov),
    raw push1 ⟨160⟩ hd8434 (by evm_ov),
    raw shl hd8436 (by evm_ov),
    raw sub hd8437 (by evm_ov),
    raw and hd8438 (by evm_ov),
    raw caller hd8439 (by evm_ov),
    raw eq hd8440 (by evm_ov),
    raw push2 ⟨8449⟩ hd8441 (by evm_ov)]
  rw [hmask] at rd8444
  have rd8449 := rd8444.jumpiT hd8444 heq (uniswapV3PoolJumpDestPatched8449 hpatch)
    (by evm_ov)
  exact ⟨_, _, rd8449⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerCallerGuardReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {owner : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8430⟩ (owner :: R) mem aw rdata acc k C)
    (hcaller : UInt256.land solcAddrMask owner ≠ solcSourceWord ee)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have hd8430 : decode code ⟨8430⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8430⟩)
      (n := ⟨1⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8432 : decode code ⟨8432⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8432⟩)
      (n := ⟨1⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8434 : decode code ⟨8434⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8434⟩)
      (n := ⟨160⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8436 : decode code ⟨8436⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8436⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8437 : decode code ⟨8437⟩ = some (.SUB, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8437⟩) (byte := 0x03)
      (op := .SUB) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8438 : decode code ⟨8438⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8438⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8439 : decode code ⟨8439⟩ = some (.CALLER, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8439⟩) (byte := 0x33)
      (op := .CALLER) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8440 : decode code ⟨8440⟩ = some (.EQ, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8440⟩) (byte := 0x14)
      (op := .EQ) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8441 : decode code ⟨8441⟩ = some (.Push .PUSH2, some (⟨8449⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8441⟩)
      (n := ⟨8449⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8444 : decode code ⟨8444⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8444⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8445 : decode code ⟨8445⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 (pc := ⟨8445⟩)
      (n := ⟨0⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 2)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8447 : decode code ⟨8447⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8447⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8448 : decode code ⟨8448⟩ = some (.REVERT, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8448⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    exact setFeeProtocolFactoryMask_eq_solcAddrMask
  have heq :
      UInt256.eq (solcSourceWord ee) (UInt256.land solcAddrMask owner) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hcaller hbad.symm
  have rd8444 := evm_run h with [
    raw push1 ⟨1⟩ hd8430 (by evm_ov),
    raw push1 ⟨1⟩ hd8432 (by evm_ov),
    raw push1 ⟨160⟩ hd8434 (by evm_ov),
    raw shl hd8436 (by evm_ov),
    raw sub hd8437 (by evm_ov),
    raw and hd8438 (by evm_ov),
    raw caller hd8439 (by evm_ov),
    raw eq hd8440 (by evm_ov),
    raw push2 ⟨8449⟩ hd8441 (by evm_ov)]
  rw [hmask, heq] at rd8444
  have rd8445 := rd8444.jumpiNT hd8444 (by decide) (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd8445 hd8445
    (by simpa [show (⟨8445⟩ : UInt256) + UInt256.ofNat 2 = ⟨8447⟩ by native_decide]
      using hd8447)
    (by simpa [
        show (⟨8445⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ = ⟨8448⟩ by native_decide]
      using hd8448)
    (by omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolOwnerStaticcallDepthLimitReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8373⟩
      (setFeeProtocolFactoryWord v :: setFeeProtocolFactoryWord v :: ⟨128⟩ :: ⟨4⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨132⟩ :: ⟨2376452955⟩ :: setFeeProtocolFactoryWord v :: R)
      setFeeProtocolOwnerCallMem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (setFeeProtocolFactoryWord v) ≠ ⟨0⟩)
    (hdepth : ee.depth = 1024)
    (hov : R.length + 11 ≤ 1024) :
    RDrev code g s0 := by
  have hd8373 : decode code ⟨8373⟩ = some (.EXTCODESIZE, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8373⟩) (byte := 0x3b)
      (op := .EXTCODESIZE) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8374 : decode code ⟨8374⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8374⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8375 : decode code ⟨8375⟩ = some (.DUP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8375⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8376 : decode code ⟨8376⟩ = some (.ISZERO, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8376⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8377 : decode code ⟨8377⟩ = some (.Push .PUSH2, some (⟨8385⟩, 2)) := by
    exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 (pc := ⟨8377⟩)
      (n := ⟨8385⟩) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 3)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd8380 : decode code ⟨8380⟩ = some (.JUMPI, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8380⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8385 : decode code ⟨8385⟩ = some (.JUMPDEST, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8385⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8386 : decode code ⟨8386⟩ = some (.POP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8386⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8387 : decode code ⟨8387⟩ = some (.GAS, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8387⟩) (byte := 0x5a)
      (op := .GAS) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hd8388 : decode code ⟨8388⟩ = some (.STATICCALL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨8388⟩) (byte := 0xfa)
      (op := .STATICCALL) hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory (n := 1)
        (by native_decide) (by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, _, rd8388⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨8373⟩) (okPc := ⟨8385⟩) h hcodeSize
      hd8373 (by simpa using hd8374) (by simpa using hd8375) (by simpa using hd8376)
      (by simpa using hd8377) (by simpa using hd8380)
      (uniswapV3PoolJumpDestPatched8385 hpatch) (by simpa using hd8385)
      (by simpa using hd8386) (by simpa using hd8387)
      (by simp only [List.length_cons]; omega)
  obtain ⟨kDepth, CDepth, rd8389⟩ :=
    RD.uniswapStaticcallDepthLimit rd8388 (by simpa using hd8388) hdepth
      (by simp only [List.length_cons]; omega)
  have rd8389' : RD code ee g s0 ⟨8389⟩
      ((if false then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨132⟩ :: ⟨2376452955⟩ ::
        setFeeProtocolFactoryWord v :: R)
      (ByteArray.empty.write 0 setFeeProtocolOwnerCallMem (⟨128⟩ : UInt256).toNat
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat (MachineState.M
        (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
          (⟨4⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat))
      ByteArray.empty (cA, σ) kDepth CDepth := by
    simpa [show (⟨8385⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8389⟩ by
      native_decide] using rd8389
  obtain ⟨_, hRevert⟩ :=
    uniswapV3PoolSetFeeProtocolOwnerStaticcallStatusGuard (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (R := R) (o := ByteArray.empty)
      hpatch rd8389' (by native_decide) (by omega)
  exact hRevert rfl

end Benchmarks.UniswapV3Pool
