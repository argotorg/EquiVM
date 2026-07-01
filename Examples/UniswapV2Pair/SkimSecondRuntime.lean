import Examples.UniswapV2Pair.SkimSafeTransferRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` second `balanceOf` runtime tail -/

noncomputable def skimSecondBalanceSelectorMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0
    (skimSafeTransferCallMem2 self o toWord value) 292 32

noncomputable def skimSecondBalanceCalldataMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray self).write 0
    (skimSecondBalanceSelectorMem self o toWord value) 296 32

noncomputable def skimSecondBalanceStaticcallMem
    (self : UInt256) (o : ByteArray) (toWord value : UInt256) (out : ByteArray) :
    ByteArray :=
  out.write 0 (skimSecondBalanceCalldataMem self o toWord value) 292
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

theorem skimSecondBalanceSelectorMem_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceSelectorMem self o toWord value).size = 388 := by
  unfold skimSecondBalanceSelectorMem
  rw [write32_eq _ _ 292 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize, toByteArray_size]
  norm_num

theorem skimSecondBalanceCalldataMem_size
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceCalldataMem self o toWord value).size = 388 := by
  unfold skimSecondBalanceCalldataMem
  rw [write32_eq _ _ 296 (by rw [toByteArray_size])
      (by rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize, toByteArray_size]
  norm_num

theorem skimSecondBalanceSelectorMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceSelectorMem self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSecondBalanceSelectorMem
  rw [write32_read_below _ _ 292 64 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSafeTransferCallMem2_read64 self toWord value ho32 hoSize

theorem skimSecondBalanceCalldataMem_read64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceCalldataMem self o toWord value).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSecondBalanceCalldataMem
  rw [write32_read_below _ _ 296 64 (by rw [toByteArray_size])
      (by rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize]; native_decide)
      (by omega)]
  exact skimSecondBalanceSelectorMem_read64 self toWord value ho32 hoSize

theorem skimSecondBalanceCalldataMem_mload64
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (skimSecondBalanceCalldataMem self o toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceCalldataMem self o toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; native_decide)
    (by native_decide) (skimSecondBalanceCalldataMem_read64 self toWord value ho32 hoSize)

theorem skimSecondBalanceSelectorMem_read292_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceSelectorMem self o toWord value).readWithPadding 292 4 =
      balanceOfSelector := by
  unfold skimSecondBalanceSelectorMem
  rw [write32_read_prefix_len _ _ 292 4 (by rw [toByteArray_size])
      (by rw [skimSafeTransferCallMem2_size self toWord value ho32 hoSize]; omega)
      (by norm_num) (by norm_num) (by norm_num)]
  native_decide

theorem skimSecondBalanceCalldataMem_read292_4
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceCalldataMem self o toWord value).readWithPadding 292 4 =
      balanceOfSelector := by
  unfold skimSecondBalanceCalldataMem
  rw [write32_read_below_len _ _ 296 292 4 (by rw [toByteArray_size])
      (by rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize]; omega)
      (by omega)
      (by rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize]; omega)
      (by norm_num) (by norm_num)]
  exact skimSecondBalanceSelectorMem_read292_4 self toWord value ho32 hoSize

theorem skimSecondBalanceCalldataMem_read296_32
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceCalldataMem self o toWord value).readWithPadding 296 32 =
      UInt256.toByteArray self := by
  unfold skimSecondBalanceCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [skimSecondBalanceSelectorMem_size self toWord value ho32 hoSize]; omega)]
  rw [show (UInt256.toByteArray self).extract 0 32 = UInt256.toByteArray self by
    rw [show 32 = (UInt256.toByteArray self).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem skimSecondBalanceCalldataMem_read292_36
    (self : UInt256) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (skimSecondBalanceCalldataMem self o toWord value).readWithPadding 292 36 =
      balanceOfSelector ++ UInt256.toByteArray self := by
  rw [byteArray_readWithPadding_split _ 292 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; norm_num)]
  rw [skimSecondBalanceCalldataMem_read292_4 self toWord value ho32 hoSize,
    skimSecondBalanceCalldataMem_read296_32 self toWord value ho32 hoSize]

theorem skimSecondBalanceCalldataMem_encode
    (self : AccountAddress) {o : ByteArray} (toWord value : UInt256)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some ((skimSecondBalanceCalldataMem (UInt256.ofNat self.val) o toWord value)
        |>.readWithPadding 292 36) := by
  rw [skimSecondBalanceCalldataMem_read292_36 _ _ _ ho32 hoSize]
  have h := balanceOfThisCalldataMem_encode self
  rw [balanceOfThisCalldataMem_read128_36] at h
  exact h

theorem skimSecondBalanceStaticcallWriteLen_of_size_ge (out : ByteArray)
    (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
  simpa using
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hhi

theorem skimSecondBalanceStaticcallMem_size_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (skimSecondBalanceStaticcallMem self o toWord value out).size = 388 := by
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out hout32 houtSize]
  rw [write32_eq _ _ 292 hout32
      (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]
  omega

theorem skimSecondBalanceStaticcallMem_read64_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out hout32 houtSize]
  rw [write32_read_below _ _ 292 64 hout32
      (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; omega)
      (by omega)]
  exact skimSecondBalanceCalldataMem_read64 self toWord value ho32 hoSize

theorem skimSecondBalanceStaticcallMem_mload64_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceStaticcallMem self o toWord value out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord value out
        ho32 hoSize hout32 houtSize]
      native_decide)
    (by native_decide)
    (skimSecondBalanceStaticcallMem_read64_of_size_ge self toWord value out
      ho32 hoSize hout32 houtSize)

theorem skimSecondBalanceStaticcallWriteLen_of_size_lt (out : ByteArray)
    (hshort : out.size < 32) (hhi : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hhi

theorem skimSecondBalanceStaticcallMem_size_of_size_lt
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    (skimSecondBalanceStaticcallMem self o toWord value out).size = 388 := by
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_lt out hshort houtSize]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero,
      skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]
  · rw [write_eq_gen _ _ 292 out.size hzero le_rfl
      (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]
    omega

theorem skimSecondBalanceStaticcallMem_read64_of_size_lt
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    (skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding 64 32 =
      UInt256.toByteArray (⟨292⟩ : UInt256) := by
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_lt out hshort houtSize]
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact skimSecondBalanceCalldataMem_read64 self toWord value ho32 hoSize
  · rw [write_read_below_gen _ _ 292 out.size 64 hzero le_rfl
      (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; omega)
      (by omega)]
    exact skimSecondBalanceCalldataMem_read64 self toWord value ho32 hoSize

theorem skimSecondBalanceStaticcallMem_mload64_of_size_lt
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondBalanceStaticcallMem self o toWord value out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨292⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [skimSecondBalanceStaticcallMem_size_of_size_lt self toWord value out
        ho32 hoSize hshort houtSize]
      native_decide)
    (by native_decide)
    (skimSecondBalanceStaticcallMem_read64_of_size_lt self toWord value out
      ho32 hoSize hshort houtSize)

theorem skimSecondBalanceStaticcallMem_read292_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding 292 32 =
      out.extract 0 32 := by
  unfold skimSecondBalanceStaticcallMem
  rw [skimSecondBalanceStaticcallWriteLen_of_size_ge out hout32 houtSize]
  exact write32_read_back _ _ 292 hout32
    (by rw [skimSecondBalanceCalldataMem_size self toWord value ho32 hoSize]; omega)

theorem skimSecondBalanceStaticcallMem_mload292_of_size_ge
    (self : UInt256) {o : ByteArray} (toWord value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨292⟩ : UInt256).toNat ≥
          (skimSecondBalanceStaticcallMem self o toWord value out).size
        ∨ (⟨292⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondBalanceStaticcallMem self o toWord value out).readWithPadding
          (⟨292⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨292⟩ : UInt256).toNat = 292 from by decide,
      skimSecondBalanceStaticcallMem_read292_of_size_ge self toWord value out
        ho32 hoSize hout32 houtSize]
  · rw [not_or]
    constructor
    · rw [skimSecondBalanceStaticcallMem_size_of_size_ge self toWord value out
        ho32 hoSize hout32 houtSize]
      native_decide
    · native_decide

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩ (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceStaticcallMem self o toWord value out) (UInt256.ofNat 13) out
      acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5314⟩
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: R)
      (skimSecondBalanceStaticcallMem self o toWord value out) (UInt256.ofNat 13) out
      acc k' C' := by
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨292⟩ (UInt256.ofNat 13)
    rdPush64 (by native_decide)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    (skimSecondBalanceStaticcallMem_mload64_of_size_ge self toWord value out
      ho32 hoSize hout32 houtSize)
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size houtSize]
    exact hout32
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMload292 := RD.mload 0
    (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) (UInt256.ofNat 13)
    rdPopLen (by native_decide)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    (skimSecondBalanceStaticcallMem_mload292_of_size_ge self toWord value out
      ho32 hoSize hout32 houtSize)
    (by native_decide)
    (by omega)
  exact ⟨_, _, by simpa using rdMload292⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord : UInt256}
    {o out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩ (d0 :: d1 :: d2 :: R)
      (skimSecondBalanceStaticcallMem self o toWord value out) (UInt256.ofNat 13) out
      acc k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rdPop0 := RD.pop h (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide) (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨292⟩ (UInt256.ofNat 13)
    rdPush64 (by native_decide)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    (skimSecondBalanceStaticcallMem_mload64_of_size_lt self toWord value out
      ho32 hoSize hshort houtSize)
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size houtSize]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨5311⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough (by native_decide)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.uniswapSkimSecondBalanceCallFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {mem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
      (status :: R) mem (UInt256.ofNat 13) out acc k C)
    (hstatus : status = ⟨0⟩) (houtSize : out.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) h hstatus
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) houtSize hov

theorem RD.uniswapSkimSecondBalanceCallSuccessToDecode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {mem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status : UInt256} {R : List UInt256}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
      (status :: R) mem (UInt256.ofNat 13) out acc k C)
    (hstatus : status ≠ ⟨0⟩) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5291⟩
      R mem (UInt256.ofNat 13) out acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) h hstatus
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_aw13_free292 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 13) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hmem : mem.size = 388)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨292⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  have rd6895 := evm_run rd6891 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem]; decide) (by native_decide) hread64)
      (by decide) (by evm_ov)]
  let mem0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem 292 32
  have hmem0 : mem0.size = 388 := by
    unfold mem0
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
    omega
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918a := evm_run rd6899 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 (UInt256.ofNat 13)
      (by decide) mem_cost
      (by unfold mem0 uniswapErrorStringSelector; rfl) (by decide) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 296 32
  have hmem1 : mem1.size = 388 := by
    unfold mem1
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem0]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem0, toByteArray_size]
    omega
  have rd6918b := evm_run rd6918a with [
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 mem1 (UInt256.ofNat 13)
      (by decide) mem_cost
      (by unfold mem1; rfl) (by decide) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨21⟩ : UInt256)).write 0 mem1 328 32
  have hmem2 : mem2.size = 388 := by
    unfold mem2
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem1]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem1, toByteArray_size]
    omega
  have rd6918 := evm_run rd6918b with [
    push1 ⟨21⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 0 mem2 (UInt256.ofNat 13)
      (by decide) mem_cost
      (by unfold mem2; rfl) (by decide) (by evm_ov)]
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  let mem3 : ByteArray :=
    (UInt256.toByteArray uniswapSafeMathSubUnderflowStringWord).write 0 mem2 360 32
  have hmem3 : mem3.size = 392 := by
    unfold mem3
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem2]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem2, toByteArray_size]
    omega
  have hread64_mem0 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨292⟩ := by
    unfold mem0
    rw [write32_read_below _ _ 292 64 (by rw [toByteArray_size])
      (by rw [hmem]; native_decide) (by omega)]
    exact hread64
  have hread64_mem1 :
      mem1.readWithPadding 64 32 = UInt256.toByteArray ⟨292⟩ := by
    unfold mem1
    rw [write32_read_below _ _ 296 64 (by rw [toByteArray_size])
      (by rw [hmem0]; native_decide) (by omega)]
    exact hread64_mem0
  have hread64_mem2 :
      mem2.readWithPadding 64 32 = UInt256.toByteArray ⟨292⟩ := by
    unfold mem2
    rw [write32_read_below _ _ 328 64 (by rw [toByteArray_size])
      (by rw [hmem1]; native_decide) (by omega)]
    exact hread64_mem1
  have hread64_mem3 :
      mem3.readWithPadding 64 32 = UInt256.toByteArray ⟨292⟩ := by
    unfold mem3
    rw [write32_read_below _ _ 360 64 (by rw [toByteArray_size])
      (by rw [hmem2]; native_decide) (by omega)]
    exact hread64_mem2
  exact evm_run rd6940 with [
    push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 0 mem3 (UInt256.ofNat 13)
      (by decide) mem_cost
      (by unfold mem3; rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem3]; decide) (by native_decide) hread64_mem3)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceOfStaticcallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token0 token1 sel : UInt256}
    {o out0 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 (UInt256.ofNat ee.codeOwner.val) o toWord value)
      (UInt256.ofNat 13) out0 (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hdepth : ee.depth.val < 1024)
    (htoken1Code : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) ≠ ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
          (toExecute σ (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceCalldataMem (UInt256.ofNat ee.codeOwner.val) o toWord value)
            |>.readWithPadding 292 36)
          (ee.depth + 1) ee.header false)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5273⟩
          ((if z then (⟨1⟩ : UInt256) else ⟨0⟩) :: ⟨328⟩ ::
            balanceOfSelectorWord :: UInt256.land token1 solcAddrMask ::
            UInt256.land reserve112Mask (UInt256.div (uniswapSlotWord ⟨8⟩ σ ee) reserve112Shift) ::
            ⟨5325⟩ :: toWord :: token1 :: ⟨5433⟩ ::
            token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
          (skimSecondBalanceStaticcallMem (UInt256.ofNat ee.codeOwner.val) o toWord value out)
          (UInt256.ofNat 13) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  let packedWord := uniswapSlotWord ⟨8⟩ σ ee
  let token1Clean := UInt256.land token1 solcAddrMask
  let reserve1Word := UInt256.land reserve112Mask (UInt256.div packedWord reserve112Shift)
  have rd5333 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨k5334, C5334, rd5334₀⟩ := rd5333.sload (by native_decide) (by evm_ov)
  have rd5334 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5334⟩
      (packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 (UInt256.ofNat ee.codeOwner.val) o toWord value)
      (UInt256.ofNat 13) out0 (cA, σ) k5334 C5334 := by
    simpa [packedWord, uniswapSlotWord] using rd5334₀
  have rd5347 := evm_run rd5334 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (skimSafeTransferCallMem2_mload64 (UInt256.ofNat ee.codeOwner.val) toWord value
        ho32 hoSize)
      (by native_decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd5348 := rd5347.mstore 0
    (skimSecondBalanceSelectorMem (UInt256.ofNat ee.codeOwner.val) o toWord value)
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5353 := evm_run rd5348 with [uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd5354 := rd5353.mstore 0
    (skimSecondBalanceCalldataMem (UInt256.ofNat ee.codeOwner.val) o toWord value)
    (UInt256.ofNat 13) (by native_decide) mem_cost
    (by
      rw [show (⟨292⟩ : UInt256) + ⟨4⟩ = ⟨296⟩ by native_decide]
      rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5356 := evm_run rd5354 with [
    swap1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (skimSecondBalanceCalldataMem_mload64 (UInt256.ofNat ee.codeOwner.val) toWord value
        ho32 hoSize)
      (by native_decide) (by evm_ov),
    push2 ⟨5433⟩, swap3, dup5, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5384₀ := evm_run rd5356 with [
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5384 := rd5384₀
  rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.sub reserve112Shift ⟨1⟩ = reserve112Mask from rfl] at rd5384
  have rd5395₀ := evm_run rd5384 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, swap2]
  have rd5395 := rd5395₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5395
  have rd5421₀ := evm_run rd5395 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  have rd5421 := rd5421₀
  rw [show (⟨292⟩ : UInt256) + ⟨36⟩ = ⟨328⟩ from by decide,
    show UInt256.sub (⟨292⟩ : UInt256) ⟨292⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5421
  obtain ⟨gasWord, _, _, rd5272⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨5269⟩) rd5421 htoken1Code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘ, rd5273, houtSize⟩ :=
    RD.uniswapStaticcall rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, out, A_in, callGas, k', C', ?_, ?_, houtSize⟩
  · simpa [token1Clean, skimSecondBalanceStaticcallMem] using hΘ
  · have haw :
        UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 13).toNat 292 36) 292 32) =
          UInt256.ofNat 13 := by
      native_decide
    simpa [packedWord, token1Clean, reserve1Word, reserve112Shift, reserve112Mask,
      skimSecondBalanceStaticcallMem, haw] using rd5273

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondBalanceOfNoCodeReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord token0 token1 sel : UInt256}
    {o out0 : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5330⟩
      (token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 (UInt256.ofNat ee.codeOwner.val) o toWord value)
      (UInt256.ofNat 13) out0 (cA, σ) k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (htoken1NoCode : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let packedWord := uniswapSlotWord ⟨8⟩ σ ee
  let token1Clean := UInt256.land token1 solcAddrMask
  have rd5333 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨k5334, C5334, rd5334₀⟩ := rd5333.sload (by native_decide) (by evm_ov)
  have rd5334 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5334⟩
      (packedWord :: token1 :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSafeTransferCallMem2 (UInt256.ofNat ee.codeOwner.val) o toWord value)
      (UInt256.ofNat 13) out0 (cA, σ) k5334 C5334 := by
    simpa [packedWord, uniswapSlotWord] using rd5334₀
  have rd5347 := evm_run rd5334 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (skimSafeTransferCallMem2_mload64 (UInt256.ofNat ee.codeOwner.val) toWord value
        ho32 hoSize)
      (by native_decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd5348 := rd5347.mstore 0
    (skimSecondBalanceSelectorMem (UInt256.ofNat ee.codeOwner.val) o toWord value)
    (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5353 := evm_run rd5348 with [uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd5354 := rd5353.mstore 0
    (skimSecondBalanceCalldataMem (UInt256.ofNat ee.codeOwner.val) o toWord value)
    (UInt256.ofNat 13) (by native_decide) mem_cost
    (by
      rw [show (⟨292⟩ : UInt256) + ⟨4⟩ = ⟨296⟩ by native_decide]
      rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5356 := evm_run rd5354 with [
    swap1,
    raw mload 0 ⟨292⟩ (UInt256.ofNat 13) (by native_decide)
      mem_cost
      (skimSecondBalanceCalldataMem_mload64 (UInt256.ofNat ee.codeOwner.val) toWord value
        ho32 hoSize)
      (by native_decide) (by evm_ov),
    push2 ⟨5433⟩, swap3, dup5, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5384₀ := evm_run rd5356 with [
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5384 := rd5384₀
  rw [show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.sub reserve112Shift ⟨1⟩ = reserve112Mask from rfl] at rd5384
  have rd5395₀ := evm_run rd5384 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, swap2]
  have rd5395 := rd5395₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5395
  have rd5421₀ := evm_run rd5395 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  have rd5421 := rd5421₀
  rw [show (⟨292⟩ : UInt256) + ⟨36⟩ = ⟨328⟩ from by decide,
    show UInt256.sub (⟨292⟩ : UInt256) ⟨292⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5421
  exact RD.uniswapExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5421 htoken1NoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
