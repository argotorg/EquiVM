import Examples.UniswapV2Pair.SkimSecondSafeTransferRuntime
import Examples.UniswapV2Pair.SkimSafeTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dynamic second `_safeTransfer` return-data tails -/

theorem skimSecondSafeTransferReturnDataActiveWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 18).toNat 488 out.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 18 ≤ (488 + out.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((488 + out.size + 31) / 32) * 32 ≤ 488 + out.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 519 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem skimSecondSafeTransferReturnDataActiveWords_toNat_ge (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    18 ≤ (skimSecondSafeTransferReturnDataActiveWords out).toNat := by
  unfold skimSecondSafeTransferReturnDataActiveWords
  have hmul := skimSecondSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 18).toNat 488 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
  unfold MachineState.M
  split
  · norm_num
  · exact Nat.le_max_left _ _

theorem skimSecondSafeTransferReturnDataActiveWords_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    (skimSecondSafeTransferReturnDataActiveWords out).toNat * 32 < UInt256.size := by
  unfold skimSecondSafeTransferReturnDataActiveWords
  have hmul := skimSecondSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
  have hMlt : MachineState.M (UInt256.ofNat 18).toNat 488 out.size < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hmul

theorem skimSecondSafeTransferReturnDataActiveWords_mload64_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩ := by
  intro h
  have hle :
      (skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
        (⟨64⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (skimSecondSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
    show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
  have hge := skimSecondSafeTransferReturnDataActiveWords_toNat_ge out houtSize
  omega

theorem skimSecondSafeTransferReturnDataMem_mload64
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).size
        ∨ (⟨64⟩ : UInt256) ≥ skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      skimSecondSafeTransferReturnDataPtr out := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := skimSecondSafeTransferReturnDataActiveWords out)
    (v := skimSecondSafeTransferReturnDataPtr out)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold skimSecondSafeTransferReturnDataMem
      by_cases hin :
          488 + out.size ≤
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size
      · rw [write_eq_gen out
          (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size = 552 :=
          skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out ho32 hoSize hout2_32 hout2Size
        have hext :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size <
              488 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)
    (skimSecondSafeTransferReturnDataActiveWords_mload64_haw out houtSize)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        skimSecondSafeTransferReturnDataMem_read64 self toWord prevValue value out ho32 hoSize hout2_32 hout2Size houtNe)

theorem skimSecondSafeTransferReturnDataActiveWords_mload456_haw (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    ¬ (⟨456⟩ : UInt256) ≥ skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩ := by
  intro h
  have hle :
      (skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
        (⟨456⟩ : UInt256).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (skimSecondSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
    show (⟨456⟩ : UInt256).toNat = 456 from by decide] at hle
  have hge := skimSecondSafeTransferReturnDataActiveWords_toNat_ge out houtSize
  omega

theorem skimSecondSafeTransferReturnDataActiveWords_mload456_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (skimSecondSafeTransferReturnDataActiveWords out).toNat
          (⟨456⟩ : UInt256).toNat 32) =
      skimSecondSafeTransferReturnDataActiveWords out := by
  have hM :
      MachineState.M (skimSecondSafeTransferReturnDataActiveWords out).toNat
          (⟨456⟩ : UInt256).toNat 32 =
        (skimSecondSafeTransferReturnDataActiveWords out).toNat := by
    rw [show (⟨456⟩ : UInt256).toNat = 456 from by decide]
    simp [MachineState.M]
    have hge := skimSecondSafeTransferReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem skimSecondSafeTransferReturnDataMem_mload456
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255) :
    (if (⟨456⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).size
        ∨ (⟨456⟩ : UInt256) ≥ skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).readWithPadding
          (⟨456⟩ : UInt256).toNat 32))) =
      UInt256.ofNat out.size := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨456⟩ : UInt256)) (aw := skimSecondSafeTransferReturnDataActiveWords out)
    (v := UInt256.ofNat out.size)
    (by
      rw [show (⟨456⟩ : UInt256).toNat = 456 from by decide]
      unfold skimSecondSafeTransferReturnDataMem
      by_cases hin :
          488 + out.size ≤
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size
      · rw [write_eq_gen out
          (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size houtNe le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size = 552 :=
          skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out ho32 hoSize hout2_32 hout2Size
        have hext :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size <
              488 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size houtNe le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)
    (skimSecondSafeTransferReturnDataActiveWords_mload456_haw out houtSize)
    (by
      simpa [show (⟨456⟩ : UInt256).toNat = 456 from by decide] using
        skimSecondSafeTransferReturnDataMem_read456 self toWord prevValue value out ho32 hoSize hout2_32 hout2Size houtNe
          (lt_size_of_lt_sign houtSize))

theorem skimSecondSafeTransferReturnDataMem_mload488
    (self : UInt256) {o : ByteArray} (toWord prevValue : UInt256) {out2 : ByteArray}
    (value : UInt256) (out : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255) :
    (if (⟨488⟩ : UInt256).toNat ≥
          (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).size
        ∨ (⟨488⟩ : UInt256) ≥ skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out).readWithPadding
          (⟨488⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨488⟩ : UInt256).toNat = 488 from by decide]
    let base := skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out
    have hbase : base.size = 552 :=
      skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out ho32 hoSize hout2_32 hout2Size
    unfold skimSecondSafeTransferReturnDataMem
    change UInt256.ofNat
        (fromByteArrayBigEndian ((out.write 0 base 488 out.size).readWithPadding 488 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    by_cases hin : 488 + out.size ≤ base.size
    · rw [write_eq_gen out base 488 out.size (by omega) le_rfl hin]
      rw [ByteArray.append_assoc]
      rw [readWithPadding_eq_extract _ 488 (by
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 488 520 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [show (base.extract 0 488).size = 488 by
        rw [ByteArray.size_extract, hbase]
        omega]
      rw [Nat.sub_self, show 520 - 488 = 32 by omega]
      rw [extract_append_left _ _ 0 32 (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_prefix _ out.size 0 32 (by omega)]
    · have hext : base.size < 488 + out.size := by omega
      rw [write_eq_gen_extend out base 488 out.size (by omega) le_rfl (by rw [hbase]; omega)
          hext]
      rw [readWithPadding_eq_extract _ 488 (by
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega)]
      rw [extract_append_right_window _ _ 488 520 (by
        rw [ByteArray.size_extract, hbase]
        omega)]
      rw [show (base.extract 0 488).size = 488 by
        rw [ByteArray.size_extract, hbase]
        omega]
      rw [Nat.sub_self, show 520 - 488 = 32 by omega]
      rw [extract_prefix _ out.size 0 32 (by omega)]
  · rw [not_or]
    constructor
    · rw [show (⟨488⟩ : UInt256).toNat = 488 from by decide]
      unfold skimSecondSafeTransferReturnDataMem
      by_cases hin :
          488 + out.size ≤
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size
      · rw [write_eq_gen out (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size (by omega) le_rfl hin]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract]
        omega
      · have hbase :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size = 552 :=
          skimSecondSafeTransferReturnDataSizeMem_size self toWord prevValue value out ho32 hoSize hout2_32 hout2Size
        have hext :
            (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out).size <
              488 + out.size := by omega
        rw [write_eq_gen_extend out
          (skimSecondSafeTransferReturnDataSizeMem self o toWord prevValue out2 value out)
          488 out.size (by omega) le_rfl (by rw [hbase]; omega) hext]
        rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
        omega
    · intro h
      have hle :
          (skimSecondSafeTransferReturnDataActiveWords out * ⟨32⟩).toNat ≤
            (⟨488⟩ : UInt256).toNat := h
      rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (skimSecondSafeTransferReturnDataActiveWords_mul32_lt out houtSize),
        show (⟨488⟩ : UInt256).toNat = 488 from by decide] at hle
      unfold skimSecondSafeTransferReturnDataActiveWords at hle
      have hMlt : MachineState.M (UInt256.ofNat 18).toNat 488 out.size < UInt256.size := by
        have hmul := skimSecondSafeTransferReturnDataActiveWords_M_mul32_lt out houtSize
        omega
      rw [UInt256.toNat_ofNat_of_lt hMlt] at hle
      rw [show (UInt256.ofNat 18).toNat = 18 from by decide] at hle
      unfold MachineState.M at hle
      split at hle
      · norm_num at hle
      · have hge : 18 ≤ max 18 ((488 + out.size + 31) / 32) := Nat.le_max_left _ _
        have hcontra : 576 ≤ 488 := by
          calc
            576 = 18 * 32 := by norm_num
            _ ≤ max 18 ((488 + out.size + 31) / 32) * 32 :=
              Nat.mul_le_mul_right 32 hge
            _ ≤ 488 := hle
        norm_num at hcontra

theorem skimSecondSafeTransferReturnDataActiveWords_mload488_same (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    UInt256.ofNat
        (MachineState.M (skimSecondSafeTransferReturnDataActiveWords out).toNat
          (⟨488⟩ : UInt256).toNat 32) =
      skimSecondSafeTransferReturnDataActiveWords out := by
  have hM :
      MachineState.M (skimSecondSafeTransferReturnDataActiveWords out).toNat
          (⟨488⟩ : UInt256).toNat 32 =
        (skimSecondSafeTransferReturnDataActiveWords out).toNat := by
    rw [show (⟨488⟩ : UInt256).toNat = 488 from by decide]
    simp [MachineState.M]
    have hge := skimSecondSafeTransferReturnDataActiveWords_toNat_ge out houtSize
    omega
  rw [hM]
  exact u256_ofNat_toNat _

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel status : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6652⟩
      (⟨456⟩ :: status :: value :: toWord :: token :: ret :: token :: token0 :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out)
      (skimSecondSafeTransferReturnDataActiveWords out) out acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    dsimp [rdsz]
    exact UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro hzero
    have hnat : rdsz.toNat = 0 := by rw [hzero]; rfl
    rw [hrdsz_toNat] at hnat
    exact houtNe hnat
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6608 := rd6607
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat out.size = rdsz from rfl, heq0] at rd6608
  have rd6610 := evm_run rd6608 with [jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd6611 := evm_run rd6610 with [
    raw mload 0 ⟨456⟩ (UInt256.ofNat 18) (by native_decide)
      mem_cost (skimSecondSafeTransferCallMem2_mload64 self toWord prevValue value ho32 hoSize hout2_32 hout2Size)
      (by native_decide) (by evm_ov)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray :=
    (UInt256.toByteArray (UInt256.add ⟨456⟩ rounded)).write 0
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) 64 32
  have rd6626 := evm_run rd6611 with [
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and,
    dup3, add, push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 18) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 456 32
  have rd6629 := evm_run rd6626 with [
    returndatasize, dup3,
    raw mstore 0 mem3 (UInt256.ofNat 18) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd6636 := evm_run rd6629 with [returndatasize, push1 ⟨0⟩, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨456⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat out.size
  have hcopyDest_toNat : copyDest.toNat = 488 := by
    decide
  have hcopyLen_toNat : copyLen.toNat = out.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)
  let mem4 : ByteArray := out.write 0 mem3 copyDest.toNat copyLen.toNat
  have hmem4 :
      mem4 = skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out := by
    simp [mem4, mem3, mem2, copyDest, copyLen, rdsz, rounded,
      skimSecondSafeTransferReturnDataMem, skimSecondSafeTransferReturnDataSizeMem,
      skimSecondSafeTransferReturnDataPtrMem, skimSecondSafeTransferReturnDataPtr,
      skimSafeTransferReturnDataRounded, hcopyDest_toNat, hcopyLen_toNat]
    rfl
  have haw4 :
      UInt256.ofNat
          (MachineState.M (UInt256.ofNat 18).toNat copyDest.toNat copyLen.toNat) =
        skimSecondSafeTransferReturnDataActiveWords out := by
    simp [skimSecondSafeTransferReturnDataActiveWords, copyDest, copyLen,
      hcopyDest_toNat, hcopyLen_toNat]
  have rd6637 := RD.returndatacopy
    (Cₘ (skimSecondSafeTransferReturnDataActiveWords out) - Cₘ (UInt256.ofNat 18))
    mem4
    (skimSecondSafeTransferReturnDataActiveWords out)
    rd6636 (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen,
        skimSecondSafeTransferReturnDataActiveWords, hcopyDest_toNat, hcopyLen_toNat])
    (by rfl)
    haw4
    (by evm_ov)
  have rd6646 := evm_run rd6637 with [push2 ⟨6646⟩, jump (by jump_dest), jumpdest]
  have rd6652 := evm_run rd6646 with [pop, swap2, pop, swap2, pop]
  rw [hmem4] at rd6652
  exact ⟨_, _, by simpa using rd6652⟩




/-! ## Dynamic `_safeTransfer` return-data tails -/

theorem skimSecondSafeTransferReturnDataHugeCopyMemCost_gt_g (g : Sat256) (out : ByteArray)
    (hhi : 2 ^ 255 ≤ out.size) (hlo : out.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 18).toNat 488 out.size)) -
        Cₘ (UInt256.ofNat 18) := by
  let M := MachineState.M (UInt256.ofNat 18).toNat 488 out.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 18) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 18) = 54 from by decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 54 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 18) := by
    omega
  simpa [M] using lt_trans hg hcost

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel status : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (status :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (hhi : 2 ^ 255 ≤ out.size)
    (houtSize : out.size < UInt256.size)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnNonemptyHugeReverts
    (base := (⟨456⟩ : UInt256)) (gasMarker := UInt256.ofNat 18)
    (R := token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
    h houtNe houtSize
    (skimSecondSafeTransferCallMem2_mload64 self toWord prevValue value ho32 hoSize
      hout2_32 hout2Size)
    (by decide)
    (by decide)
    (by
      rw [show (((⟨456⟩ : UInt256) + ⟨32⟩).toNat) = 488 from by decide]
      simpa [skimSecondSafeTransferReturnDataActiveWords] using
        skimSecondSafeTransferReturnDataHugeCopyMemCost_gt_g g out hhi houtSize)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck
      (self := self) (value := value) (toWord := toWord) (token := token)
      (token0 := token0) (ret := ret) (sel := sel) (status := (⟨0⟩ : UInt256))
      h houtNe houtSize ho32 hoSize hout2_32 hout2Size
  exact RD.uniswapSafeTransferReturnNonemptyFailureReverts
    (R := token :: token0 :: toWord :: ⟨570⟩ :: sel :: []) rd6652
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel status : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
      (⟨456⟩ :: status :: value :: toWord :: token :: ret :: token :: token0 :: toWord ::
        ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out)
      (skimSecondSafeTransferReturnDataActiveWords out) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.uniswapSafeTransferReturnFailureMessageFrom6697Reverts
    (R := token :: token0 :: toWord :: ⟨570⟩ :: sel :: []) h (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6676⟩
      (UInt256.ofNat out.size :: ⟨488⟩ :: ⟨456⟩ :: ⟨1⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out)
      (skimSecondSafeTransferReturnDataActiveWords out) out acc k' C' := by
  obtain ⟨_, _, rd6652⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyReturnToCheck
      (self := self) (value := value) (toWord := toWord) (token := token)
      (token0 := token0) (ret := ret) (sel := sel) (status := (⟨1⟩ : UInt256))
      h houtNe houtSize ho32 hoSize hout2_32 hout2Size
  exact RD.uniswapSafeTransferReturnNonemptyTrueStatusToLengthLoaded
    (retPtr := (⟨488⟩ : UInt256)) (R := token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
    rd6652 houtNe houtSize
    (skimSecondSafeTransferReturnDataMem_mload456 self toWord prevValue value out
      ho32 hoSize hout2_32 hout2Size houtNe houtSize)
    (skimSecondSafeTransferReturnDataActiveWords_mload456_same out houtSize)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (hshort : out.size < 32) (houtSize : out.size < 2 ^ 255)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize hout2_32 hout2Size
  exact RD.uniswapSafeTransferReturnNonemptyShortReverts rd6676 hshort houtSize
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword :
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize hout2_32 hout2Size
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have haw488 := skimSecondSafeTransferReturnDataActiveWords_mload488_same out houtSize
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSecondSafeTransferReturnDataActiveWords out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw488])
    (skimSecondSafeTransferReturnDataMem_mload488 self toWord prevValue value out ho32 hoSize hout2_32 hout2Size hout32
      houtSize)
    haw488
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  rw [hword] at rd6692
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  obtain ⟨k6697, C6697, rd6697'⟩ : ∃ k' C',
      RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6697⟩
        (⟨456⟩ :: ⟨1⟩ :: value :: toWord :: token :: ret :: token :: token0 ::
          toWord :: ⟨570⟩ :: sel :: [])
        (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out)
        (skimSecondSafeTransferReturnDataActiveWords out) out acc k' C' := by
    exact ⟨_, _, by simpa using rd6697⟩
  exact RD.uniswapSkimSecondSafeTransferFailureMessageFrom6697Reverts
    rd6697' houtNe houtSize ho32 hoSize hout2_32 hout2Size

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (houtNe : out.size ≠ 0) (hout32 : 32 ≤ out.size) (houtSize : out.size < 2 ^ 255)
    (hword :
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferReturnDataMem self o toWord prevValue out2 value out)
      (skimSecondSafeTransferReturnDataActiveWords out) out acc k' C' := by
  obtain ⟨k6676, C6676, rd6676⟩ :=
    RD.uniswapSkimSecondSafeTransferNonemptyTrueStatusToLengthLoaded
      h houtNe houtSize ho32 hoSize hout2_32 hout2Size
  have rd6684₀ := evm_run rd6676 with [push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨6689⟩]
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign houtSize)]
    exact hout32
  have rd6684 := rd6684₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6684
  have rd6691 := evm_run rd6684 with [jumpiT (by native_decide) (by jump_dest), jumpdest, pop]
  have haw488 := skimSecondSafeTransferReturnDataActiveWords_mload488_same out houtSize
  have rd6692₀ := RD.mload
    0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (skimSecondSafeTransferReturnDataActiveWords out) rd6691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, haw488])
    (skimSecondSafeTransferReturnDataMem_mload488 self toWord prevValue value out ho32 hoSize hout2_32 hout2Size hout32
      houtSize)
    haw488
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6692 := rd6692₀
  have rd6773 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiT hword (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyFailureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨0⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value)
      (UInt256.ofNat 18) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6692 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6697 := evm_run rd6692 with [
    jumpdest, push2 ⟨6773⟩, jumpiNT (by native_decide)]
  let mem0 := skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value
  let aw0 : UInt256 := UInt256.ofNat 18
  let fp0 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ mem0.size ∨ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem0.readWithPadding 64 32))
  let aw1 : UInt256 := UInt256.ofNat (MachineState.M aw0.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6701 := evm_run rd6697 with [push1 ⟨64⟩, dup1]
  have rd6701' := RD.mload
    (Cₘ aw1 - Cₘ aw0) fp0 aw1 rd6701 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0, aw1])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6705 := rd6701'.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd6708 := evm_run rd6705 with [push1 ⟨229⟩, shl, dup2]
  let err0 : ByteArray := (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem0 fp0.toNat 32
  let aw2 : UInt256 := UInt256.ofNat (MachineState.M aw1.toNat fp0.toNat 32)
  have rd6710 := RD.mstore
    (Cₘ aw2 - Cₘ aw1) err0 aw2 rd6708 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, aw2])
    (by simp [err0, mem0, uniswapErrorStringSelector])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6716 := evm_run rd6710 with [push1 ⟨32⟩, push1 ⟨4⟩, dup3, add]
  let off1 : UInt256 := fp0 + ⟨4⟩
  let err1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 err0 off1.toNat 32
  let aw3 : UInt256 := UInt256.ofNat (MachineState.M aw2.toNat off1.toNat 32)
  have rd6717 := RD.mstore
    (Cₘ aw3 - Cₘ aw2) err1 aw3 rd6716 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, aw3, off1])
    (by simp [err1, off1])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6723 := evm_run rd6717 with [push1 ⟨26⟩, push1 ⟨36⟩, dup3, add]
  let off2 : UInt256 := fp0 + ⟨36⟩
  let err2 : ByteArray := (UInt256.toByteArray (⟨26⟩ : UInt256)).write 0 err1 off2.toNat 32
  let aw4 : UInt256 := UInt256.ofNat (MachineState.M aw3.toNat off2.toNat 32)
  have rd6724 := RD.mstore
    (Cₘ aw4 - Cₘ aw3) err2 aw4 rd6723 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3, aw4, off2])
    (by simp [err2, off2])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6757 := rd6724.pushConst uniswapSafeTransferFailedStringWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6760 := evm_run rd6757 with [push1 ⟨68⟩, dup3, add]
  let off3 : UInt256 := fp0 + ⟨68⟩
  let err3 : ByteArray := (UInt256.toByteArray uniswapSafeTransferFailedStringWord).write 0
    err2 off3.toNat 32
  let aw5 : UInt256 := UInt256.ofNat (MachineState.M aw4.toNat off3.toNat 32)
  have rd6762 := RD.mstore
    (Cₘ aw5 - Cₘ aw4) err3 aw5 rd6760 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw4, aw5, off3])
    (by simp [err3, off3])
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6763 := evm_run rd6762 with [swap1]
  let fp1 : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ err3.size ∨ (⟨64⟩ : UInt256) ≥ aw5 * ⟨32⟩ then
      ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (err3.readWithPadding 64 32))
  let aw6 : UInt256 := UInt256.ofNat (MachineState.M aw5.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6764 := RD.mload
    (Cₘ aw6 - Cₘ aw5) fp1 aw6 rd6763 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw5, aw6])
    (by rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6772 := evm_run rd6764 with [
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat
      (MachineState.M aw6.toNat fp1.toNat ((⟨100⟩ : UInt256) + fp0.sub fp1).toNat)) -
      Cₘ aw6)
    rd6772 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by simp only [List.length_cons, List.length_nil]; omega)


set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyReturnToRet {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 ret sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ret :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (hout : out.size = 0)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k' C' := by
  have rd6607 := evm_run h with [
    swap2, pop, pop, returndatasize, dup1, push1 ⟨0⟩, dup2, eq, push2 ⟨6641⟩]
  have rd6607' := rd6607
  rw [hout] at rd6607'
  have rd6641 := evm_run rd6607' with [jumpiT (by native_decide) (by jump_dest)]
  have rd6652 := evm_run rd6641 with [
    jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap2, pop, swap2, pop]
  have rd6658 := evm_run rd6652 with [
    dup2, dup1, iszero, push2 ⟨6692⟩, jumpiNT (by native_decide)]
  have rd6668 := evm_run rd6658 with [
    pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 18) (by native_decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [skimSecondSafeTransferCallMem2_size self toWord prevValue value ho32 hoSize hout2_32 hout2Size]; native_decide)
        (by native_decide)
        (skimSecondSafeTransferCallMem2_read96_zero self toWord prevValue value ho32 hoSize hout2_32 hout2Size))
      (by native_decide) (by evm_ov),
    iszero, dup1, push2 ⟨6692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd6773 := evm_run rd6668 with [jumpdest, push2 ⟨6773⟩,
    jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd6773 with [jumpdest, pop, pop, pop, pop, pop,
    jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {self value toWord prevValue token token0 sel : UInt256}
    {o out2 out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6595⟩
      (⟨1⟩ :: ⟨524⟩ :: UInt256.land token solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
        value :: toWord :: token :: ⟨5433⟩ :: token :: token0 :: toWord :: ⟨570⟩ ::
        sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k C)
    (hout : out.size = 0) (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout2_32 : 32 ≤ out2.size) (hout2Size : out2.size < UInt256.size) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5433⟩
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: [])
      (skimSecondSafeTransferCallMem2 self o toWord prevValue out2 value) (UInt256.ofNat 18) out acc k' C' := by
  exact RD.uniswapSkimSecondSafeTransferEmptyReturnToRet h hout ho32 hoSize hout2_32 hout2Size (by jump_dest)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSkimAfterSecondSafeTransferToReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {token token0 toWord sel : UInt256}
    {mem out : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5433⟩
      (token :: token0 :: toWord :: ⟨570⟩ :: sel :: []) mem aw out (cA, σ) k C)
    (hperm : ee.perm = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0
      (cA, sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨1⟩) ByteArray.empty := by
  have rd5435 := evm_run h with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨12⟩]
  obtain ⟨_, _, rd5441⟩ := rd5435.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd570 := evm_run rd5441 with [pop, jump (by jump_dest), jumpdest]
  exact rd570.stop (by native_decide) (by evm_ov)

end UniswapV2Pair
