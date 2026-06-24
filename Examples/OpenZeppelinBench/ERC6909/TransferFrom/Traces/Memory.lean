import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

theorem erc6909ScratchMem_mload64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ base.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (base.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [hbase]; decide) (by decide) hread64

noncomputable def solcReturnBaseMem (base : ByteArray) (selector : UInt256) : ByteArray :=
  (UInt256.toByteArray selector).write 0 base 128 32

noncomputable def approveErrorBaseMem (base : ByteArray) (selector arg : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnBaseMem base selector) 132 32

theorem solcReturnBaseMem_size {base : ByteArray} (selector : UInt256)
    (hbase : base.size = 96) :
    (solcReturnBaseMem base selector).size = 160 := by
  unfold solcReturnBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem solcReturnBaseMem_read64 {base : ByteArray} (selector : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcReturnBaseMem base selector).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcReturnBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem approveErrorBaseMem_size {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96) :
    (approveErrorBaseMem base selector arg).size = 164 := by
  unfold approveErrorBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnBaseMem_size selector hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcReturnBaseMem_size selector hbase,
    toByteArray_size]
  omega

theorem approveErrorBaseMem_read64 {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (approveErrorBaseMem base selector arg).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveErrorBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnBaseMem_size selector hbase]; omega) (by omega),
    solcReturnBaseMem_read64 selector hbase hread64]

theorem approveErrorBaseMem_mload64 {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveErrorBaseMem base selector arg).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveErrorBaseMem base selector arg).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveErrorBaseMem_size selector arg hbase]; decide)
    (by decide) (approveErrorBaseMem_read64 selector arg hbase hread64)

noncomputable def transferInsufficientBalanceSelectorBaseMem
    (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferInsufficientBalanceSelectorWord).write 0 base 128 32

noncomputable def transferInsufficientBalanceSenderBaseMem
    (base : ByteArray) (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0
    (transferInsufficientBalanceSelectorBaseMem base) 132 32

noncomputable def transferInsufficientBalanceBalanceBaseMem
    (base : ByteArray) (owner balance : UInt256) : ByteArray :=
  (UInt256.toByteArray balance).write 0
    (transferInsufficientBalanceSenderBaseMem base owner) 164 32

noncomputable def transferInsufficientBalanceAmountBaseMem
    (base : ByteArray) (owner balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (transferInsufficientBalanceBalanceBaseMem base owner balance) 196 32

noncomputable def transferInsufficientBalanceIdBaseMem
    (base : ByteArray) (owner id balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0
    (transferInsufficientBalanceAmountBaseMem base owner balance amount) 228 32

theorem transferInsufficientBalanceSelectorBaseMem_size {base : ByteArray}
    (hbase : base.size = 96) :
    (transferInsufficientBalanceSelectorBaseMem base).size = 160 := by
  unfold transferInsufficientBalanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferInsufficientBalanceSenderBaseMem_size {base : ByteArray}
    (owner : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceSenderBaseMem base owner).size = 164 := by
  unfold transferInsufficientBalanceSenderBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorBaseMem_size hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceSelectorBaseMem_size hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceBalanceBaseMem_size {base : ByteArray}
    (owner balance : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceBalanceBaseMem base owner balance).size = 196 := by
  unfold transferInsufficientBalanceBalanceBaseMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderBaseMem_size owner hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceSenderBaseMem_size owner hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceAmountBaseMem_size {base : ByteArray}
    (owner balance amount : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceAmountBaseMem base owner balance amount).size = 228 := by
  unfold transferInsufficientBalanceAmountBaseMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceBaseMem_size owner balance hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceBalanceBaseMem_size owner balance hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceIdBaseMem_size {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceIdBaseMem base owner id balance amount).size = 260 := by
  unfold transferInsufficientBalanceIdBaseMem
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceSelectorBaseMem_read64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceSelectorBaseMem base).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem transferInsufficientBalanceSenderBaseMem_read64 {base : ByteArray}
    (owner : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceSenderBaseMem base owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSenderBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorBaseMem_size hbase]; omega) (by omega),
    transferInsufficientBalanceSelectorBaseMem_read64 hbase hread64]

theorem transferInsufficientBalanceBalanceBaseMem_read64 {base : ByteArray}
    (owner balance : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceBalanceBaseMem base owner balance).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceBalanceBaseMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderBaseMem_size owner hbase]) (by omega),
    transferInsufficientBalanceSenderBaseMem_read64 owner hbase hread64]

theorem transferInsufficientBalanceAmountBaseMem_read64 {base : ByteArray}
    (owner balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceAmountBaseMem base owner balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceAmountBaseMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceBaseMem_size owner balance hbase])
      (by omega),
    transferInsufficientBalanceBalanceBaseMem_read64 owner balance hbase hread64]

theorem transferInsufficientBalanceIdBaseMem_read64 {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceIdBaseMem base owner id balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceIdBaseMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase])
      (by omega),
    transferInsufficientBalanceAmountBaseMem_read64 owner balance amount hbase hread64]

theorem transferInsufficientBalanceIdBaseMem_mload64 {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferInsufficientBalanceIdBaseMem base owner id balance amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferInsufficientBalanceIdBaseMem base owner id balance amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [transferInsufficientBalanceIdBaseMem_size owner id balance amount hbase]; decide)
    (by decide) (transferInsufficientBalanceIdBaseMem_read64 owner id balance amount hbase hread64)

def transferFromInsufficientAllowanceSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x2c51fead⟩ ⟨225⟩

noncomputable def transferFromInsufficientAllowanceSelectorBaseMem
    (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferFromInsufficientAllowanceSelectorWord).write 0 base 128 32

noncomputable def transferFromInsufficientAllowanceSenderBaseMem
    (base : ByteArray) (sender : UInt256) : ByteArray :=
  (UInt256.toByteArray sender).write 0
    (transferFromInsufficientAllowanceSelectorBaseMem base) 132 32

noncomputable def transferFromInsufficientAllowanceAllowanceBaseMem
    (base : ByteArray) (sender allowance : UInt256) : ByteArray :=
  (UInt256.toByteArray allowance).write 0
    (transferFromInsufficientAllowanceSenderBaseMem base sender) 164 32

noncomputable def transferFromInsufficientAllowanceAmountBaseMem
    (base : ByteArray) (sender allowance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance) 196 32

noncomputable def transferFromInsufficientAllowanceIdBaseMem
    (base : ByteArray) (sender id allowance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount) 228 32

theorem transferFromInsufficientAllowanceSelectorBaseMem_size {base : ByteArray}
    (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceSelectorBaseMem base).size = 160 := by
  unfold transferFromInsufficientAllowanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferFromInsufficientAllowanceSenderBaseMem_size {base : ByteArray}
    (sender : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceSenderBaseMem base sender).size = 164 := by
  unfold transferFromInsufficientAllowanceSenderBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorBaseMem_size hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceSelectorBaseMem_size hbase, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceAllowanceBaseMem_size {base : ByteArray}
    (sender allowance : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance).size = 196 := by
  unfold transferFromInsufficientAllowanceAllowanceBaseMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSenderBaseMem_size sender hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceSenderBaseMem_size sender hbase, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceAmountBaseMem_size {base : ByteArray}
    (sender allowance amount : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount).size = 228 := by
  unfold transferFromInsufficientAllowanceAmountBaseMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase,
    toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceIdBaseMem_size {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).size = 260 := by
  unfold transferFromInsufficientAllowanceIdBaseMem
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase,
    toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceSelectorBaseMem_read64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceSelectorBaseMem base).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem transferFromInsufficientAllowanceSenderBaseMem_read64 {base : ByteArray}
    (sender : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceSenderBaseMem base sender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceSenderBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorBaseMem_size hbase]; omega) (by omega),
    transferFromInsufficientAllowanceSelectorBaseMem_read64 hbase hread64]

theorem transferFromInsufficientAllowanceAllowanceBaseMem_read64 {base : ByteArray}
    (sender allowance : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceAllowanceBaseMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSenderBaseMem_size sender hbase])
      (by omega),
    transferFromInsufficientAllowanceSenderBaseMem_read64 sender hbase hread64]

theorem transferFromInsufficientAllowanceAmountBaseMem_read64 {base : ByteArray}
    (sender allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceAmountBaseMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase])
      (by omega),
    transferFromInsufficientAllowanceAllowanceBaseMem_read64 sender allowance hbase hread64]

theorem transferFromInsufficientAllowanceIdBaseMem_read64 {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceIdBaseMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase])
      (by omega),
    transferFromInsufficientAllowanceAmountBaseMem_read64 sender allowance amount hbase hread64]

theorem transferFromInsufficientAllowanceIdBaseMem_mload64 {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [transferFromInsufficientAllowanceIdBaseMem_size sender id allowance amount hbase]; decide)
    (by decide)
    (transferFromInsufficientAllowanceIdBaseMem_read64 sender id allowance amount hbase hread64)

/-! ## EVM ABI decode trace for `transferFrom(address,address,uint256,uint256)` -/

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP7` xstep.
theorem erc6909Swap7_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: t)
    (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: gg :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP7, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: t).length - 8 + 8 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Common.lean / Reasoning.Reach: generic `RD.swap7`.
theorem RD.erc6909Swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Swap7_xstep hc hp hdec hs hov)


end OpenZeppelinBench.ERC6909
