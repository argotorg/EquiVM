import Solidity.Examples.ERC20.Transfer

/-!
# ERC20 — `transferFrom(address,address,uint256)` refines its Solidity body

Outcomes: the two `require` failures (`Error("ERC20: insufficient allowance")`,
`Error("ERC20: insufficient balance")`), the debit's underflow and the credit's overflow
(`Panic(0x11)`; the debit re-reads `balanceOf[from]` after the allowance store, so its check is
decided again rather than taken from the `require`), and success.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM runs -/

theorem tfEntry {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2)) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x45f⟩, ⟨4⟩ :: UInt256.ofNat (initState cA gh bl σ σ₀ g A I).executionEnv.calldata.size :: ⟨0xb1⟩ :: ⟨0x77⟩ ::
        [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := reachBodyOf 2 (by omega) ⟨0xa3⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨0x77⟩, push2 ⟨0xb1⟩, calldatasize, push1 ⟨4⟩, push2 ⟨0x45f⟩,
    jump (by jump_dest)]⟩

abbrev tfFrom (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev tfTo (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
abbrev tfValue (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 68
abbrev tfS1 (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨1⟩ (tfFrom I)
/-- `allowance[from][msg.sender]`, `balanceOf[from]`, `balanceOf[to]`. -/
abbrev tfSA (I : ExecutionEnv) : UInt256 := solcMappingSlot (tfS1 I) (callerW I)
abbrev tfSF (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨0⟩ (tfFrom I)
abbrev tfST (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨0⟩ (tfTo I)
abbrev tfAlw (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord σ I (tfSA I)
abbrev tfBalF (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord σ I (tfSF I)
abbrev tfNewAlw (I : ExecutionEnv) (σ : AccountMap) : UInt256 := UInt256.sub (tfAlw I σ) (tfValue I)
abbrev tfW1 (I : ExecutionEnv) (σ : AccountMap) : AccountMap := sstoreAccountMap I.codeOwner σ (tfSA I) (tfNewAlw I σ)
abbrev tfBalF1 (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord (tfW1 I σ) I (tfSF I)
abbrev tfDiff (I : ExecutionEnv) (σ : AccountMap) : UInt256 := UInt256.sub (tfBalF1 I σ) (tfValue I)
abbrev tfW2 (I : ExecutionEnv) (σ : AccountMap) : AccountMap := sstoreAccountMap I.codeOwner (tfW1 I σ) (tfSF I) (tfDiff I σ)
abbrev tfBalT (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord (tfW2 I σ) I (tfST I)
abbrev tfSum (I : ExecutionEnv) (σ : AccountMap) : UInt256 := tfValue I + tfBalT I σ
abbrev tfLog (I : ExecutionEnv) : LogEntry :=
  ⟨I.codeOwner, #[transferTopic, tfFrom I, tfTo I], UInt256.toByteArray (tfValue I)⟩
def insufficientAllowanceWord : UInt256 := ⟨0x45524332303a20696e73756666696369656e7420616c6c6f77616e6365000000⟩

noncomputable abbrev tfMA (I : ExecutionEnv) : ByteArray := twoWordHashMem (tfFrom I) ⟨1⟩ solcFreePtrMem
noncomputable abbrev tfMB (I : ExecutionEnv) : ByteArray := twoWordHashMem (callerW I) (tfS1 I) (tfMA I)
noncomputable abbrev tfMC (I : ExecutionEnv) : ByteArray := twoWordHashMem (tfFrom I) ⟨0⟩ (tfMB I)
noncomputable abbrev tfMD (I : ExecutionEnv) : ByteArray := twoWordHashMem (tfFrom I) ⟨1⟩ (tfMC I)
noncomputable abbrev tfME (I : ExecutionEnv) : ByteArray := twoWordHashMem (callerW I) (tfS1 I) (tfMD I)
noncomputable abbrev tfMF (I : ExecutionEnv) : ByteArray := twoWordHashMem (tfFrom I) ⟨0⟩ (tfME I)
noncomputable abbrev tfMG (I : ExecutionEnv) : ByteArray := twoWordHashMem (tfTo I) ⟨0⟩ (tfMF I)
noncomputable abbrev tfMH (I : ExecutionEnv) : ByteArray := (UInt256.toByteArray (tfValue I)).write 0 (tfMG I) 128 32

theorem tfMA_size (I : ExecutionEnv) : (tfMA I).size = 96 := twoWordHashMem_size_96 _ _ solcFreePtrMem_size
theorem tfMA_read64 (I : ExecutionEnv) : (tfMA I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
theorem tfMB_size (I : ExecutionEnv) : (tfMB I).size = 96 := twoWordHashMem_size_96 _ _ (tfMA_size I)
theorem tfMB_read64 (I : ExecutionEnv) : (tfMB I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (tfMA_size I) (tfMA_read64 I)
theorem tfMC_size (I : ExecutionEnv) : (tfMC I).size = 96 := twoWordHashMem_size_96 _ _ (tfMB_size I)
theorem tfMC_read64 (I : ExecutionEnv) : (tfMC I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (tfMB_size I) (tfMB_read64 I)
theorem tfMD_size (I : ExecutionEnv) : (tfMD I).size = 96 := twoWordHashMem_size_96 _ _ (tfMC_size I)
theorem tfME_size (I : ExecutionEnv) : (tfME I).size = 96 := twoWordHashMem_size_96 _ _ (tfMD_size I)
theorem tfMF_size (I : ExecutionEnv) : (tfMF I).size = 96 := twoWordHashMem_size_96 _ _ (tfME_size I)
theorem tfMG_size (I : ExecutionEnv) : (tfMG I).size = 96 := twoWordHashMem_size_96 _ _ (tfMF_size I)
theorem tfMG_read64 (I : ExecutionEnv) : (tfMG I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (tfMF_size I) (twoWordHashMem_read64 _ _ (tfME_size I)
    (twoWordHashMem_read64 _ _ (tfMD_size I) (twoWordHashMem_read64 _ _ (tfMC_size I) (tfMC_read64 I))))
theorem tfMG_gap (I : ExecutionEnv) : 128 - (tfMG I).size < USize.size := by
  rw [tfMG_size]; exact lt_usize _ (by norm_num)

/-- The `Error("ERC20: insufficient allowance")` tail at `0x1aa`; it falls into the shared block at `0x1ed`. -/
theorem errTailAllowance {s0 : State} {stk : List UInt256} {mem rdata : ByteArray} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x1aa⟩, stk, mem, UInt256.ofNat 3, rdata, w⟩ k C) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (hov : stk.length + 4 ≤ 1024) :
    Reverted erc20Runtime s0 (solcErrorStringPayload ⟨29⟩ insufficientAllowanceWord mem) := by
  have h1 := evm_run h with [push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have h2 := h1.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have h3 := evm_run h2 with [push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨29⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨29⟩ mem) (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have h4 := h3.pushConst insufficientAllowanceWord (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have h5 := evm_run h4 with [push1 ⟨68⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨29⟩ insufficientAllowanceWord mem) (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  exact errBlock h5 (by decide) hmem hread64 hov

/-- Up to the allowance check: `LT alw value` on top. -/
theorem tfCheckAlw {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x1a5⟩, UInt256.lt (tfAlw I σ) (tfValue I) :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ ::
        [solcSelectorWord I], tfMB I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := tfEntry hcode hwv hsize hsel
  obtain ⟨_, _, h1'⟩ := decAddrAddrU256Ok h hsz hbig hc0 hc1 (by jump_dest) (by simp)
  have h1 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0xb1⟩, tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3,
        ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ _ _ := h1'
  have hlandF : UInt256.land (tfFrom I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = tfFrom I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc0
  have h2 := evm_run h1 with [jumpdest, push2 ⟨0x17e⟩, jump (by jump_dest), jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩,
    shl, sub, dup4, and]
  rw [hlandF] at h2
  have h3 := evm_run h2 with [push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (tfFrom I) solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    push1 ⟨1⟩, push1 ⟨0x20⟩, swap1, dup2,
    raw mstore 0 (tfMA I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup1, dup4,
    raw keccak256 0 (tfS1 I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tfFrom I) solcFreePtrMem_size) (by decide) (by evm_ov),
    caller, dup5,
    raw mstore 0 (wordAt0Mem (callerW I) (tfMA I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    swap1, swap2,
    raw mstore 0 (tfMB I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    dup2,
    raw keccak256 0 (tfSA I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot (tfS1 I) (callerW I) (tfMA_size I)) (by decide) (by evm_ov)]
  obtain ⟨_, _, h4'⟩ := h3.sload (by native_decide) (by evm_ov)
  have h4 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x1a2⟩, tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMB I,
        UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ _ _ := h4'
  exact ⟨_, _, evm_run h4 with [dup3, dup2, lt]⟩

theorem tfRunInsufficientAllowance {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hlt : (tfAlw I σ).toNat < (tfValue I).toNat) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) (errorStringData "ERC20: insufficient allowance".toUTF8) := by
  obtain ⟨_, _, h⟩ := tfCheckAlw hcode hwv hsize hsel hsz hbig hc0 hc1
  rw [ult_one hlt] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h1
  have h2' := evm_run h1 with [push2 ⟨0x1f6⟩, jumpiNT rfl]
  have h2 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x1aa⟩, tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMB I, UInt256.ofNat 3,
        ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ _ _ := h2'
  have hrev := errTailAllowance h2 (tfMB_size I) (tfMB_read64 I) (by simp)
  rw [solcErrorStringPayload_eq (msg := "ERC20: insufficient allowance".toUTF8) (by native_decide) (by native_decide)
    (by rw [tfMB_size]; omega) (by native_decide) (by native_decide)] at hrev
  exact hrev

/-- After the allowance check: `GT value balF` on top. -/
theorem tfCheckBal {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x211⟩, UInt256.gt (tfValue I) (tfBalF I σ) :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ ::
        [solcSelectorWord I], tfMC I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := tfCheckAlw hcode hwv hsize hsel hsz hbig hc0 hc1
  rw [ult_zero hleA] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h1
  have hlandF : UInt256.land (tfFrom I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = tfFrom I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc0
  have h2 := evm_run h1 with [push2 ⟨0x1f6⟩, jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨0xa0⟩, shl, sub, dup6, and]
  rw [hlandF] at h2
  have h3 := evm_run h2 with [push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (tfFrom I) (tfMB I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (tfMC I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, swap1,
    raw keccak256 0 (tfSF I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (tfFrom I) (tfMB_size I)) (by decide) (by evm_ov)]
  obtain ⟨_, _, h4'⟩ := h3.sload (by native_decide) (by evm_ov)
  have h4 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x20f⟩, tfBalF I σ :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMC I,
        UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ _ _ := h4'
  exact ⟨_, _, evm_run h4 with [dup4, gt]⟩

theorem tfRunInsufficientBalance {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hlt : (tfBalF I σ).toNat < (tfValue I).toNat) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) (errorStringData "ERC20: insufficient balance".toUTF8) := by
  obtain ⟨_, _, h⟩ := tfCheckBal hcode hwv hsize hsel hsz hbig hc0 hc1 hleA
  rw [ugt_one hlt] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h1
  have h2 := evm_run h1 with [push2 ⟨0x25d⟩, jumpiNT rfl]
  have hrev := errTail h2 (len := ⟨27⟩) (word := insufficientBalanceWord)
    (by dsimp only [errTailWf]; repeat' first | apply And.intro | native_decide) (tfMC_size I) (tfMC_read64 I) (by simp)
  rw [solcErrorStringPayload_eq (msg := "ERC20: insufficient balance".toUTF8) (by native_decide) (by native_decide)
    (by rw [tfMC_size]; omega) (by native_decide) (by native_decide)] at hrev
  exact hrev

/-- After both checks: the allowance stored, `balanceOf[from]` re-read, the debit's `checked_sub` entered. -/
theorem tfDebit {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hleB : (tfValue I).toNat ≤ (tfBalF I σ).toNat) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x4fe⟩, tfBalF1 I σ :: tfValue I :: ⟨0x2a7⟩ :: ⟨0⟩ :: tfSF I :: tfValue I :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I ::
        tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMF I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW1 I σ, A.logSeries⟩⟩
      k C := by
  obtain ⟨_, _, h⟩ := tfCheckBal hcode hwv hsize hsel hsz hbig hc0 hc1 hleA
  rw [ugt_zero hleB] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h1
  have h2 := evm_run h1 with [push2 ⟨0x25d⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x267⟩, dup4, dup3,
    push2 ⟨0x4fe⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3⟩ := checkedSubOk h2 hleA (by jump_dest) (by simp)
  have hlandF : UInt256.land (tfFrom I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = tfFrom I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc0
  have h4 := evm_run h3 with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, dup7, and]
  rw [hlandF] at h4
  have h5 := evm_run h4 with [push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (tfFrom I) (tfMC I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨0x20⟩, swap1, dup2,
    raw mstore 0 (tfMD I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup1, dup4,
    raw keccak256 0 (tfS1 I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tfFrom I) (tfMC_size I)) (by decide) (by evm_ov),
    caller, dup5,
    raw mstore 0 (wordAt0Mem (callerW I) (tfMD I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    dup3,
    raw mstore 0 (tfME I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    dup1, dup4,
    raw keccak256 0 (tfSA I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot (tfS1 I) (callerW I) (tfMD_size I)) (by decide) (by evm_ov),
    swap5, swap1, swap5]
  obtain ⟨_, _, h6'⟩ := h5.sstore hperm (by native_decide) (by evm_ov)
  have h6 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x28e⟩, ⟨0x20⟩ :: ⟨0⟩ :: tfFrom I :: ⟨0x40⟩ :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ ::
        [solcSelectorWord I], tfME I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW1 I σ, A.logSeries⟩⟩ _ _ := h6'
  have h7 := evm_run h6 with [swap2, dup2,
    raw mstore 0 (wordAt0Mem (tfFrom I) (tfME I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    swap1, dup2, swap1,
    raw mstore 0 (tfMF I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    swap1, dup2,
    raw keccak256 0 (tfSF I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (tfFrom I) (tfME_size I)) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, h8'⟩ := h7.sload (by native_decide) (by evm_ov)
  have h8 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x29a⟩, tfBalF1 I σ :: tfSF I :: ⟨0⟩ :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ ::
        [solcSelectorWord I], tfMF I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW1 I σ, A.logSeries⟩⟩ _ _ := h8'
  exact ⟨_, _, evm_run h8 with [dup6, swap3, swap1, push2 ⟨0x2a7⟩, swap1, dup5, swap1, push2 ⟨0x4fe⟩, jump (by jump_dest)]⟩

theorem tfRunUnderflow {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hleB : (tfValue I).toNat ≤ (tfBalF I σ).toNat)
    (hlt : (tfBalF1 I σ).toNat < (tfValue I).toNat) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) (panicData 0x11) := by
  obtain ⟨_, _, h⟩ := tfDebit hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB
  have hrev := checkedSubUnderflow h hlt (by simp)
  rw [solcPanicPayload_eq] at hrev
  exact hrev

/-- After the debit: the credit's `checked_add` entered. -/
theorem tfCredit {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hleB : (tfValue I).toNat ≤ (tfBalF I σ).toNat)
    (hleF : (tfValue I).toNat ≤ (tfBalF1 I σ).toNat) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x511⟩, tfBalT I σ :: tfValue I :: ⟨0x2d3⟩ :: ⟨0⟩ :: tfST I :: tfValue I :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I ::
        tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMG I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW2 I σ, A.logSeries⟩⟩
      k C := by
  obtain ⟨_, _, h⟩ := tfDebit hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB
  obtain ⟨_, _, h1⟩ := checkedSubOk h hleF (by jump_dest) (by simp)
  have h2 := evm_run h1 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, h3'⟩ := h2.sstore hperm (by native_decide) (by evm_ov)
  have h3 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x2ab⟩, ⟨0⟩ :: tfValue I :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I],
        tfMF I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW2 I σ, A.logSeries⟩⟩ _ _ := h3'
  have hlandT : UInt256.land (tfTo I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = tfTo I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc1
  have h4 := evm_run h3 with [pop, pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, dup5, and]
  rw [hlandT] at h4
  have h5 := evm_run h4 with [push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (tfTo I) (tfMF I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (tfMG I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup2,
    raw keccak256 0 (tfST I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (tfTo I) (tfMF_size I)) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, h6'⟩ := h5.sload (by native_decide) (by evm_ov)
  have h6 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x2c6⟩, tfBalT I σ :: tfST I :: ⟨0⟩ :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ ::
        [solcSelectorWord I], tfMG I, UInt256.ofNat 3, ByteArray.empty, ⟨cA, tfW2 I σ, A.logSeries⟩⟩ _ _ := h6'
  exact ⟨_, _, evm_run h6 with [dup6, swap3, swap1, push2 ⟨0x2d3⟩, swap1, dup5, swap1, push2 ⟨0x511⟩, jump (by jump_dest)]⟩

theorem tfRunOverflow {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hleB : (tfValue I).toNat ≤ (tfBalF I σ).toNat)
    (hleF : (tfValue I).toNat ≤ (tfBalF1 I σ).toNat) (hover : UInt256.size ≤ (tfValue I).toNat + (tfBalT I σ).toNat) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) (panicData 0x11) := by
  obtain ⟨_, _, h⟩ := tfCredit hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB hleF
  have hrev := checkedAddOverflow h hover (by simp)
  rw [solcPanicPayload_eq] at hrev
  exact hrev

theorem tfRunOk {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (tfAlw I σ).toNat) (hleB : (tfValue I).toNat ≤ (tfBalF I σ).toNat)
    (hleF : (tfValue I).toNat ≤ (tfBalF1 I σ).toNat) (hfit : (tfValue I).toNat + (tfBalT I σ).toNat < UInt256.size) :
    Returned erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ (tfSA I) (tfNewAlw I σ))
        (tfSF I) (tfDiff I σ)) (tfST I) (tfSum I σ), A.logSeries.push (tfLog I)⟩
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, h⟩ := tfCredit hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB hleF
  obtain ⟨_, _, h1⟩ := checkedAddOk h hfit (by jump_dest) (by simp)
  have h2 := evm_run h1 with [jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, h3'⟩ := h2.sstore hperm (by native_decide) (by evm_ov)
  have h3 : Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x2da⟩, tfSum I σ :: tfAlw I σ :: ⟨0⟩ :: tfValue I :: tfTo I :: tfFrom I :: ⟨0x77⟩ :: [solcSelectorWord I], tfMG I,
        UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, sstoreAccountMap I.codeOwner (tfW2 I σ) (tfST I) (tfSum I σ), A.logSeries⟩⟩ _ _ := h3'
  have hlandF : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (tfFrom I) = tfFrom I := by
    rw [u256_land_comm, solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc0
  have hlandT : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (tfTo I) = tfTo I := by
    rw [u256_land_comm, solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc1
  have h4 := evm_run h3 with [pop, dup4, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, and]
  rw [hlandT] at h4
  have h5 := evm_run h4 with [dup6, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, and]
  rw [hlandF] at h5
  have h6 := h5.pushConst (width := 32) (op := .PUSH32) transferTopic (by decide) (by native_decide) (by evm_ov)
  have hm : 96 ≤ (tfMG I).size := by rw [tfMG_size]
  obtain ⟨hszH, hrH, hbH⟩ := freePtr_after_write128 (tfValue I) hm (tfMG_read64 I) (tfMG_gap I)
  have hsH : 128 + 32 ≤ (tfMH I).size := toByteArray_write_size_ge_off_add32 _ _ 128 (tfMG_gap I)
  have h7 := evm_run h6 with [dup6, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost (mloadFreePtrValue (by omega) (by decide) (tfMG_read64 I))
      (by decide) (by evm_ov),
    push2 ⟨0x31f⟩, swap2, dup2,
    raw mstore 6 (tfMH I) (UInt256.ofNat 5) (by native_decide) mem_cost rfl (by native_decide) (by evm_ov),
    push1 ⟨0x20⟩, add, swap1, jump (by jump_dest), jumpdest, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (mloadFreePtrValue hszH (by decide) hrH) (by decide)
      (by evm_ov),
    dup1, swap2, sub, swap1]
  rw [show UInt256.sub (⟨32⟩ + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide] at h7
  have h8 := h7.log3 0 (UInt256.ofNat 5) (by native_decide) hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from rfl, hbH] at h8
  have h9 := evm_run h8 with [pop, push1 ⟨1⟩, swap5, swap4, pop, pop, pop, pop, jump (by jump_dest)]
  exact retBoolTrue (R := [solcSelectorWord I]) (mem := tfMH I) h9 (by omega) hrH (lt_usize _ (by omega)) (by simp)

theorem tfRunShort {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2)) (hshort : I.calldata.size < 100) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := tfEntry hcode hwv hsize hsel
  exact decAddrAddrU256LenRevert h (lenCheck_short (by norm_num) (size_ge_of_sel rfl hsel) hshort) (by simp)

theorem tfRunHuge {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2)) (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := tfEntry hcode hwv hsize hsel
  exact decAddrAddrU256LenRevert h (lenCheck_huge (by norm_num) hhuge hsize) (by simp)

theorem tfRunDirty0 {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc0 : ¬ (tfFrom I).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := tfEntry hcode hwv hsize hsel
  exact decAddrAddrU256Dirty0Revert h hsz hbig hnc0 (by simp)

theorem tfRunDirty1 {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 2))
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hnc1 : ¬ (tfTo I).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := tfEntry hcode hwv hsize hsel
  exact decAddrAddrU256Dirty1Revert h hsz hbig hc0 hnc1 (by simp)

/-! ## The spec derivations -/

def tfFrame (f t : EVM.Address) (w : UInt256) : Frame :=
  (((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "from" addrTy (some .memory) (.address f)).bind
    "to" addrTy (some .memory) (.address t)).bind "value" u256 (some .memory) (u256Val w.toNat)).bind
    "#ret0" .bool (some .memory) (.bool false)

def tfStmts : Block :=
  [ .varDecl u256 none "currentAllowance" (some (.index (.index (.ident "allowance") (.ident "from")) msgSender)),
    .exprStmt (.call (.ident "require") [] (.positional
      [ .binary .ge (.ident "currentAllowance") (.ident "value"), .lit (.str "ERC20: insufficient allowance") ])),
    .exprStmt (.call (.ident "require") [] (.positional
      [ .binary .ge (.index (.ident "balanceOf") (.ident "from")) (.ident "value"), .lit (.str "ERC20: insufficient balance") ])),
    .exprStmt (.assign .assign (.index (.index (.ident "allowance") (.ident "from")) msgSender)
      (.binary .sub (.ident "currentAllowance") (.ident "value"))),
    .exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")),
    .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
    .emit (.ident "Transfer") (.positional [.ident "from", .ident "to", .ident "value"]),
    .return (some (.lit (.bool true))) ]

theorem tfEnter (m : Machine) (f t : EVM.Address) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTransferFrom.decl [.address f, .address t, u256Val w.toNat] m =
      some (.ok (tfFrame f t w, m)) := by
  simp [enterFn, declare, coerce, fnTransferFrom, tfFrame, fuelDefault]
  try rfl

/-- The allowance slot read by the body. -/
abbrev aSlot (m : Machine) (f : EVM.Address) : UInt256 := alwSlot f m.evm.executionEnv.source
/-- The frame after `uint256 currentAllowance = allowance[from][msg.sender];`. -/
abbrev tfFr1 (m : Machine) (f t : EVM.Address) (w : UInt256) : Frame :=
  (bodyFrame (tfFrame f t w) tfStmts).bind "currentAllowance" u256 none (u256Val (loadU256 m (aSlot m f)).toNat)
noncomputable abbrev tfM1 (m : Machine) (f : EVM.Address) (w : UInt256) : Machine :=
  storeU256 m (aSlot m f) (UInt256.ofNat ((loadU256 m (aSlot m f)).toNat - w.toNat))
noncomputable abbrev tfM2 (m : Machine) (f : EVM.Address) (w : UInt256) : Machine :=
  storeU256 (tfM1 m f w) (balSlot f) (UInt256.ofNat ((loadU256 (tfM1 m f w) (balSlot f)).toNat - w.toNat))
noncomputable abbrev tfM3 (m : Machine) (f t : EVM.Address) (w : UInt256) : Machine :=
  storeU256 (tfM2 m f w) (balSlot t) (UInt256.ofNat ((loadU256 (tfM2 m f w) (balSlot t)).toNat + w.toNat))
noncomputable abbrev tfLe (m : Machine) (f t : EVM.Address) (w : UInt256) : LogEntry :=
  { address := (tfM3 m f t w).this,
    topics := #[hashWord evTransfer.sigStr.toUTF8, UInt256.ofNat f.toNat, UInt256.ofNat t.toNat],
    data := UInt256.toByteArray w }
noncomputable abbrev tfFinal (m : Machine) (f t : EVM.Address) (w : UInt256) : Machine :=
  (tfM3 m f t w).pushLog (tfLe m f t w)

theorem tfDecl (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    ExecStmt erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m
      (.varDecl u256 none "currentAllowance" (some (.index (.index (.ident "allowance") (.ident "from")) msgSender)))
      (.normal (tfFr1 m f t w) m) :=
  ExecStmt.varDeclU256 (EvalExpr.mapping2AddrU256 (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_allowance rfl rfl
    (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])) EvalExpr.msgSender
    (erc20Layout_allowance f _ m.evm))

theorem tfCondA (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (tfFr1 m f t w) m (.binary .ge (.ident "currentAllowance") (.ident "value"))
      (.ok (.bool (decide (w.toNat ≤ (loadU256 m (aSlot m f)).toNat))) (tfFr1 m f t w) m) :=
  EvalExpr.geU256 (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
    (EvalExpr.localVal u256 none (by frame_simp [bodyFrame, tfFrame]))

theorem tfCondB (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (tfFr1 m f t w) m (.binary .ge (.index (.ident "balanceOf") (.ident "from")) (.ident "value"))
      (.ok (.bool (decide (w.toNat ≤ (loadU256 m (balSlot f)).toNat))) (tfFr1 m f t w) m) :=
  EvalExpr.geU256 (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
    (EvalExpr.mappingAddrU256 (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])) (erc20Layout_balanceOf f m.evm))

theorem tfBodyInsufficientAllowance (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hlt : (loadU256 m (aSlot m f)).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts
      (.reverted (errorStringData "ERC20: insufficient allowance".toUTF8)) := by
  have hc := tfCondA o m f t w
  rw [decide_eq_false (by omega)] at hc
  exact ExecBlock.cons (tfDecl o m f t w) (ExecBlock.consRevert (ExecStmt.requireMsgRevert hc))

theorem tfBodyInsufficientBalance (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hlt : (loadU256 m (balSlot f)).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts
      (.reverted (errorStringData "ERC20: insufficient balance".toUTF8)) := by
  have hcA := tfCondA o m f t w
  rw [decide_eq_true hleA] at hcA
  have hcB := tfCondB o m f t w
  rw [decide_eq_false (by omega)] at hcB
  exact ExecBlock.cons (tfDecl o m f t w) (ExecBlock.cons (ExecStmt.requireTrue hcA)
    (ExecBlock.consRevert (ExecStmt.requireMsgRevert hcB)))

/-- The allowance assignment `allowance[from][msg.sender] = currentAllowance - value;`. -/
theorem tfStoreAlw (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr1 m f t w) m
      (.exprStmt (.assign .assign (.index (.index (.ident "allowance") (.ident "from")) msgSender)
        (.binary .sub (.ident "currentAllowance") (.ident "value"))))
      (.normal (tfFr1 m f t w) (tfM1 m f w)) := by
  have hb : (loadU256 m (aSlot m f)).toNat < UInt256.size := (loadU256 m (aSlot m f)).val.isLt
  have hsub : EvalExpr erc20Cfg o erc20Flat (tfFr1 m f t w) m (.binary .sub (.ident "currentAllowance") (.ident "value"))
      (.ok (u256Val ((loadU256 m (aSlot m f)).toNat - w.toNat)) (tfFr1 m f t w) m) :=
    EvalExpr.subU256 (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
      (EvalExpr.localVal u256 none (by frame_simp [bodyFrame, tfFrame])) (by frame_simp [bodyFrame, tfFrame]) hb hleA
  rw [← ulit_toNat' ((loadU256 m (aSlot m f)).toNat - w.toNat) (by omega)] at hsub
  exact ExecStmt.assignStorageU256 (w := UInt256.ofNat ((loadU256 m (aSlot m f)).toNat - w.toNat)) hsub
    (EvalLValue.mapping2Addr (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_allowance rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])) EvalExpr.msgSender)
    (erc20Layout_allowance f _ m.evm)

/-- The common prefix of the three later outcomes: declaration, both checks, the allowance store. -/
theorem tfPrefix (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) {r : ExecResult}
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hleB : w.toNat ≤ (loadU256 m (balSlot f)).toNat)
    (hrest : ExecBlock erc20Cfg o erc20Flat (tfFr1 m f t w) (tfM1 m f w) (tfStmts.drop 4) r) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts r := by
  have hcA := tfCondA o m f t w
  rw [decide_eq_true hleA] at hcA
  have hcB := tfCondB o m f t w
  rw [decide_eq_true hleB] at hcB
  exact ExecBlock.cons (tfDecl o m f t w) (ExecBlock.cons (ExecStmt.requireTrue hcA)
    (ExecBlock.cons (ExecStmt.requireTrue hcB) (ExecBlock.cons (tfStoreAlw o m f t w hleA) hrest)))

theorem tfBodyUnderflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hleB : w.toNat ≤ (loadU256 m (balSlot f)).toNat)
    (hlt : (loadU256 (tfM1 m f w) (balSlot f)).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts (.reverted (panicData 0x11)) :=
  tfPrefix o m f t w hleA hleB (ExecBlock.consRevert (ExecStmt.subAssignU256Underflow (b := w) (slot := balSlot f)
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])))
    (erc20Layout_balanceOf f _) (by frame_simp [bodyFrame, tfFrame]) hlt))

theorem tfDebitStmt (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleF : w.toNat ≤ (loadU256 (tfM1 m f w) (balSlot f)).toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr1 m f t w) (tfM1 m f w)
      (.exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")))
      (.normal (tfFr1 m f t w) (tfM2 m f w)) :=
  ExecStmt.subAssignU256 (b := w) (slot := balSlot f)
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])))
    (erc20Layout_balanceOf f _) (by frame_simp [bodyFrame, tfFrame]) hleF

theorem tfBodyOverflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hleB : w.toNat ≤ (loadU256 m (balSlot f)).toNat)
    (hleF : w.toNat ≤ (loadU256 (tfM1 m f w) (balSlot f)).toNat)
    (hover : UInt256.size ≤ (loadU256 (tfM2 m f w) (balSlot t)).toNat + w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts (.reverted (panicData 0x11)) :=
  tfPrefix o m f t w hleA hleB (ExecBlock.cons (tfDebitStmt o m f t w hleF) (ExecBlock.consRevert
    (ExecStmt.addAssignU256Overflow (b := w) (slot := balSlot t)
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
      (EvalLValue.mappingAddr (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_balanceOf rfl rfl
        (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])))
      (erc20Layout_balanceOf t _) (by frame_simp [bodyFrame, tfFrame]) hover)))

theorem tfBodyOk (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hleB : w.toNat ≤ (loadU256 m (balSlot f)).toNat)
    (hleF : w.toNat ≤ (loadU256 (tfM1 m f w) (balSlot f)).toNat)
    (hfit : (loadU256 (tfM2 m f w) (balSlot t)).toNat + w.toNat < UInt256.size) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts
      (.returned ((tfFr1 m f t w).setVal "#ret0" (.bool true)) (tfFinal m f t w)) := by
  refine tfPrefix o m f t w hleA hleB (ExecBlock.cons (tfDebitStmt o m f t w hleF) ?_)
  refine ExecBlock.cons (ExecStmt.addAssignU256 (b := w) (slot := balSlot t)
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, tfFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame])))
    (erc20Layout_balanceOf t _) (by frame_simp [bodyFrame, tfFrame]) hfit) ?_
  refine ExecBlock.cons (ExecStmt.emitAddrAddrU256 (a := f) (b := t) (n := w) erc20Flat_eventsNamed_Transfer rfl rfl rfl
    (EvalExprs.three (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame]))
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, tfFrame]))
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, tfFrame])))) ?_
  exact ExecBlock.consReturn (ExecStmt.returnBool { ty := .bool, loc := some .memory, val := .bool false } rfl
    (EvalExpr.boolLit true) (by frame_simp [bodyFrame, tfFrame]) rfl (by frame_simp [bodyFrame, tfFrame]))

theorem tfCallOk (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hleA : w.toNat ≤ (loadU256 m (aSlot m f)).toNat) (hleB : w.toNat ≤ (loadU256 m (balSlot f)).toNat)
    (hleF : w.toNat ≤ (loadU256 (tfM1 m f w) (balSlot f)).toNat)
    (hfit : (loadU256 (tfM2 m f w) (balSlot t)).toNat + w.toNat < UInt256.size) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransferFrom [.address f, .address t, u256Val w.toNat]
      (.ok [.bool true] (tfFinal m f t w)) :=
  CallFn.plain (tfEnter m f t w) rfl rfl (tfBodyOk o m f t w hleA hleB hleF hfit) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, tfFrame]) (by frame_simp [bodyFrame, tfFrame])
      (by frame_simp [retVals, bodyFrame, tfFrame]))

theorem tfCallRevert (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) {d : ByteArray}
    (hb : ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame f t w) tfStmts) m tfStmts (.reverted d)) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransferFrom [.address f, .address t, u256Val w.toNat] (.reverted d) :=
  CallFn.plainRevert (tfEnter m f t w) rfl rfl hb

abbrev tfFromA (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (tfFrom I).toNat
abbrev tfToA (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (tfTo I).toNat

theorem tfArgs {I : ExecutionEnv} (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata =
      some [.address (tfFromA I), .address (tfToA I), .int (Int.ofNat (tfValue I).toNat)] := by
  rw [decodeArgs_transferFrom]; exact decodeCalldataValues_address_address_uint256_ok hsz hbig hc0 hc1

theorem tfBind (I : ExecutionEnv) :
    ofAbiParams erc20Flat.types I.calldata fnTransferFrom.decl.params
      [.address (tfFromA I), .address (tfToA I), .int (Int.ofNat (tfValue I).toNat)] {} =
      some ([.address (tfFromA I), .address (tfToA I), u256Val (tfValue I).toNat], {}) := by
  simp [ofAbiParams, fnTransferFrom, fuelDefault, calldataRef]

theorem tfSpecOk (o : Oracle) {cA gh bl σ σ₀ g A I} (hsel : selIs I (selBytes 2)) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hleA : (tfValue I).toNat ≤ (loadU256 (initMachine cA gh bl σ σ₀ g A I) (aSlot (initMachine cA gh bl σ σ₀ g A I) (tfFromA I))).toNat)
    (hleB : (tfValue I).toNat ≤ (loadU256 (initMachine cA gh bl σ σ₀ g A I) (balSlot (tfFromA I))).toNat)
    (hleF : (tfValue I).toNat ≤ (loadU256 (tfM1 (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfValue I)) (balSlot (tfFromA I))).toNat)
    (hfit : (loadU256 (tfM2 (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfValue I)) (balSlot (tfToA I))).toNat +
      (tfValue I).toNat < UInt256.size) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned (tfFinal (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfToA I) (tfValue I)) [.bool true])
      (.abi [.elem .bool]) := by
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault
      (tfFinal (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfToA I) (tfValue I)).heap [.bool true] =
      some (.ok ([.bool true], (tfFinal (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfToA I) (tfValue I)).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp)
  exact solidityExec.call (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv) rfl (tfArgs hsz hbig hc0 hc1)
    (tfBind I) (tfCallOk o (initMachine cA gh bl σ σ₀ g A I) (tfFromA I) (tfToA I) (tfValue I) hleA hleB hleF hfit) hprep
    (by simp [fuelDefault])

theorem tfSpecRevert (o : Oracle) {cA gh bl σ σ₀ g A I} {d : ByteArray} (hsel : selIs I (selBytes 2)) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (tfFrom I).toNat < EVM.addressModulus) (hc1 : (tfTo I).toNat < EVM.addressModulus)
    (hb : ExecBlock erc20Cfg o erc20Flat (bodyFrame (tfFrame (tfFromA I) (tfToA I) (tfValue I)) tfStmts)
      (initMachine cA gh bl σ σ₀ g A I) tfStmts (.reverted d)) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I (.reverted d) (.abi [.elem .bool]) :=
  solidityExec.callReverted (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv) rfl (tfArgs hsz hbig hc0 hc1)
    (tfBind I) (tfCallRevert o _ _ _ _ hb)

/-! ## The coupled result -/

theorem transferFromCorrect {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I (selBytes 2)) (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceFor erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hdec : decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none →
      Reverted erc20Runtime (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty →
      runtimeEquivalenceFor erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := fun hd h =>
    Reverted.specDecodingFailed hcode h (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv)
      (decodeCallArgs_none_of_decodeArgs hd)
  by_cases hsz : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc0 : (tfFrom I).toNat < EVM.addressModulus
      · by_cases hc1 : (tfTo I).toNat < EVM.addressModulus
        · set m0 := initMachine cA gh bl σ_spec σ₀ g A I with hm0
          have hw0 : WorldEquiv ⟨cA, σ_evm, A.logSeries⟩ m0 := WorldEquiv.init {} hAccounts
          have hslotA : aSlot m0 (tfFromA I) = tfSA I := by
            rw [aSlot, alwSlot_eq, hm0, initMachine_executionEnv]
            show solcMappingSlot (solcMappingSlot ⟨1⟩ (UInt256.ofNat (AccountAddress.ofNat (tfFrom I).toNat).toNat))
              (UInt256.ofNat I.source.val) = _
            rw [addrWord_canon hc0]
          have hslotF : balSlot (tfFromA I) = tfSF I := by
            rw [balSlot_eq]
            show solcMappingSlot ⟨0⟩ (UInt256.ofNat (AccountAddress.ofNat (tfFrom I).toNat).toNat) = _
            rw [addrWord_canon hc0]
          have hslotT : balSlot (tfToA I) = tfST I := by
            rw [balSlot_eq]
            show solcMappingSlot ⟨0⟩ (UInt256.ofNat (AccountAddress.ofNat (tfTo I).toNat).toNat) = _
            rw [addrWord_canon hc1]
          have halw : tfAlw I σ_evm = loadU256 m0 (aSlot m0 (tfFromA I)) := by rw [hslotA]; exact hw0.sload rfl _
          have hbalF : tfBalF I σ_evm = loadU256 m0 (balSlot (tfFromA I)) := by rw [hslotF]; exact hw0.sload rfl _
          by_cases hleA : (tfValue I).toNat ≤ (tfAlw I σ_evm).toNat
          · have hleA' : (tfValue I).toNat ≤ (loadU256 m0 (aSlot m0 (tfFromA I))).toNat := by rw [← halw]; exact hleA
            by_cases hleB : (tfValue I).toNat ≤ (tfBalF I σ_evm).toNat
            · have hleB' : (tfValue I).toNat ≤ (loadU256 m0 (balSlot (tfFromA I))).toNat := by rw [← hbalF]; exact hleB
              have hnew : UInt256.ofNat ((loadU256 m0 (aSlot m0 (tfFromA I))).toNat - (tfValue I).toNat) = tfNewAlw I σ_evm := by
                have hb : (tfAlw I σ_evm).toNat < UInt256.size := (tfAlw I σ_evm).val.isLt
                rw [← halw]; apply u256_inj; rw [ulit_toNat' _ (by omega), usub_toNat hleA]
              have hw1 : WorldEquiv ⟨cA, tfW1 I σ_evm, A.logSeries⟩ (tfM1 m0 (tfFromA I) (tfValue I)) := by
                show WorldEquiv ⟨cA, sstoreAccountMap I.codeOwner σ_evm (tfSA I) (tfNewAlw I σ_evm), A.logSeries⟩ _
                rw [← hnew, ← hslotA]
                exact hw0.sstore (owner := I.codeOwner) rfl (aSlot m0 (tfFromA I)) _
              have hown1 : I.codeOwner = (tfM1 m0 (tfFromA I) (tfValue I)).evm.executionEnv.codeOwner := by
                rw [storeU256_executionEnv, hm0, initMachine_executionEnv]
              have hbalF1 : tfBalF1 I σ_evm = loadU256 (tfM1 m0 (tfFromA I) (tfValue I)) (balSlot (tfFromA I)) := by
                rw [hslotF]; exact hw1.sload (I := I) hown1 (tfSF I)
              by_cases hleF : (tfValue I).toNat ≤ (tfBalF1 I σ_evm).toNat
              · have hleF' : (tfValue I).toNat ≤ (loadU256 (tfM1 m0 (tfFromA I) (tfValue I)) (balSlot (tfFromA I))).toNat := by
                  rw [← hbalF1]; exact hleF
                have hdiff : UInt256.ofNat ((loadU256 (tfM1 m0 (tfFromA I) (tfValue I)) (balSlot (tfFromA I))).toNat -
                    (tfValue I).toNat) = tfDiff I σ_evm := by
                  have hb : (tfBalF1 I σ_evm).toNat < UInt256.size := (tfBalF1 I σ_evm).val.isLt
                  rw [← hbalF1]; apply u256_inj; rw [ulit_toNat' _ (by omega), usub_toNat hleF]
                have hw2 : WorldEquiv ⟨cA, tfW2 I σ_evm, A.logSeries⟩ (tfM2 m0 (tfFromA I) (tfValue I)) := by
                  show WorldEquiv ⟨cA, sstoreAccountMap I.codeOwner (tfW1 I σ_evm) (tfSF I) (tfDiff I σ_evm), A.logSeries⟩ _
                  rw [← hdiff, ← hslotF]
                  exact hw1.sstore (owner := I.codeOwner) hown1 (balSlot (tfFromA I)) _
                have hown2 : I.codeOwner = (tfM2 m0 (tfFromA I) (tfValue I)).evm.executionEnv.codeOwner := by
                  rw [storeU256_executionEnv, storeU256_executionEnv, hm0, initMachine_executionEnv]
                have hbalT : tfBalT I σ_evm = loadU256 (tfM2 m0 (tfFromA I) (tfValue I)) (balSlot (tfToA I)) := by
                  rw [hslotT]; exact hw2.sload (I := I) hown2 (tfST I)
                by_cases hfit : (tfValue I).toNat + (tfBalT I σ_evm).toNat < UInt256.size
                · have hfit' : (loadU256 (tfM2 m0 (tfFromA I) (tfValue I)) (balSlot (tfToA I))).toNat + (tfValue I).toNat <
                      UInt256.size := by rw [← hbalT]; omega
                  have hsum : UInt256.ofNat ((loadU256 (tfM2 m0 (tfFromA I) (tfValue I)) (balSlot (tfToA I))).toNat +
                      (tfValue I).toNat) = tfSum I σ_evm := by
                    rw [← hbalT]; apply u256_inj
                    rw [ulit_toNat' _ (by omega), uadd_toNat, Nat.add_comm, Nat.mod_eq_of_lt (by omega)]
                  have hw3 : WorldEquiv ⟨cA, sstoreAccountMap I.codeOwner (tfW2 I σ_evm) (tfST I) (tfSum I σ_evm), A.logSeries⟩
                      (tfM3 m0 (tfFromA I) (tfToA I) (tfValue I)) := by
                    rw [← hsum, ← hslotT]
                    exact hw2.sstore (owner := I.codeOwner) hown2 (balSlot (tfToA I)) _
                  have hle3 : tfLe m0 (tfFromA I) (tfToA I) (tfValue I) = tfLog I := by
                    simp only [tfLe, Machine.this, tfM2, tfM1, storeU256, storageStore_executionEnv, hm0,
                      initMachine_executionEnv, evTransfer_topic, addrWord_canon hc0, addrWord_canon hc1, tfLog, transferTopic]
                  have hw4 := hw3.pushLog (tfLe m0 (tfFromA I) (tfToA I) (tfValue I))
                  have hrun := tfRunOk (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
                    hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB hleF hfit
                  rw [← hle3] at hrun
                  exact Returned.specExecutionW default hcode hrun (tfSpecOk default hsel hwv hsz hbig hc0 hc1 hleA' hleB' hleF' hfit')
                    hw4 (.abi boolTrueReturnEncoding)
                · have hover : UInt256.size ≤ (loadU256 (tfM2 m0 (tfFromA I) (tfValue I)) (balSlot (tfToA I))).toNat +
                      (tfValue I).toNat := by rw [← hbalT]; omega
                  exact Reverted.specRevert default hcode
                    (tfRunOverflow hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB hleF (by omega))
                    (tfSpecRevert default hsel hwv hsz hbig hc0 hc1
                      (tfBodyOverflow default m0 (tfFromA I) (tfToA I) (tfValue I) hleA' hleB' hleF' hover))
              · have hlt : (loadU256 (tfM1 m0 (tfFromA I) (tfValue I)) (balSlot (tfFromA I))).toNat < (tfValue I).toNat := by
                  rw [← hbalF1]; omega
                exact Reverted.specRevert default hcode
                  (tfRunUnderflow hcode hwv hsize hperm hsel hsz hbig hc0 hc1 hleA hleB (by omega))
                  (tfSpecRevert default hsel hwv hsz hbig hc0 hc1
                    (tfBodyUnderflow default m0 (tfFromA I) (tfToA I) (tfValue I) hleA' hleB' hlt))
            · have hlt : (loadU256 m0 (balSlot (tfFromA I))).toNat < (tfValue I).toNat := by rw [← hbalF]; omega
              exact Reverted.specRevert default hcode
                (tfRunInsufficientBalance hcode hwv hsize hsel hsz hbig hc0 hc1 hleA (by omega))
                (tfSpecRevert default hsel hwv hsz hbig hc0 hc1
                  (tfBodyInsufficientBalance default m0 (tfFromA I) (tfToA I) (tfValue I) hleA' hlt))
          · have hlt : (loadU256 m0 (aSlot m0 (tfFromA I))).toNat < (tfValue I).toNat := by rw [← halw]; omega
            exact Reverted.specRevert default hcode (tfRunInsufficientAllowance hcode hwv hsize hsel hsz hbig hc0 hc1 (by omega))
              (tfSpecRevert default hsel hwv hsz hbig hc0 hc1
                (tfBodyInsufficientAllowance default m0 (tfFromA I) (tfToA I) (tfValue I) hlt))
        · exact hdec (by rw [decodeArgs_transferFrom]; exact decodeCalldataValues_address_address_uint256_none_noncanon1 hsz hbig hc0 hc1)
            (tfRunDirty1 hcode hwv hsize hsel hsz hbig hc0 hc1)
      · exact hdec (by rw [decodeArgs_transferFrom]; exact decodeCalldataValues_address_address_uint256_none_noncanon0 hsz hbig hc0)
          (tfRunDirty0 hcode hwv hsize hsel hsz hbig hc0)
    · exact hdec (by rw [decodeArgs_transferFrom]; exact decodeCalldataValues_address_address_uint256_none_huge (by omega))
        (tfRunHuge hcode hwv hsize hsel (by omega))
  · exact hdec (by rw [decodeArgs_transferFrom]; exact decodeCalldataValues_address_address_uint256_none_short hsz4 (by omega))
      (tfRunShort hcode hwv hsize hsel (by omega))

end ERC20.Opt
