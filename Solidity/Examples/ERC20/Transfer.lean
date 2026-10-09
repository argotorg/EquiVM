import Solidity.Examples.ERC20.Shapes

/-!
# ERC20 — `transfer(address,uint256)` refines its Solidity body

Three outcomes: the `require` failure (`Error("ERC20: insufficient balance")`), the credit's
overflow (`Panic(0x11)`), and success (two stores, the `Transfer` log, `true`).
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM runs -/

theorem trEntry {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4)) :
    ∃ k C, Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x437⟩, ⟨4⟩ :: UInt256.ofNat (initState σ σ₀ g A I).executionEnv.calldata.size :: ⟨0xe3⟩ :: ⟨0x77⟩ ::
        [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := reachBodyOf 4 (by omega) ⟨0xd5⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨0x77⟩, push2 ⟨0xe3⟩, calldatasize, push1 ⟨4⟩, push2 ⟨0x437⟩,
    jump (by jump_dest)]⟩

abbrev trTo (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev trValue (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
/-- The slots of `balanceOf[msg.sender]` and `balanceOf[to]`. -/
abbrev trSlotS (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨0⟩ (callerW I)
abbrev trSlotT (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨0⟩ (trTo I)
abbrev trBal (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord σ I (trSlotS I)
abbrev trDiff (I : ExecutionEnv) (σ : AccountMap) : UInt256 := UInt256.sub (trBal I σ) (trValue I)
abbrev trW1 (I : ExecutionEnv) (σ : AccountMap) : AccountMap := sstoreAccountMap I.codeOwner σ (trSlotS I) (trDiff I σ)
abbrev trBalT (I : ExecutionEnv) (σ : AccountMap) : UInt256 := solcSlotWord (trW1 I σ) I (trSlotT I)
abbrev trSum (I : ExecutionEnv) (σ : AccountMap) : UInt256 := trValue I + trBalT I σ
def transferTopic : UInt256 := ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩
abbrev trLog (I : ExecutionEnv) : LogEntry :=
  ⟨I.codeOwner, #[transferTopic, callerW I, trTo I], UInt256.toByteArray (trValue I)⟩
/-- The left-aligned word of `"ERC20: insufficient balance"`. -/
def insufficientBalanceWord : UInt256 := ⟨0x45524332303a20696e73756666696369656e742062616c616e63650000000000⟩

noncomputable abbrev trMem2 (I : ExecutionEnv) : ByteArray := twoWordHashMem (callerW I) ⟨0⟩ solcFreePtrMem
noncomputable abbrev trMem4 (I : ExecutionEnv) : ByteArray := twoWordHashMem (callerW I) ⟨0⟩ (trMem2 I)
noncomputable abbrev trMem6 (I : ExecutionEnv) : ByteArray := twoWordHashMem (trTo I) ⟨0⟩ (trMem4 I)
noncomputable abbrev trMem7 (I : ExecutionEnv) : ByteArray := (UInt256.toByteArray (trValue I)).write 0 (trMem6 I) 128 32

theorem trMem2_size (I : ExecutionEnv) : (trMem2 I).size = 96 := twoWordHashMem_size_96 _ _ solcFreePtrMem_size
theorem trMem2_read64 (I : ExecutionEnv) : (trMem2 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
theorem trMem4_size (I : ExecutionEnv) : (trMem4 I).size = 96 := twoWordHashMem_size_96 _ _ (trMem2_size I)
theorem trMem4_read64 (I : ExecutionEnv) : (trMem4 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (trMem2_size I) (trMem2_read64 I)
theorem trMem6_size (I : ExecutionEnv) : (trMem6 I).size = 96 := twoWordHashMem_size_96 _ _ (trMem4_size I)
theorem trMem6_read64 (I : ExecutionEnv) : (trMem6 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (trMem4_size I) (trMem4_read64 I)
theorem trMem6_gap (I : ExecutionEnv) : 128 - (trMem6 I).size < USize.size := by
  rw [trMem6_size]; exact lt_usize _ (by norm_num)

/-- Up to the balance check: `GT value bal` on top. -/
theorem trCheck {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus) :
    ∃ k C, Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x344⟩, UInt256.gt (trValue I) (trBal I σ) :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I],
        trMem2 I, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := trEntry hcode hwv hsize hsel
  obtain ⟨_, _, h1'⟩ := decAddrU256Ok h hsz68 hbig hc (by jump_dest) (by simp)
  have h1 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0xe3⟩, trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3,
        ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ _ _ := h1'
  have h2 := evm_run h1 with [jumpdest, push2 ⟨0x332⟩, jump (by jump_dest), jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (callerW I) solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (trMem2 I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup2,
    raw keccak256 0 (trSlotS I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (callerW I) solcFreePtrMem_size) (by decide) (by evm_ov)]
  obtain ⟨_, _, h3'⟩ := h2.sload (by native_decide) (by evm_ov)
  have h3 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x342⟩, trBal I σ :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], trMem2 I, UInt256.ofNat 3,
        ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ _ _ := h3'
  exact ⟨_, _, evm_run h3 with [dup3, gt]⟩

theorem trRunInsufficient {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hlt : (trBal I σ).toNat < (trValue I).toNat) :
    Reverted erc20Runtime (initState σ σ₀ g A I) (errorStringData "ERC20: insufficient balance".toUTF8) := by
  obtain ⟨_, _, h⟩ := trCheck hcode hwv hsize hsel hsz68 hbig hc
  rw [ugt_one hlt] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h1
  have h2 := evm_run h1 with [push2 ⟨0x390⟩, jumpiNT rfl]
  have hrev := errTail h2 (len := ⟨27⟩) (word := insufficientBalanceWord)
    (by dsimp only [errTailWf]; repeat' first | apply And.intro | native_decide) (trMem2_size I) (trMem2_read64 I) (by simp)
  rw [solcErrorStringPayload_eq (msg := "ERC20: insufficient balance".toUTF8) (by native_decide) (by native_decide)
    (by rw [trMem2_size]; omega) (by native_decide) (by native_decide)] at hrev
  exact hrev

/-- After the balance check passed: the debit stored, `GT balT (value + balT)` about to be decided. -/
theorem trCredit {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hle : (trValue I).toNat ≤ (trBal I σ).toNat) :
    ∃ k C, Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x511⟩, trBalT I σ :: trValue I :: ⟨0x3da⟩ :: ⟨0⟩ :: trSlotT I :: trValue I :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ ::
        [solcSelectorWord I], trMem6 I, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, trW1 I σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := trCheck hcode hwv hsize hsel hsz68 hbig hc
  rw [ugt_zero hle] at h
  have h1 := evm_run h with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h1
  have h2 := evm_run h1 with [push2 ⟨0x390⟩, jumpiT (by decide) (by jump_dest), jumpdest, caller, push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (callerW I) (trMem2 I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (trMem4 I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup2,
    raw keccak256 0 (trSlotS I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (callerW I) (trMem2_size I)) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, h3'⟩ := h2.sload (by native_decide) (by evm_ov)
  have h3 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x3a1⟩, trBal I σ :: trSlotS I :: ⟨0⟩ :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], trMem4 I,
        UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ _ _ := h3'
  have h4 := evm_run h3 with [dup5, swap3, swap1, push2 ⟨0x3ae⟩, swap1, dup5, swap1, push2 ⟨0x4fe⟩, jump (by jump_dest)]
  obtain ⟨_, _, h5⟩ := checkedSubOk h4 hle (by jump_dest) (by simp)
  have h6 := evm_run h5 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, h7'⟩ := h6.sstore hperm (by native_decide) (by evm_ov)
  have h7 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x3b2⟩, ⟨0⟩ :: trValue I :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], trMem4 I,
        UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, trW1 I σ, A.logSeries⟩⟩ _ _ := h7'
  have h8 := evm_run h7 with [pop, pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, dup4, and]
  have hland : UInt256.land (trTo I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = trTo I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc
  rw [hland] at h8
  have h9 := evm_run h8 with [push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (trTo I) (trMem4 I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (trMem6 I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup2,
    raw keccak256 0 (trSlotT I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨0⟩ (trTo I) (trMem4_size I)) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, h10'⟩ := h9.sload (by native_decide) (by evm_ov)
  have h10 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x3cd⟩, trBalT I σ :: trSlotT I :: ⟨0⟩ :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], trMem6 I,
        UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, trW1 I σ, A.logSeries⟩⟩ _ _ := h10'
  exact ⟨_, _, evm_run h10 with [dup5, swap3, swap1, push2 ⟨0x3da⟩, swap1, dup5, swap1, push2 ⟨0x511⟩, jump (by jump_dest)]⟩

theorem trRunOverflow {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hle : (trValue I).toNat ≤ (trBal I σ).toNat) (hover : UInt256.size ≤ (trValue I).toNat + (trBalT I σ).toNat) :
    Reverted erc20Runtime (initState σ σ₀ g A I) (panicData 0x11) := by
  obtain ⟨_, _, h⟩ := trCredit hcode hwv hsize hperm hsel hsz68 hbig hc hle
  have hrev := checkedAddOverflow h hover (by simp)
  rw [solcPanicPayload_eq] at hrev
  exact hrev

theorem trRunOk {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hle : (trValue I).toNat ≤ (trBal I σ).toNat) (hfit : (trValue I).toNat + (trBalT I σ).toNat < UInt256.size) :
    Returned erc20Runtime (initState σ σ₀ g A I)
      ⟨A.createdAccounts, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ (trSlotS I) (trDiff I σ)) (trSlotT I) (trSum I σ),
        A.logSeries.push (trLog I)⟩
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, h⟩ := trCredit hcode hwv hsize hperm hsel hsz68 hbig hc hle
  obtain ⟨_, _, h1⟩ := checkedAddOk h hfit (by jump_dest) (by simp)
  have h2 := evm_run h1 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, h3'⟩ := h2.sstore hperm (by native_decide) (by evm_ov)
  have h3 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x3de⟩, ⟨0⟩ :: trValue I :: ⟨0⟩ :: trValue I :: trTo I :: ⟨0x77⟩ :: [solcSelectorWord I], trMem6 I,
        UInt256.ofNat 3, ByteArray.empty,
        ⟨A.createdAccounts, sstoreAccountMap I.codeOwner (trW1 I σ) (trSlotT I) (trSum I σ), A.logSeries⟩⟩ _ _ := h3'
  have hm6 : 96 ≤ (trMem6 I).size := by rw [trMem6_size]
  obtain ⟨hsz7, hr7, hb7⟩ := freePtr_after_write128 (trValue I) hm6 (trMem6_read64 I) (trMem6_gap I)
  have hs7 : 128 + 32 ≤ (trMem7 I).size := toByteArray_write_size_ge_off_add32 _ _ 128 (trMem6_gap I)
  have h4 := evm_run h3 with [pop, pop, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by omega) (trMem6_read64 I)) (by decide) (by evm_ov),
    dup3, dup2,
    raw mstore 6 (trMem7 I) (UInt256.ofNat 5) (by native_decide) mem_cost rfl (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, dup5, and]
  have hland : UInt256.land (trTo I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = trTo I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc
  rw [hland] at h4
  have h5 := evm_run h4 with [swap1, caller, swap1]
  have h6 := h5.pushConst (width := 32) (op := .PUSH32) transferTopic (by decide) (by native_decide) (by evm_ov)
  have h7 := evm_run h6 with [swap1, push1 ⟨0x20⟩, add, push2 ⟨0x16c⟩, jump (by jump_dest), jumpdest, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (mloadFreePtrValue hsz7 hr7)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  rw [show UInt256.sub (⟨32⟩ + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide] at h7
  have h8 := h7.log3 0 (UInt256.ofNat 5) (by native_decide) hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from rfl, hb7] at h8
  have h9 := evm_run h8 with [pop, push1 ⟨1⟩, jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact retBoolTrue (R := [solcSelectorWord I]) (mem := trMem7 I) h9 (by omega) hr7 (lt_usize _ (by omega)) (by simp)

theorem trRunShort {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4)) (hshort : I.calldata.size < 68) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := trEntry hcode hwv hsize hsel
  exact decAddrU256LenRevert h (lenCheck_short (by norm_num) (size_ge_of_sel rfl hsel) hshort) (by simp)

theorem trRunHuge {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4)) (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := trEntry hcode hwv hsize hsel
  exact decAddrU256LenRevert h (lenCheck_huge (by norm_num) hhuge hsize) (by simp)

theorem trRunDirty {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 4))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (trTo I).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := trEntry hcode hwv hsize hsel
  exact decAddrU256DirtyRevert h hsz68 hbig hnc (by simp)

/-! ## The spec derivations -/

def trFrame (a : EVM.Address) (w : UInt256) : Frame :=
  ((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "to" addrTy (some .memory)
    (.address a)).bind "value" u256 (some .memory) (u256Val w.toNat)).bind "#ret0" .bool (some .memory) (.bool false)

def trStmts : Block :=
  [ .exprStmt (.call (.ident "require") [] (.positional
      [ .binary .ge (.index (.ident "balanceOf") msgSender) (.ident "value"), .lit (.str "ERC20: insufficient balance") ])),
    .exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")),
    .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
    .emit (.ident "Transfer") (.positional [msgSender, .ident "to", .ident "value"]),
    .return (some (.lit (.bool true))) ]

theorem trEnter (m : Machine) (a : EVM.Address) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTransfer.decl [.address a, u256Val w.toNat] m =
      some (.ok (trFrame a w, m)) := by
  simp [enterFn, declare, coerce, fnTransfer, trFrame, fuelDefault]
  try rfl

/-- The slot of `balanceOf[msg.sender]`. -/
abbrev sSlot (m : Machine) : UInt256 := balSlot m.evm.executionEnv.source
/-- After the debit. -/
noncomputable abbrev trM1 (m : Machine) (w : UInt256) : Machine :=
  storeU256 m (sSlot m) (UInt256.ofNat ((loadU256 m (sSlot m)).toNat - w.toNat))
/-- After the credit. -/
noncomputable abbrev trM2 (m : Machine) (a : EVM.Address) (w : UInt256) : Machine :=
  storeU256 (trM1 m w) (balSlot a) (UInt256.ofNat ((loadU256 (trM1 m w) (balSlot a)).toNat + w.toNat))
noncomputable abbrev trLe (m : Machine) (a : EVM.Address) (w : UInt256) : LogEntry :=
  { address := (trM2 m a w).this,
    topics := #[hashWord evTransfer.sigStr.toUTF8, UInt256.ofNat (trM2 m a w).evm.executionEnv.source.toNat,
      UInt256.ofNat a.toNat],
    data := UInt256.toByteArray w }
noncomputable abbrev trFinal (m : Machine) (a : EVM.Address) (w : UInt256) : Machine := (trM2 m a w).pushLog (trLe m a w)

theorem trCond (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m
      (.binary .ge (.index (.ident "balanceOf") msgSender) (.ident "value"))
      (.ok (.bool (decide (w.toNat ≤ (loadU256 m (sSlot m)).toNat))) (bodyFrame (trFrame a w) trStmts) m) :=
  EvalExpr.geU256 (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, trFrame]))
    (EvalExpr.mappingAddrU256 (by frame_simp [bodyFrame, trFrame]) erc20Flat_var_balanceOf rfl rfl EvalExpr.msgSender
      (erc20Leaf_balanceOf _))

theorem trBodyInsufficient (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hlt : (loadU256 m (sSlot m)).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m trStmts
      (.reverted (errorStringData "ERC20: insufficient balance".toUTF8)) := by
  have hc := trCond o m a w
  rw [decide_eq_false (by omega)] at hc
  exact ExecBlock.consRevert (ExecStmt.requireMsgRevert hc)

theorem trDebit (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) (hle : w.toNat ≤ (loadU256 m (sSlot m)).toNat) :
    ExecStmt erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m
      (.exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")))
      (.normal (bodyFrame (trFrame a w) trStmts) (trM1 m w)) :=
  ExecStmt.subAssignU256 (b := w) (slot := sSlot m) (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, trFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, trFrame]) erc20Flat_var_balanceOf rfl rfl EvalExpr.msgSender)
    (erc20Leaf_balanceOf _) (by frame_simp [bodyFrame, trFrame]) hle

theorem trBodyOverflow (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hle : w.toNat ≤ (loadU256 m (sSlot m)).toNat)
    (hover : UInt256.size ≤ (loadU256 (trM1 m w) (balSlot a)).toNat + w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m trStmts (.reverted (panicData 0x11)) := by
  have hc := trCond o m a w
  rw [decide_eq_true hle] at hc
  refine ExecBlock.cons (ExecStmt.requireTrue hc) (ExecBlock.cons (trDebit o m a w hle) (ExecBlock.consRevert ?_))
  exact ExecStmt.addAssignU256Overflow (b := w) (slot := balSlot a)
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, trFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, trFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, trFrame])))
    (erc20Leaf_balanceOf a) (by frame_simp [bodyFrame, trFrame]) hover

theorem trBodyOk (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hle : w.toNat ≤ (loadU256 m (sSlot m)).toNat)
    (hfit : (loadU256 (trM1 m w) (balSlot a)).toNat + w.toNat < UInt256.size) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m trStmts
      (.returned ((bodyFrame (trFrame a w) trStmts).setVal "#ret0" (.bool true)) (trFinal m a w)) := by
  have hc := trCond o m a w
  rw [decide_eq_true hle] at hc
  refine ExecBlock.cons (ExecStmt.requireTrue hc) (ExecBlock.cons (trDebit o m a w hle) ?_)
  refine ExecBlock.cons (ExecStmt.addAssignU256 (b := w) (slot := balSlot a)
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, trFrame]))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, trFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, trFrame])))
    (erc20Leaf_balanceOf a) (by frame_simp [bodyFrame, trFrame]) hfit) ?_
  refine ExecBlock.cons (ExecStmt.emitAddrAddrU256 (a := (trM2 m a w).evm.executionEnv.source) (b := a) (n := w)
    erc20Flat_eventsNamed_Transfer rfl rfl rfl
    (EvalExprs.three EvalExpr.msgSender (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, trFrame]))
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, trFrame])))) ?_
  exact ExecBlock.consReturn (ExecStmt.returnBool { ty := .bool, loc := some .memory, val := .bool false } rfl
    (EvalExpr.boolLit true) (by frame_simp [bodyFrame, trFrame]) rfl (by frame_simp [bodyFrame, trFrame]))

theorem trCallOk (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hle : w.toNat ≤ (loadU256 m (sSlot m)).toNat)
    (hfit : (loadU256 (trM1 m w) (balSlot a)).toNat + w.toNat < UInt256.size) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransfer [.address a, u256Val w.toNat]
      (.ok [.bool true] (trFinal m a w)) :=
  CallFn.plain (trEnter m a w) rfl rfl (trBodyOk o m a w hle hfit) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, trFrame]) (by frame_simp [bodyFrame, trFrame])
      (by frame_simp [retVals, bodyFrame, trFrame]))

theorem trCallRevert (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) {d : ByteArray}
    (hb : ExecBlock erc20Cfg o erc20Flat (bodyFrame (trFrame a w) trStmts) m trStmts (.reverted d)) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransfer [.address a, u256Val w.toNat] (.reverted d) :=
  CallFn.plainRevert (trEnter m a w) rfl rfl hb

abbrev trToA (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (trTo I).toNat

theorem trArgs {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc : (trTo I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata =
      some [.address (trToA I), .int (Int.ofNat (trValue I).toNat)] := by
  rw [decodeArgs_transfer]; exact decodeCalldataValues_addr_uint256_ok hsz68 hbig hc

theorem trBind (I : ExecutionEnv) :
    ofAbiParams erc20Flat.types I.calldata fnTransfer.decl.params [.address (trToA I), .int (Int.ofNat (trValue I).toNat)] {} =
      some ([.address (trToA I), u256Val (trValue I).toNat], {}) := by
  simp [ofAbiParams, fnTransfer, fuelDefault, calldataRef]

theorem trSpecOk (o : Oracle) {σ σ₀ g A I} (hsel : selIs I (selBytes 4)) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hle : (trValue I).toNat ≤ (loadU256 (initMachine σ σ₀ g A I ∅) (sSlot (initMachine σ σ₀ g A I ∅))).toNat)
    (hfit : (loadU256 (trM1 (initMachine σ σ₀ g A I ∅) (trValue I)) (balSlot (trToA I))).toNat + (trValue I).toNat <
      UInt256.size) :
    solidityExec erc20Cfg o erc20Flat ∅ σ σ₀ g A I
      (.returned (trFinal (initMachine σ σ₀ g A I ∅) (trToA I) (trValue I)) [.bool true]) (.abi [.elem .bool]) := by
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault
      (trFinal (initMachine σ σ₀ g A I ∅) (trToA I) (trValue I)).heap [.bool true] =
      some (.ok ([.bool true], (trFinal (initMachine σ σ₀ g A I ∅) (trToA I) (trValue I)).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp)
  exact solidityExec.call (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv) rfl (trArgs hsz68 hbig hc) (trBind I)
    (trCallOk o (initMachine σ σ₀ g A I ∅) (trToA I) (trValue I) hle hfit) hprep (by simp [fuelDefault])

theorem trSpecRevert (o : Oracle) {σ σ₀ g A I} {d : ByteArray} (hsel : selIs I (selBytes 4)) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) (hc : (trTo I).toNat < EVM.addressModulus)
    (hb : ExecBlock erc20Cfg o erc20Flat (bodyFrame (trFrame (trToA I) (trValue I)) trStmts) (initMachine σ σ₀ g A I ∅)
      trStmts (.reverted d)) :
    solidityExec erc20Cfg o erc20Flat ∅ σ σ₀ g A I (.reverted d) (.abi [.elem .bool]) :=
  solidityExec.callReverted (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv) rfl (trArgs hsz68 hbig hc) (trBind I)
    (trCallRevert o _ _ _ hb)

/-! ## The coupled result -/

theorem transferCorrect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I (selBytes 4)) :
    runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hdec : decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata = none →
      Reverted erc20Runtime (initState σ σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty →
      runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := fun hd h =>
    Reverted.specDecodingFailed hcode h (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv)
      (decodeCallArgs_none_of_decodeArgs hd)
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : (trTo I).toNat < EVM.addressModulus
      · -- the spec's machine and the bytecode's words
        set m0 := initMachine σ σ₀ g A I ∅ with hm0
        have hw0 : WorldEquiv ⟨A.createdAccounts, σ, A.logSeries⟩ m0 := WorldEquiv.init ∅ {}
        have hslotS : sSlot m0 = trSlotS I := by
          simp only [sSlot, balSlot_eq, hm0, initMachine_executionEnv, trSlotS, callerW]
        have hslotT : balSlot (trToA I) = trSlotT I := by
          rw [balSlot_eq]
          show solcMappingSlot ⟨0⟩ (UInt256.ofNat (AccountAddress.ofNat (trTo I).toNat).toNat) = _
          rw [addrWord_canon hc]
        have hbal : trBal I σ = loadU256 m0 (sSlot m0) := by rw [hslotS]; exact hw0.sload rfl _
        by_cases hle : (trValue I).toNat ≤ (trBal I σ).toNat
        · have hle' : (trValue I).toNat ≤ (loadU256 m0 (sSlot m0)).toNat := by rw [← hbal]; exact hle
          have hd : UInt256.ofNat ((loadU256 m0 (sSlot m0)).toNat - (trValue I).toNat) = trDiff I σ := by
            have hb : (trBal I σ).toNat < UInt256.size := (trBal I σ).val.isLt
            rw [← hbal]; apply u256_inj; rw [ulit_toNat' _ (by omega), usub_toNat hle]
          have hw1 : WorldEquiv ⟨A.createdAccounts, trW1 I σ, A.logSeries⟩ (trM1 m0 (trValue I)) := by
            show WorldEquiv ⟨A.createdAccounts, sstoreAccountMap I.codeOwner σ (trSlotS I) (trDiff I σ), A.logSeries⟩ _
            rw [← hd, ← hslotS]
            exact hw0.sstore (owner := I.codeOwner) rfl (sSlot m0) _
          have hown1 : I.codeOwner = (trM1 m0 (trValue I)).evm.executionEnv.codeOwner := by
            rw [storeU256_executionEnv, hm0, initMachine_executionEnv]
          have hbalT : trBalT I σ = loadU256 (trM1 m0 (trValue I)) (balSlot (trToA I)) := by
            rw [hslotT]; exact hw1.sload (I := I) hown1 (trSlotT I)
          by_cases hfit : (trValue I).toNat + (trBalT I σ).toNat < UInt256.size
          · have hfit' : (loadU256 (trM1 m0 (trValue I)) (balSlot (trToA I))).toNat + (trValue I).toNat < UInt256.size := by
              rw [← hbalT]; omega
            have hsum : UInt256.ofNat ((loadU256 (trM1 m0 (trValue I)) (balSlot (trToA I))).toNat + (trValue I).toNat) =
                trSum I σ := by
              rw [← hbalT]; apply u256_inj
              rw [ulit_toNat' _ (by omega), uadd_toNat, Nat.add_comm, Nat.mod_eq_of_lt (by omega)]
            have hw2 : WorldEquiv ⟨A.createdAccounts, sstoreAccountMap I.codeOwner (trW1 I σ) (trSlotT I) (trSum I σ), A.logSeries⟩
                (trM2 m0 (trToA I) (trValue I)) := by
              rw [← hsum, ← hslotT]
              exact hw1.sstore (owner := I.codeOwner) hown1 (balSlot (trToA I)) _
            have hle2 : trLe m0 (trToA I) (trValue I) = trLog I := by
              simp only [trLe, Machine.this, trM2, trM1, storeU256, storageStore_executionEnv, hm0, initMachine_executionEnv,
                evTransfer_topic, addrWord_canon hc, trLog, transferTopic, callerW]
              rfl
            have hw3 := hw2.pushLog (trLe m0 (trToA I) (trValue I))
            have hrun := trRunOk (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
              hcode hwv hsize hperm hsel hsz68 hbig hc hle hfit
            rw [← hle2] at hrun
            exact Returned.specExecutionW default hcode hrun (trSpecOk default hsel hwv hsz68 hbig hc hle' hfit') hw3
              (.abi boolTrueReturnEncoding)
          · have hover : UInt256.size ≤ (loadU256 (trM1 m0 (trValue I)) (balSlot (trToA I))).toNat + (trValue I).toNat := by
              rw [← hbalT]; omega
            exact Reverted.specRevert default hcode
              (trRunOverflow hcode hwv hsize hperm hsel hsz68 hbig hc hle (by omega))
              (trSpecRevert default hsel hwv hsz68 hbig hc (trBodyOverflow default m0 (trToA I) (trValue I) hle' hover))
        · have hlt : (loadU256 m0 (sSlot m0)).toNat < (trValue I).toNat := by rw [← hbal]; omega
          exact Reverted.specRevert default hcode (trRunInsufficient hcode hwv hsize hsel hsz68 hbig hc (by omega))
            (trSpecRevert default hsel hwv hsz68 hbig hc (trBodyInsufficient default m0 (trToA I) (trValue I) hlt))
      · exact hdec (by rw [decodeArgs_transfer]; exact decodeCalldataValues_addr_uint256_none_noncanon hsz68 hbig hc)
          (trRunDirty hcode hwv hsize hsel hsz68 hbig hc)
    · exact hdec (by rw [decodeArgs_transfer]; exact decodeCalldataValues_addr_uint256_none_huge (by omega))
        (trRunHuge hcode hwv hsize hsel (by omega))
  · exact hdec (by rw [decodeArgs_transfer]; exact decodeCalldataValues_addr_uint256_none_short hsz4 (by omega))
      (trRunShort hcode hwv hsize hsel (by omega))

end ERC20.Opt
