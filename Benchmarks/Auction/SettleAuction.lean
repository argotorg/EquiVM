import Benchmarks.Auction.Unpause
import Benchmarks.Auction.SettleAuctionTrace

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionNatLorLowBool20High (a q : Nat) (ha : a < 2 ^ 160) :
    Nat.lor (2 ^ 160) (Nat.lor a (q * 2 ^ 168)) =
      a + 2 ^ 160 + q * 2 ^ 168 := by
  have hcomm3 :
      Nat.lor (2 ^ 160) (Nat.lor a (q * 2 ^ 168)) =
        Nat.lor a (Nat.lor (2 ^ 160) (q * 2 ^ 168)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show Nat.lor (2 ^ 160) (Nat.lor a (q * 2 ^ 168)) =
        (2 ^ 160) ||| (a ||| (q * 2 ^ 168)) from rfl]
    rw [show Nat.lor a (Nat.lor (2 ^ 160) (q * 2 ^ 168)) =
        a ||| ((2 ^ 160) ||| (q * 2 ^ 168)) from rfl]
    repeat rw [Nat.testBit_or]
    simp [Bool.or_left_comm]
  rw [hcomm3]
  rw [nat_lor_shift_add (2 ^ 160) q 168 (by norm_num)]
  rw [show 2 ^ 160 + q * 2 ^ 168 = (1 + q * 2 ^ 8) * 2 ^ 160 by ring]
  rw [nat_lor_shift_add a (1 + q * 2 ^ 8) 160 ha]
  ring

theorem auctionSetBoolOffset20TrueWord_eq_evm (old : UInt256) :
    UInt256.lor (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩)) old) =
      auctionSetBoolOffset20TrueWord old := by
  unfold auctionSetBoolOffset20TrueWord
  apply u256_inj
  rw [u256_lor_toNat, u256_land_toNat]
  have hmask :
      (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩)).toNat =
        Nat.lor (2 ^ 160 - 1) (2 ^ 256 - 2 ^ 168) := by
    native_decide
  have hset : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 := by
    native_decide
  rw [hmask, hset]
  rw [nat_land_comm (Nat.lor (2 ^ 160 - 1) (2 ^ 256 - 2 ^ 168)) old.toNat]
  have hmaskLt : Nat.lor (2 ^ 160 - 1) (2 ^ 256 - 2 ^ 168) < UInt256.size := by
    native_decide
  have hland_lt :
      Nat.land old.toNat (Nat.lor (2 ^ 160 - 1) (2 ^ 256 - 2 ^ 168)) <
        UInt256.size := by
    exact lt_of_le_of_lt (nat_land_le_right _ _) hmaskLt
  rw [Nat.mod_eq_of_lt hland_lt]
  rw [natLand_lor]
  rw [nat_land_mask_eq_mod old.toNat 160]
  rw [natLandClearLow old.toNat 168 (by norm_num) old.val.isLt]
  have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
  rw [auctionNatLorLowBool20High (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 168) hlow]
  rw [ulit_toNat' _ (auctionSetBoolOffset20TrueNat_lt_size old)]
  rw [Nat.mod_eq_of_lt (auctionSetBoolOffset20TrueNat_lt_size old)]

theorem auctionDispatch_settleAuction {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 13)) :
    dispatchMsg auctionContract I.calldata = some settleAuctionTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition])
    (post := [pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter])
    (ti := settleAuctionTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 13 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, settleAuctionSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_settleAuction {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
      (settleAuctionTransition.params.map Param.name)
      (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachSettleAuctionBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 13)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨765⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xa4, 0xd0, 0xa1, 0x7e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xa4d0a17e⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xa4 0xd0 0xa1 0x7e ⟨0xa4d0a17e⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper :
      UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    decide
  have h98 := RD.selectorSplitTakenAuto h29 auctionUpperSplitWellFormed hupper
    (by jump_dest) (by simp)
  have h99 := h98.jumpdest (by decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc 3))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨765⟩ 3 h99
    (fun j hj => auctionUpperLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_settleAuction_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨765⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd765⟩ := hreach
  exact evm_run rd765 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨776⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleAuctionX_toBody {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨765⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2351⟩
      [⟨413⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd765⟩ := hreach
  exact ⟨_, _, evm_run rd765 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨776⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨2351⟩, jump (by jump_dest)]⟩

theorem auctionX_settleAuction_revert_paused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2351⟩ := auctionSettleAuctionX_toBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2355₀ := evm_run rd2351 with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2355₁⟩ := rd2355₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2355⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2355⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2355₁⟩
  have rd2358 := evm_run rd2355 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = ⟨0⟩ := by
    simpa [hmask] using hzero
  have rd2365 := evm_run rd2358 with [
    push2 ⟨2424⟩, jumpiNT hcond,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2369 := rd2365.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2388 := evm_run rd2369 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨20⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2409 := rd2388.pushConst auctionPausableNotPausedRawStringWord
    (width := 20) (op := .PUSH20) (by decide) (by decide) (by evm_ov)
  have rd2412₀ := evm_run rd2409 with [push1 ⟨98⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausableNotPausedRawStringWord ⟨98⟩ =
        auctionPausableNotPausedStringWord := by
    native_decide
  have rd2412 := rd2412₀
  rw [hword] at rd2412
  have rd2419₀ := evm_run rd2412 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨20⟩ auctionPausableNotPausedStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd2419 := rd2419₀
  rw [show (⟨100⟩ : UInt256) + ⟨128⟩ = ⟨228⟩ by decide] at rd2419
  have rd994 := evm_run rd2419 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨20⟩ auctionPausableNotPausedStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleAuctionX_toStatusGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2424⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2351⟩ := auctionSettleAuctionX_toBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := auctionSelWord I) hreach hwv
  have rd2355₀ := evm_run rd2351 with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2355₁⟩ := rd2355₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2355⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2355⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2355₁⟩
  have rd2358 := evm_run rd2355 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) ≠ ⟨0⟩ := by
    simpa [hmask] using hpaused
  exact ⟨_, _, evm_run rd2358 with [push2 ⟨2424⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionX_toStatusOpen {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2458⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2424⟩ := auctionSettleAuctionX_toStatusGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hpaused hreach
  have rd2429₀ := evm_run rd2424 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2429₁⟩ := rd2429₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2430⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2430⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2429₁⟩
  have rd2431 := evm_run rd2430 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne hstatus
  exact ⟨_, _, evm_run rd2431 with [push2 ⟨2458⟩, jumpiT hcond (by jump_dest)]⟩

theorem auctionSettleAuctionX_toInternalSettleAuction {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4086⟩
      [⟨2471⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
  obtain ⟨_, _, rd2458⟩ := auctionSettleAuctionX_toStatusOpen
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hpaused hstatus hreach
  have rd2463 := evm_run rd2458 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2464₀⟩ := rd2463.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd2464⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2464⟩
      [⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSettleAuctionEnterMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionSettleAuctionEnterMap] using rd2464₀⟩
  exact ⟨_, _, evm_run rd2464 with [push2 ⟨2471⟩, push2 ⟨4086⟩, jump (by jump_dest)]⟩

theorem auctionSolcErrorStringMem0_read64 :
    (solcErrorStringMem0 solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem0
  have hread : 64 + 32 ≤ solcFreePtrMem.size := by
    rw [solcFreePtrMem_size]
  have hbelow : 64 + 32 ≤ 128 := by omega
  have hgap : 128 - solcFreePtrMem.size < USize.size := by
    rw [solcFreePtrMem_size]
    exact lt_usize _ (by norm_num)
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector solcFreePtrMem 128 64
      hread hbelow hgap]
  exact solcFreePtrMem_read64

theorem auctionSolcErrorStringMem0_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem0 solcFreePtrMem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem0 solcFreePtrMem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  change (if 64 ≥ (solcErrorStringMem0 solcFreePtrMem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem0 solcFreePtrMem).readWithPadding 64 32))) = ⟨128⟩
  rw [auctionSolcErrorStringMem0_read64, solcErrorStringMem0_size solcFreePtrMem_size,
    fromByteArrayBigEndian_toByteArray]
  decide

noncomputable def auctionSettleAuctionSnapshotFreeMem : ByteArray :=
  (UInt256.toByteArray (⟨320⟩ : UInt256)).write 0 solcFreePtrMem 64 32

noncomputable def auctionSettleAuctionSnapshotNounMem (noun : UInt256) : ByteArray :=
  (UInt256.toByteArray noun).write 0 auctionSettleAuctionSnapshotFreeMem 128 32

noncomputable def auctionSettleAuctionSnapshotAmountMem
    (noun amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (auctionSettleAuctionSnapshotNounMem noun) 160 32

noncomputable def auctionSettleAuctionSnapshotStartMem
    (noun amount start : UInt256) : ByteArray :=
  (UInt256.toByteArray start).write 0
    (auctionSettleAuctionSnapshotAmountMem noun amount) 192 32

noncomputable def auctionSettleAuctionSnapshotEndMem
    (noun amount start finish : UInt256) : ByteArray :=
  (UInt256.toByteArray finish).write 0
    (auctionSettleAuctionSnapshotStartMem noun amount start) 224 32

noncomputable def auctionSettleAuctionSnapshotBidderMem
    (noun amount start finish bidder : UInt256) : ByteArray :=
  (UInt256.toByteArray bidder).write 0
    (auctionSettleAuctionSnapshotEndMem noun amount start finish) 256 32

noncomputable def auctionSettleAuctionSnapshotMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray settled).write 0
    (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder) 288 32

theorem auctionSettleAuctionSnapshotFreeMem_size :
    auctionSettleAuctionSnapshotFreeMem.size = 96 := by
  unfold auctionSettleAuctionSnapshotFreeMem
  exact toByteArray_write32_size_of_le solcFreePtrMem (⟨320⟩ : UInt256) 64 96 96
    solcFreePtrMem_size (by rw [solcFreePtrMem_size]; omega) (by decide)

theorem auctionSettleAuctionSnapshotNounMem_size (noun : UInt256) :
    (auctionSettleAuctionSnapshotNounMem noun).size = 160 := by
  unfold auctionSettleAuctionSnapshotNounMem
  exact toByteArray_write32_size_of_ge auctionSettleAuctionSnapshotFreeMem noun 128 96 160
    auctionSettleAuctionSnapshotFreeMem_size (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionSnapshotAmountMem_size (noun amount : UInt256) :
    (auctionSettleAuctionSnapshotAmountMem noun amount).size = 192 := by
  unfold auctionSettleAuctionSnapshotAmountMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotNounMem noun) amount 160 160 192
    (auctionSettleAuctionSnapshotNounMem_size noun) (by omega) (lt_usize _ (by norm_num))
    rfl

theorem auctionSettleAuctionSnapshotStartMem_size (noun amount start : UInt256) :
    (auctionSettleAuctionSnapshotStartMem noun amount start).size = 224 := by
  unfold auctionSettleAuctionSnapshotStartMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotAmountMem noun amount) start 192 192 224
    (auctionSettleAuctionSnapshotAmountMem_size noun amount) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionSnapshotEndMem_size (noun amount start finish : UInt256) :
    (auctionSettleAuctionSnapshotEndMem noun amount start finish).size = 256 := by
  unfold auctionSettleAuctionSnapshotEndMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotStartMem noun amount start) finish 224 224 256
    (auctionSettleAuctionSnapshotStartMem_size noun amount start) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionSnapshotBidderMem_size
    (noun amount start finish bidder : UInt256) :
    (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder).size = 288 := by
  unfold auctionSettleAuctionSnapshotBidderMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotEndMem noun amount start finish) bidder 256 256 288
    (auctionSettleAuctionSnapshotEndMem_size noun amount start finish) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionSnapshotMem_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size = 320 := by
  unfold auctionSettleAuctionSnapshotMem
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder) settled 288 288 320
    (auctionSettleAuctionSnapshotBidderMem_size noun amount start finish bidder) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionSettleAuctionSnapshotFreeMem_read64 :
    auctionSettleAuctionSnapshotFreeMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionSettleAuctionSnapshotFreeMem
  exact toByteArray_write_read_back_of_gap (⟨320⟩ : UInt256) solcFreePtrMem 64
    (by rw [solcFreePtrMem_size]; change 0 < USize.size; exact USize.size_pos)

theorem auctionSettleAuctionSnapshotMem_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 64
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 64
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 64
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 64
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotAmountMem
  rw [toByteArray_write_read_below_of_gap amount _ 160 64
    (by rw [auctionSettleAuctionSnapshotNounMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotNounMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotNounMem
  rw [toByteArray_write_read_below_of_gap noun auctionSettleAuctionSnapshotFreeMem 128 64
    (by rw [auctionSettleAuctionSnapshotFreeMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotFreeMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotFreeMem_read64

theorem auctionSettleAuctionSnapshotMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

theorem auctionSettleAuctionSnapshotMem_read128_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        128 32 =
      UInt256.toByteArray noun := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 128
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 128
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 128
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 128
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotAmountMem
  rw [toByteArray_write_read_below_of_gap amount _ 160 128
    (by rw [auctionSettleAuctionSnapshotNounMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotNounMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotNounMem
  exact toByteArray_write_read_back_of_gap noun auctionSettleAuctionSnapshotFreeMem 128
    (by rw [auctionSettleAuctionSnapshotFreeMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload128
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      noun :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read128_word noun amount start finish bidder settled)

theorem auctionSettleAuctionSnapshotMem_read224_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        224 32 =
      UInt256.toByteArray finish := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 224
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 224
    (by rw [auctionSettleAuctionSnapshotEndMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotEndMem
  exact toByteArray_write_read_back_of_gap finish
    (auctionSettleAuctionSnapshotStartMem noun amount start) 224
    (by rw [auctionSettleAuctionSnapshotStartMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload224
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      finish :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read224_word noun amount start finish bidder settled)

theorem auctionSettleAuctionSnapshotMem_read256_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        256 32 =
      UInt256.toByteArray bidder := by
  unfold auctionSettleAuctionSnapshotMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 256
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]) (by omega)
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionSettleAuctionSnapshotBidderMem
  exact toByteArray_write_read_back_of_gap bidder
    (auctionSettleAuctionSnapshotEndMem noun amount start finish) 256
    (by rw [auctionSettleAuctionSnapshotEndMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload256
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      bidder :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read256_word noun amount start finish bidder settled)

theorem auctionSettleAuctionSnapshotMem_read288_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).readWithPadding
        288 32 =
      UInt256.toByteArray settled := by
  unfold auctionSettleAuctionSnapshotMem
  exact toByteArray_write_read_back_of_gap settled
    (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder) 288
    (by rw [auctionSettleAuctionSnapshotBidderMem_size]; exact lt_usize _ (by norm_num))

theorem auctionSettleAuctionSnapshotMem_mload288
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
            |>.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      settled :=
  mloadWordValue_of_readWithPadding
    (by rw [auctionSettleAuctionSnapshotMem_size]; decide)
    (by decide)
    (auctionSettleAuctionSnapshotMem_read288_word noun amount start finish bidder settled)

def auctionAuctionHasntBegunRawStringWord : UInt256 :=
  ⟨0x20bab1ba34b7b7103430b9b713ba103132b3bab7⟩

def auctionAuctionHasntBegunStringWord : UInt256 :=
  ⟨0x41756374696f6e206861736e277420626567756e000000000000000000000000⟩

noncomputable def auctionAuctionHasntStartedMem0
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled) 320 32

noncomputable def auctionAuctionHasntStartedMem1
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled) 324 32

noncomputable def auctionAuctionHasntStartedMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨20⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionAuctionHasntStartedMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionAuctionHasntBegunStringWord).write 0
    (auctionAuctionHasntStartedMem2 noun amount start finish bidder settled) 388 32

theorem auctionAuctionHasntStartedMem0_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled).size = 352 := by
  unfold auctionAuctionHasntStartedMem0
  exact toByteArray_write32_size_of_ge
    (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
    solcErrorStringSelector 320 320 352
    (auctionSettleAuctionSnapshotMem_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionHasntStartedMem1_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled).size = 356 := by
  unfold auctionAuctionHasntStartedMem1
  exact toByteArray_write32_size_of_le
    (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
    (⟨32⟩ : UInt256) 324 352 356
    (auctionAuctionHasntStartedMem0_size noun amount start finish bidder settled)
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by decide)

theorem auctionAuctionHasntStartedMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntStartedMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionAuctionHasntStartedMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) (⟨20⟩ : UInt256)
    356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionHasntStartedMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntStartedMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionAuctionHasntStartedMem3
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem2 noun amount start finish bidder settled)
    auctionAuctionHasntBegunStringWord 388 388 420
    (auctionAuctionHasntStartedMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionHasntStartedMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntStartedMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionAuctionHasntStartedMem3
  rw [toByteArray_write_read_below_of_gap auctionAuctionHasntBegunStringWord _ 388 64
    (by rw [auctionAuctionHasntStartedMem2_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem2
  rw [toByteArray_write_read_below_of_gap (⟨20⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionAuctionHasntStartedMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionAuctionHasntStartedMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionAuctionHasntStartedMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionAuctionHasntStartedMem3_size]; decide)
    (auctionAuctionHasntStartedMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

def auctionAuctionAlreadySettledStringWord : UInt256 :=
  ⟨0x41756374696f6e2068617320616c7265616479206265656e20736574746c6564⟩

noncomputable def auctionAuctionAlreadySettledMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionAuctionAlreadySettledMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionAuctionAlreadySettledStringWord).write 0
    (auctionAuctionAlreadySettledMem2 noun amount start finish bidder settled) 388 32

theorem auctionAuctionAlreadySettledMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionAlreadySettledMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionAuctionAlreadySettledMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨32⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionAlreadySettledMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionAuctionAlreadySettledMem3
  exact toByteArray_write32_size_of_ge
    (auctionAuctionAlreadySettledMem2 noun amount start finish bidder settled)
    auctionAuctionAlreadySettledStringWord 388 388 420
    (auctionAuctionAlreadySettledMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionAlreadySettledMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionAuctionAlreadySettledMem3
  rw [toByteArray_write_read_below_of_gap auctionAuctionAlreadySettledStringWord _ 388 64
    (by rw [auctionAuctionAlreadySettledMem2_size]; omega) (by omega)
    (by rw [auctionAuctionAlreadySettledMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionAlreadySettledMem2
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionAuctionAlreadySettledMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionAuctionAlreadySettledMem3_size]; decide)
    (auctionAuctionAlreadySettledMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

def auctionAuctionHasntCompletedStringWord : UInt256 :=
  ⟨0x41756374696f6e206861736e277420636f6d706c657465640000000000000000⟩

noncomputable def auctionAuctionHasntCompletedMem2
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨24⟩ : UInt256)).write 0
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled) 356 32

noncomputable def auctionAuctionHasntCompletedMem3
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionAuctionHasntCompletedStringWord).write 0
    (auctionAuctionHasntCompletedMem2 noun amount start finish bidder settled) 388 32

theorem auctionAuctionHasntCompletedMem2_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntCompletedMem2 noun amount start finish bidder settled).size = 388 := by
  unfold auctionAuctionHasntCompletedMem2
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
    (⟨24⟩ : UInt256) 356 356 388
    (auctionAuctionHasntStartedMem1_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionHasntCompletedMem3_size
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled).size = 420 := by
  unfold auctionAuctionHasntCompletedMem3
  exact toByteArray_write32_size_of_ge
    (auctionAuctionHasntCompletedMem2 noun amount start finish bidder settled)
    auctionAuctionHasntCompletedStringWord 388 388 420
    (auctionAuctionHasntCompletedMem2_size noun amount start finish bidder settled)
    (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionHasntCompletedMem3_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold auctionAuctionHasntCompletedMem3
  rw [toByteArray_write_read_below_of_gap auctionAuctionHasntCompletedStringWord _ 388 64
    (by rw [auctionAuctionHasntCompletedMem2_size]; omega) (by omega)
    (by rw [auctionAuctionHasntCompletedMem2_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntCompletedMem2
  rw [toByteArray_write_read_below_of_gap (⟨24⟩ : UInt256) _ 356 64
    (by rw [auctionAuctionHasntStartedMem1_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem1_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 324 64
    (by rw [auctionAuctionHasntStartedMem0_size]; omega) (by omega)
    (by rw [auctionAuctionHasntStartedMem0_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionHasntStartedMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 320 64
    (by rw [auctionSettleAuctionSnapshotMem_size]; omega) (by omega)
    (by rw [auctionSettleAuctionSnapshotMem_size]; exact lt_usize _ (by norm_num))]
  exact auctionSettleAuctionSnapshotMem_read64 noun amount start finish bidder settled

theorem auctionAuctionHasntCompletedMem3_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ :=
  mload64_of_readWithPadding_of_aw
    (by rw [auctionAuctionHasntCompletedMem3_size]; decide)
    (auctionAuctionHasntCompletedMem3_read64 noun amount start finish bidder settled)
    (by decide) (by decide)

def auctionReentrancyGuardReentrantStringWord : UInt256 :=
  ⟨0x5265656e7472616e637947756172643a207265656e7472616e742063616c6c00⟩

theorem auctionX_settleAuction_revert_statusEntered {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I = ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2424⟩ := auctionSettleAuctionX_toStatusGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hpaused hreach
  have rd2429₀ := evm_run rd2424 with [jumpdest, push1 ⟨2⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd2429₁⟩ := rd2429₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2430⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2430⟩
      (auctionSlotWord ⟨101⟩ σ I :: ⟨2⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2429₁⟩
  have rd2431 := evm_run rd2430 with [sub]
  have hcond : UInt256.sub (auctionSlotWord ⟨101⟩ σ I) ⟨2⟩ = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rd2438 := evm_run rd2431 with [
    push2 ⟨2458⟩, jumpiNT hcond,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2442 := rd2438.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd2450 := evm_run rd2442 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add]
  obtain ⟨_, _, rd2450'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2450⟩
      [((⟨4⟩ : UInt256) + ⟨128⟩), ⟨413⟩, auctionSelWord I]
      (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd2450⟩
  have rd5575 := evm_run rd2450' with [
    push2 ⟨994⟩, swap1, push2 ⟨5575⟩, jump (by jump_dest)]
  have rd5587 := evm_run rd5575 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨31⟩, swap1, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨31⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5620 := rd5587.pushConst auctionReentrancyGuardReentrantStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd5629₀ := evm_run rd5620 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨31⟩ auctionReentrancyGuardReentrantStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5629 := rd5629₀
  rw [show (⟨96⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨128⟩) = ⟨228⟩ by decide]
    at rd5629
  have rd994 := evm_run rd5629 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨31⟩ auctionReentrancyGuardReentrantStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleAuctionX_toSnapshotCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I, ⟨2471⟩,
        ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty (cA, auctionSettleAuctionEnterMap σ I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  obtain ⟨_, _, rd4086⟩ := auctionSettleAuctionX_toInternalSettleAuction
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hwv hpaused hstatus hreach
  have rd4096 := evm_run rd4086 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨192⟩, dup2, add, dup3,
    raw mstore 0 auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4100₀⟩ := (evm_run rd4096 with [push1 ⟨207⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4100⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4100⟩
      (noun :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [noun, auctionAuctionNounWord, auctionSlotWord, σ1] using rd4100₀⟩
  have rd4102 := evm_run rd4100 with [
    dup2,
    raw mstore 6 (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4105₀⟩ := (evm_run rd4102 with [push1 ⟨208⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4105⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4105⟩
      (amount :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [amount, auctionAuctionAmountWord, auctionSlotWord, σ1] using rd4105₀⟩
  have rd4109 := evm_run rd4105 with [
    push1 ⟨32⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4113₀⟩ := (evm_run rd4109 with [push1 ⟨209⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4113⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4113⟩
      (start :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [start, auctionAuctionStartWord, auctionSlotWord, σ1] using rd4113₀⟩
  have rd4119 := evm_run rd4113 with [
    swap2, dup2, add, dup3, swap1,
    raw mstore 3 (auctionSettleAuctionSnapshotStartMem noun amount start)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4122₀⟩ := (evm_run rd4119 with [push1 ⟨210⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4122⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4122⟩
      (finish :: ⟨128⟩ :: start :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotStartMem noun amount start) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [finish, auctionAuctionEndWord, auctionSlotWord, σ1] using rd4122₀⟩
  have rd4126 := evm_run rd4122 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotEndMem noun amount start finish)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4130₀⟩ := (evm_run rd4126 with [push1 ⟨211⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4130⟩
      (packed :: ⟨128⟩ :: start :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotEndMem noun amount start finish) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1] using rd4130₀⟩
  have rd4144 := evm_run rd4130 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add]
  have rd4145 := evm_run rd4144 with [
    raw mstore 3 (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder)
      (UInt256.ofNat 9) (by decide) mem_cost
      (by
        dsimp [bidder, auctionPackedBidderWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by native_decide]
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd4161 := evm_run rd4145 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and,
    iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) (by decide) mem_cost
      (by
        dsimp [settled, auctionPackedSettledEVMReturnWord, auctionPackedSettledEVMWord,
          auctionPackedSettledBaseWord]
        rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4161⟩

theorem auctionX_settleAuction_revert_notStarted {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartEnter : start = ⟨0⟩ := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres.trans hstart
  obtain ⟨_, _, rd4086⟩ := auctionSettleAuctionX_toInternalSettleAuction
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hwv hpaused hstatus hreach
  have rd4096 := evm_run rd4086 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨192⟩, dup2, add, dup3,
    raw mstore 0 auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4100₀⟩ := (evm_run rd4096 with [push1 ⟨207⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4100⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4100⟩
      (noun :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      auctionSettleAuctionSnapshotFreeMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [noun, auctionAuctionNounWord, auctionSlotWord, σ1] using rd4100₀⟩
  have rd4102 := evm_run rd4100 with [
    dup2,
    raw mstore 6 (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4105₀⟩ := (evm_run rd4102 with [push1 ⟨208⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4105⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4105⟩
      (amount :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotNounMem noun) (UInt256.ofNat 5) ByteArray.empty
      (cA, σ1) k C := by
    exact ⟨_, _, by simpa [amount, auctionAuctionAmountWord, auctionSlotWord, σ1] using rd4105₀⟩
  have rd4109 := evm_run rd4105 with [
    push1 ⟨32⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4113₀⟩ := (evm_run rd4109 with [push1 ⟨209⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4113⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4113⟩
      (start :: ⟨128⟩ :: ⟨64⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotAmountMem noun amount) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [start, auctionAuctionStartWord, auctionSlotWord, σ1] using rd4113₀⟩
  have rd4119 := evm_run rd4113 with [
    swap2, dup2, add, dup3, swap1,
    raw mstore 3 (auctionSettleAuctionSnapshotStartMem noun amount start)
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4122₀⟩ := (evm_run rd4119 with [push1 ⟨210⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4122⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4122⟩
      (finish :: ⟨128⟩ :: start :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotStartMem noun amount start) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [finish, auctionAuctionEndWord, auctionSlotWord, σ1] using rd4122₀⟩
  have rd4126 := evm_run rd4122 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotEndMem noun amount start finish)
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  obtain ⟨_, _, rd4130₀⟩ := (evm_run rd4126 with [push1 ⟨211⟩]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd4130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4130⟩
      (packed :: ⟨128⟩ :: start :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotEndMem noun amount start finish) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1] using rd4130₀⟩
  have rd4144 := evm_run rd4130 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    push1 ⟨128⟩, dup4, add]
  have rd4145 := evm_run rd4144 with [
    raw mstore 3 (auctionSettleAuctionSnapshotBidderMem noun amount start finish bidder)
      (UInt256.ofNat 9) (by decide) mem_cost
      (by
        dsimp [bidder, auctionPackedBidderWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by native_decide]
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd4161 := evm_run rd4145 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and,
    iszero, iszero, push1 ⟨160⟩, dup3, add,
    raw mstore 3 (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) (by decide) mem_cost
      (by
        dsimp [settled, auctionPackedSettledEVMReturnWord, auctionPackedSettledEVMWord,
          auctionPackedSettledBaseWord]
        rfl)
      (by decide) (by evm_ov)]
  have hcond : UInt256.sub (⟨0⟩ : UInt256) start = ⟨0⟩ := by
    rw [hstartEnter]
    decide
  have rd4169 := evm_run rd4161 with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiNT hcond]
  have rd4171 := evm_run rd4169 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4179 := rd4171.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4194 := evm_run rd4179 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4219 := rd4194.pushConst auctionAuctionHasntBegunRawStringWord
    (width := 20) (op := .PUSH20) (by decide) (by decide) (by evm_ov)
  have rd4219₀ := evm_run rd4219 with [push1 ⟨97⟩, shl]
  have hword :
      UInt256.shiftLeft auctionAuctionHasntBegunRawStringWord ⟨97⟩ =
        auctionAuctionHasntBegunStringWord := by
    native_decide
  have rd4219' := rd4219₀
  rw [hword] at rd4219'
  have rd4227₀ := evm_run rd4219' with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4227 := rd4227₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4227
  have rd994 := evm_run rd4227 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionHasntStartedMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_settleAuction_revert_alreadySettled {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed ≠ ⟨0⟩ := by
    intro hzero
    exact hsettled (by simpa [hpackedPres] using hzero)
  have hsettledEVM : auctionPackedSettledEVMWord packed ≠ ⟨0⟩ := by
    intro hzero
    have hzero' : auctionPackedSettledWord packed = ⟨0⟩ := by
      simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm] using hzero
    exact hsettledEnter hzero'
  obtain ⟨_, _, rd4162⟩ := auctionSettleAuctionX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hwv hpaused hstatus hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨1⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [isZero_eq_zero_of_ne hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled = ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4242 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiNT hsettledCond]
  have rd4244 := evm_run rd4242 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4252 := rd4244.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4267 := evm_run rd4252 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add, dup2, swap1,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionAlreadySettledMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4301 := rd4267.pushConst auctionAuctionAlreadySettledStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd4309₀ := evm_run rd4301 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionAlreadySettledMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4309 := rd4309₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4309
  have rd994 := evm_run rd4309 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionAlreadySettledMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_settleAuction_revert_timeNotReached {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hfinishPres : finish = auctionAuctionEndWord σ I := by
    have hpres :
        auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionEndWord σ I := by
      unfold auctionAuctionEndWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨210⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [finish, σ1] using hpres
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed = ⟨0⟩ := by
    simpa [hpackedPres] using hsettled
  have hsettledEVM : auctionPackedSettledEVMWord packed = ⟨0⟩ := by
    simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm]
      using hsettledEnter
  obtain ⟨_, _, rd4162⟩ := auctionSettleAuctionX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hwv hpaused hstatus hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨0⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled ≠ ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4313 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiT hsettledCond (by jump_dest)]
  have rd4321 := evm_run rd4313 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt, iszero]
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨1⟩ := by
    apply ult_one
    simpa [hfinishPres] using htime
  have htimeCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat I.header.timestamp) finish) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd4328 := evm_run rd4321 with [
    push2 ⟨4397⟩, jumpiNT htimeCond,
    push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov)]
  have rd4335 := rd4328.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd4351 := evm_run rd4335 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 3 (auctionAuctionHasntStartedMem0 noun amount start finish bidder settled)
      (UInt256.ofNat 11) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntStartedMem1 noun amount start finish bidder settled)
      (UInt256.ofNat 12) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨24⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntCompletedMem2 noun amount start finish bidder settled)
      (UInt256.ofNat 13) (by decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4385 := rd4351.pushConst auctionAuctionHasntCompletedStringWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd4393₀ := evm_run rd4385 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3 (auctionAuctionHasntCompletedMem3 noun amount start finish bidder settled)
      (UInt256.ofNat 14) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd4393 := rd4393₀
  rw [show (⟨100⟩ : UInt256) + ⟨320⟩ = ⟨420⟩ by decide] at rd4393
  have rd994 := evm_run rd4393 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 14) (by decide)
      mem_cost
      (auctionAuctionHasntCompletedMem3_mload64 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨420⟩ : UInt256) ⟨320⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionSettleAuctionX_toMarkSettled {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  have hstartPres : start = auctionAuctionStartWord σ I := by
    have hpres :
        auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionStartWord σ I := by
      unfold auctionAuctionStartWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [start, σ1] using hpres
  have hstartEnter : start ≠ ⟨0⟩ := by
    intro hzero
    exact hstart (hstartPres.symm.trans hzero)
  have hfinishPres : finish = auctionAuctionEndWord σ I := by
    have hpres :
        auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionEndWord σ I := by
      unfold auctionAuctionEndWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨210⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [finish, σ1] using hpres
  have hpackedPres : packed = auctionAuctionPackedWord σ I := by
    have hpres :
        auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I =
          auctionAuctionPackedWord σ I := by
      unfold auctionAuctionPackedWord auctionSettleAuctionEnterMap auctionSlotWord
      simpa using
        sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨101⟩ ⟨2⟩ (by decide)
    simpa [packed, σ1] using hpres
  have hsettledEnter : auctionPackedSettledWord packed = ⟨0⟩ := by
    simpa [hpackedPres] using hsettled
  have hsettledEVM : auctionPackedSettledEVMWord packed = ⟨0⟩ := by
    simpa [auctionPackedSettledEVMWord, auctionPackedSettledWord, u256_land_comm]
      using hsettledEnter
  obtain ⟨_, _, rd4162⟩ := auctionSettleAuctionX_toSnapshotCheck
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm hwv hpaused hstatus hreach
  obtain ⟨_, _, rd4162'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4162⟩
      [⟨128⟩, start, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled] using rd4162⟩
  have hstartCond : UInt256.sub (⟨0⟩ : UInt256) start ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by intro h; exact hstartEnter h.symm)
  have rd4231 := evm_run rd4162' with [
    swap1, push0, sub, push2 ⟨4231⟩, jumpiT hstartCond (by jump_dest)]
  have rd4237 := evm_run rd4231 with [
    jumpdest, dup1, push1 ⟨160⟩, add,
    raw mload 0 settled (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload288 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    iszero]
  have hsettledRet : settled = ⟨0⟩ := by
    dsimp [settled, auctionPackedSettledEVMReturnWord]
    rw [hsettledEVM]
    decide
  have hsettledCond : UInt256.isZero settled ≠ ⟨0⟩ := by
    rw [hsettledRet]
    decide
  have rd4313 := evm_run rd4237 with [push2 ⟨4313⟩, jumpiT hsettledCond (by jump_dest)]
  have rd4321 := evm_run rd4313 with [
    jumpdest, dup1, push1 ⟨96⟩, add,
    raw mload 0 finish (UInt256.ofNat 10) (by decide)
      mem_cost
      (auctionSettleAuctionSnapshotMem_mload224 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    timestamp, lt, iszero]
  have htimeLe : finish.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat := by
    apply Nat.le_of_not_gt
    simpa [hfinishPres] using htime
  have hlt : UInt256.lt (UInt256.ofNat I.header.timestamp) finish = ⟨0⟩ :=
    ult_zero htimeLe
  have htimeCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat I.header.timestamp) finish) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd4397 := evm_run rd4321 with [push2 ⟨4397⟩, jumpiT htimeCond (by jump_dest)]
  have rd4401₀ := evm_run rd4397 with [jumpdest, push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd4402₀⟩ := rd4401₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd4402⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4402⟩
      (packed :: ⟨211⟩ :: ⟨128⟩ :: ⟨2471⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      (auctionSettleAuctionSnapshotMem noun amount start finish bidder settled)
      (UInt256.ofNat 10) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, by simpa [packed, auctionAuctionPackedWord, auctionSlotWord, σ1]
      using rd4402₀⟩
  have rd4416₀ := evm_run rd4402 with [
    push1 ⟨255⟩, push1 ⟨160⟩, shl, not, and,
    push1 ⟨1⟩, push1 ⟨160⟩, shl, lor, swap1]
  have hpost :
      UInt256.lor (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
          (UInt256.land (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩))
            packed) =
        auctionSetBoolOffset20TrueWord packed :=
    auctionSetBoolOffset20TrueWord_eq_evm packed
  have rd4416 := rd4416₀
  rw [hpost] at rd4416
  obtain ⟨_, _, rd4417₀⟩ := rd4416.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [auctionSettleAuctionMarkSettledMap, packed, auctionAuctionPackedWord, auctionSlotWord,
      σ1, noun, amount, start, finish, bidder, settled] using rd4417₀⟩

theorem auctionSettleAuctionX_toBurnPath {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ I ≠ ⟨2⟩)
    (hstart : auctionAuctionStartWord σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionAuctionPackedWord σ I) = ⟨0⟩)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat < (auctionAuctionEndWord σ I).toNat)
    (hbidderZero :
      auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I) =
        ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨765⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4435⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionSnapshotMem
        (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ I) I)
        (auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I))
        (auctionPackedSettledEVMReturnWord
          (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ I) I)))
      (UInt256.ofNat 10) ByteArray.empty
      (cA, auctionSettleAuctionMarkSettledMap (auctionSettleAuctionEnterMap σ I) I) k C := by
  let σ1 := auctionSettleAuctionEnterMap σ I
  let noun := auctionAuctionNounWord σ1 I
  let amount := auctionAuctionAmountWord σ1 I
  let start := auctionAuctionStartWord σ1 I
  let finish := auctionAuctionEndWord σ1 I
  let packed := auctionAuctionPackedWord σ1 I
  let bidder := auctionPackedBidderWord packed
  let settled := auctionPackedSettledEVMReturnWord packed
  let mem := auctionSettleAuctionSnapshotMem noun amount start finish bidder settled
  let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
  obtain ⟨_, _, rd4417⟩ := auctionSettleAuctionX_toMarkSettled
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hperm hwv hpaused hstatus hstart hsettled htime hreach
  obtain ⟨_, _, rd4417'⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4417⟩
      [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem (UInt256.ofNat 10)
      ByteArray.empty (cA, σ2) k C := by
    exact ⟨_, _, by
      simpa [σ1, noun, amount, start, finish, packed, bidder, settled, mem, σ2] using rd4417⟩
  have rd4434 := evm_run rd4417' with [
    push1 ⟨128⟩, dup2, add,
    raw mload 0 bidder (UInt256.ofNat 10) (by decide)
      mem_cost
      (by simpa [mem] using
        auctionSettleAuctionSnapshotMem_mload256 noun amount start finish bidder settled)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨4536⟩]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          bidder =
        ⟨0⟩ := by
    rw [hmask]
    simp [bidder, packed, σ1, hbidderZero]
    decide
  exact ⟨_, _, by simpa using evm_run rd4434 with [jumpiNT hcond]⟩

theorem auctionSettleAuctionTransitionReverts_statusEntered (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ = ⟨2⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_settleAuction_status_ne_entered_false evm hstatus))

theorem auctionSettleAuctionTransitionReverts_notStarted (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_notStarted (auctionSettleAuctionEnterState evm) (by
      have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          evm.executionEnv.codeOwner ⟨209⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
        simpa [auctionSettleAuctionEnterState] using
          storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
            (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
      have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
        simpa [auctionSettleAuctionEnterState] using
          storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
      simpa [henv, hstart] using hload)))

theorem auctionSettleAuctionTransitionReverts_alreadySettled (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_alreadySettled (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        intro hzero
        exact hstart (by simpa [henv, hload] using hzero))
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        intro hzero
        exact hsettled (by simpa [henv, hload] using hzero))))

theorem auctionSettleAuctionTransitionReverts_timeNotReached (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_timeNotReached (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        intro hzero
        exact hstart (by simpa [henv, hload] using hzero))
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)))

theorem auctionSettleAuctionTransitionReverts_burnNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_burnNoCode (auctionSettleAuctionEnterState evm)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        intro hzero
        exact hstart (by simpa [henv, hload] using hzero))
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hbidder)
      hnounsNoCode))

end Auction
