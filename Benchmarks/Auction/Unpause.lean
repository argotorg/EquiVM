import Benchmarks.Auction.AuctionGetter
import Benchmarks.Auction.Common
import Benchmarks.Auction.CreateAuction
import Benchmarks.Auction.Pause
import Benchmarks.Auction.UnpauseCreateAuction
import Benchmarks.Auction.UnpauseErrorStringTrace
import Benchmarks.Auction.UnpauseMintFailureTraceSub
import Benchmarks.Auction.UnpauseMintTrace
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionUnpausedTopic : UInt256 :=
  ⟨0x5db9ee0a495bf2e6ff9c91a7834c1ba4fdd244a5e8aa4e537bd38aeae4b073aa⟩

def auctionPausableNotPausedRawStringWord : UInt256 :=
  ⟨0x14185d5cd8589b194e881b9bdd081c185d5cd959⟩

def auctionPausableNotPausedStringWord : UInt256 :=
  ⟨0x5061757361626c653a206e6f7420706175736564000000000000000000000000⟩

theorem auctionDispatch_unpause {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 3)) :
    dispatchMsg auctionContract I.calldata = some unpauseTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition])
    (post := [setTimeBufferTransition, setReservePriceTransition, setMinBidIncTransition,
      transferOwnershipTransition, renounceOwnershipTransition, ownerGetter, pausedGetter,
      nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter, minBidIncGetter,
      durationGetter, auctionGetter])
    (ti := unpauseTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 3 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes, hcd,
        auctionSelBytes]
      native_decide
  · rw [selectorOf, unpauseSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_unpause {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (unpauseTransition.params.map Param.name)
        (transitionSignature unpauseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionUnpauseBodyReverts_callvalue (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionUnpauseBodyReverts_owner (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_pause_owner_eq_false evm howner))

theorem auctionUnpauseBodyReverts_paused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ unpauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_pause_paused_false evm hzero))

theorem auctionReachUnpauseBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 3)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨415⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x3f, 0x4b, 0xa8, 0x3a]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x3f4ba83a⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x3f 0x4b 0xa8 0x3a ⟨0x3f4ba83a⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h157 := auctionSelectorSplitTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitTargetPc
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by native_decide) (by simp)
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h227 := auctionSelectorSplitTakenTo h158 auctionLowerSplitWellFormed hlower
      auctionLowerSplitTargetPc
    (by jump_dest) (by simp)
  have h228 := h227.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerLowFirstArmPc 3))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨415⟩ 3 h228
    (fun j hj => auctionLowerLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_unpause_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨415⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd415⟩ := hreach
  exact evm_run rd415 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨426⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionUnpauseX_toBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1076⟩
      [⟨413⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd415⟩ := hreach
  exact ⟨_, _, evm_run rd415 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨426⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨1076⟩, jump (by jump_dest)]⟩

theorem auctionUnpauseX_toInternalUnpause {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2853⟩
      [⟨1126⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1076⟩ := auctionUnpauseX_toBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I) hreach hwv
  have rd1080₀ := evm_run rd1076 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd1080₁⟩ := rd1080₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1080⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1080⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1080₁⟩
  have rd1091₀ := evm_run rd1080 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) = auctionSourceWord I := by
    rw [u256_land_comm, howner]
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩ := by
    change UInt256.eq (auctionSourceWord I)
      (UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩
    rw [hmask, u256_eq_refl]
  have rd1091 := rd1091₀
  rw [heq] at rd1091
  have rd1118 := evm_run rd1091 with [
    push2 ⟨1118⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd1118 with [push2 ⟨1126⟩, push2 ⟨2853⟩, jump (by jump_dest)]⟩

theorem auctionX_unpause_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1076⟩ := auctionUnpauseX_toBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I) hreach hwv
  have rd1080₀ := evm_run rd1076 with [jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd1080₁⟩ := rd1080₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1080⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1080⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1080₁⟩
  have rd1091₀ := evm_run rd1080 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) ≠ auctionSourceWord I := by
    intro hmask
    exact howner (by
      rw [u256_land_comm] at hmask
      exact hmask)
  have hneq :
      UInt256.ofNat I.source.val ≠
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I) := by
    change auctionSourceWord I ≠ UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)
    exact fun h => hmask h.symm
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨0⟩ := by
    exact u256_eq_of_ne hneq
  have rd1091 := rd1091₀
  rw [heq] at rd1091
  have rd1095 := evm_run rd1091 with [
    push2 ⟨1118⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd1102 := rd1095.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd5522 := evm_run rd1102 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcReturnMem ⟨0x08c379a000000000000000000000000000000000000000000000000000000000⟩)
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨994⟩, swap1, push2 ⟨5522⟩, jump (by jump_dest)]
  have rd5532 := evm_run rd5522 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, dup2, add,
    raw mstore 3 (solcErrorStringMem2 ⟨32⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5565 := rd5532.pushConst auctionPauseOnlyOwnerStringWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd5574₀ := evm_run rd5565 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨32⟩ auctionPauseOnlyOwnerStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5574 := rd5574₀
  rw [show (⟨96⟩ : UInt256) + (⟨4⟩ + ⟨128⟩) = ⟨228⟩ by decide] at rd5574
  have rd994 := evm_run rd5574 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨32⟩ auctionPauseOnlyOwnerStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem auctionUnpauseRoutine_success {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : auctionPausedWord σ I ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length ≤ 1000)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2853⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionUnpausePostMap σ I) k C := by
  have rd2857₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2857₁⟩ := rd2857₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2857⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2857⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2857₁⟩
  have rd2860 := evm_run rd2857 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) ≠ ⟨0⟩ := by
    simpa [hmask] using hnz
  have rd2926 := evm_run rd2860 with [push2 ⟨2926⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd2931₀ := evm_run rd2926 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd2931₁⟩ := rd2931₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2931⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2931⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2931₁⟩
  have rd2936₀ := evm_run rd2931 with [push1 ⟨255⟩, not, and, swap1]
  have hclear : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I) := by
    rw [u256_land_comm]
    rfl
  have rd2936 := rd2936₀
  rw [hclear] at rd2936
  obtain ⟨_, _, rd2937₀⟩ := rd2936.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2937⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨2937⟩ (ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionUnpausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionUnpausePostMap] using rd2937₀⟩
  have rd2970 := rd2937.pushConst auctionUnpausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2988₀ := evm_run rd2970 with [
    caller, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  have rd2988_mem := evm_run rd2988 with [
    raw mstore 6 (auctionEventMem I) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2998₀ := evm_run rd2988_mem with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (auctionEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  have rd2999 := RD.log1 0 (UInt256.ofNat 5) rd2998 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2999 with [jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_unpause_revert_paused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2853⟩ := auctionUnpauseX_toInternalUnpause (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  have rd2857₀ := evm_run rd2853 with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd2857₁⟩ := rd2857₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2857⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2857⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨1126⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2857₁⟩
  have rd2860 := evm_run rd2857 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = ⟨0⟩ := by
    simpa [hmask] using hzero
  have rd2864 := evm_run rd2860 with [
    push2 ⟨2926⟩, jumpiNT hcond,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2871 := rd2864.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd2890 := evm_run rd2871 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨20⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2911 := rd2890.pushConst auctionPausableNotPausedRawStringWord
    (width := 20) (op := .PUSH20) (by decide) (by native_decide) (by evm_ov)
  have rd2914₀ := evm_run rd2911 with [push1 ⟨98⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausableNotPausedRawStringWord ⟨98⟩ =
        auctionPausableNotPausedStringWord := by
    native_decide
  have rd2914 := rd2914₀
  rw [hword] at rd2914
  have rd2921₀ := evm_run rd2914 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨20⟩ auctionPausableNotPausedStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd2921 := rd2921₀
  rw [show (⟨100⟩ : UInt256) + ⟨128⟩ = ⟨228⟩ by decide] at rd2921
  have rd994 := evm_run rd2921 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨20⟩ auctionPausableNotPausedStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem auctionX_unpause_success_noCreate {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstart : auctionSlotWord ⟨209⟩ σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionUnpausePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd2853⟩ := auctionUnpauseX_toInternalUnpause (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  obtain ⟨_, _, rd1126⟩ := auctionUnpauseRoutine_success (σ := σ) (g := g)
    (ret := ⟨1126⟩) (R := [⟨413⟩, auctionSelWord I]) hperm hpaused
    (by jump_dest) (by simp) rd2853
  let σ1 := auctionUnpausePostMap σ I
  have hstartPost : auctionSlotWord ⟨209⟩ σ1 I = auctionSlotWord ⟨209⟩ σ I := by
    simpa [σ1, auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide)
  have hsettledPost : auctionSlotWord ⟨211⟩ σ1 I = auctionSlotWord ⟨211⟩ σ I := by
    simpa [σ1, auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide)
  have rd1130₀ := evm_run rd1126 with [jumpdest, push1 ⟨209⟩]
  obtain ⟨_, _, rd1130₁⟩ := rd1130₀.sload (by native_decide) (by evm_ov)
  have hstartPost' :
      Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨209⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ1 I.codeOwner) =
        auctionSlotWord ⟨209⟩ σ I := by
    simpa [auctionSlotWord] using hstartPost
  have rd1130₂ := rd1130₁
  rw [show ({ val := 1126 } + { val := 1 } + UInt256.ofNat 2 + { val := 1 } : UInt256) =
      ⟨1130⟩ by decide] at rd1130₂
  rw [hstartPost'] at rd1130₂
  obtain ⟨_, _, rd1130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1130⟩
      [auctionSlotWord ⟨209⟩ σ I, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, rd1130₂⟩
  have rd1132₀ := evm_run rd1130 with [iszero, dup1]
  have hstartIz : UInt256.isZero (auctionSlotWord ⟨209⟩ σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hstart
  have rd1132 := rd1132₀
  rw [hstartIz] at rd1132
  have rd1137 := evm_run rd1132 with [
    push2 ⟨1150⟩, jumpiNT (by decide), pop, push1 ⟨211⟩]
  obtain ⟨_, _, rd1140₁⟩ := rd1137.sload (by native_decide) (by evm_ov)
  have hsettledPost' :
      Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨211⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ1 I.codeOwner) =
        auctionSlotWord ⟨211⟩ σ I := by
    simpa [auctionSlotWord] using hsettledPost
  have rd1140₂ := rd1140₁
  rw [show ({ val := 1130 } + { val := 1 } + { val := 1 } + UInt256.ofNat 3 +
        { val := 1 } + { val := 1 } + UInt256.ofNat 2 + { val := 1 } : UInt256) =
      ⟨1140⟩ by decide] at rd1140₂
  rw [hsettledPost'] at rd1140₂
  obtain ⟨_, _, rd1140⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1140⟩
      [auctionSlotWord ⟨211⟩ σ I, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ1) k C := by
    exact ⟨_, _, rd1140₂⟩
  have rd1150₀ := evm_run rd1140 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and]
  have hpow : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ =
      UInt256.ofNat (256 ^ 20) := by
    native_decide
  have hsettledEvm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨211⟩ σ I)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) = ⟨0⟩ := by
    rw [hpow]
    change UInt256.land ⟨255⟩
      (auctionPackedSettledBaseWord (auctionSlotWord ⟨211⟩ σ I)) = ⟨0⟩
    rw [u256_land_comm]
    exact hsettled
  have rd1150 := rd1150₀
  rw [hsettledEvm] at rd1150
  have rd1163 := evm_run rd1150 with [
    jumpdest, iszero, push2 ⟨1163⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd413 := evm_run rd1163 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionUnpauseX_toCreateAuction_startZero {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hstart : auctionSlotWord ⟨209⟩ σ I = ⟨0⟩)
    (hov : R.length ≤ 1000)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨1126⟩
      (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (⟨1163⟩ :: ret :: R) mem aw rdata (cA, σ) k C := by
  have rd1130₀ := evm_run h with [jumpdest, push1 ⟨209⟩]
  obtain ⟨_, _, rd1130₁⟩ := rd1130₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨1130⟩
      (auctionSlotWord ⟨209⟩ σ I :: ret :: R) mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1130₁⟩
  have rd1132₀ := evm_run rd1130 with [iszero, dup1]
  have hstartIz : UInt256.isZero (auctionSlotWord ⟨209⟩ σ I) = ⟨1⟩ := by
    rw [hstart]
    rfl
  have rd1132 := rd1132₀
  rw [hstartIz] at rd1132
  have rd1150 := evm_run rd1132 with [
    push2 ⟨1150⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  have rd3000 := evm_run rd1150 with [
    iszero, push2 ⟨1163⟩, jumpiNT (by decide),
    push2 ⟨1163⟩, push2 ⟨3000⟩, jump (by jump_dest)]
  exact ⟨_, _, rd3000⟩

theorem auctionUnpauseX_toCreateAuction_settled {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hstart : auctionSlotWord ⟨209⟩ σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ I) ≠ ⟨0⟩)
    (hov : R.length ≤ 1000)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨1126⟩
      (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (⟨1163⟩ :: ret :: R) mem aw rdata (cA, σ) k C := by
  have rd1130₀ := evm_run h with [jumpdest, push1 ⟨209⟩]
  obtain ⟨_, _, rd1130₁⟩ := rd1130₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1130⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨1130⟩
      (auctionSlotWord ⟨209⟩ σ I :: ret :: R) mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1130₁⟩
  have rd1132₀ := evm_run rd1130 with [iszero, dup1]
  have hstartIz : UInt256.isZero (auctionSlotWord ⟨209⟩ σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hstart
  have rd1132 := rd1132₀
  rw [hstartIz] at rd1132
  have rd1137 := evm_run rd1132 with [
    push2 ⟨1150⟩, jumpiNT (by decide), pop, push1 ⟨211⟩]
  obtain ⟨_, _, rd1140₁⟩ := rd1137.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1140⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨1140⟩
      (auctionSlotWord ⟨211⟩ σ I :: ret :: R) mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd1140₁⟩
  have rd1150₀ := evm_run rd1140 with [
    push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and]
  have hpow : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ =
      UInt256.ofNat (256 ^ 20) := by
    native_decide
  have hsettledEvm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨211⟩ σ I)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) ≠ ⟨0⟩ := by
    intro hzero
    apply hsettled
    rw [hpow] at hzero
    change UInt256.land ⟨255⟩
      (auctionPackedSettledBaseWord (auctionSlotWord ⟨211⟩ σ I)) = ⟨0⟩ at hzero
    rw [u256_land_comm] at hzero
    exact hzero
  have rd1151₀ := evm_run rd1150₀ with [jumpdest, iszero]
  have hsettledIz : UInt256.isZero
      (UInt256.land ⟨255⟩
        (UInt256.div (auctionSlotWord ⟨211⟩ σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hsettledEvm
  have rd1151 := rd1151₀
  rw [hsettledIz] at rd1151
  have rd3000 := evm_run rd1151 with [
    push2 ⟨1163⟩, jumpiNT (by decide),
    push2 ⟨1163⟩, push2 ⟨3000⟩, jump (by jump_dest)]
  exact ⟨_, _, rd3000⟩

theorem auctionX_unpause_toCreateAuction_startZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstart : auctionSlotWord ⟨209⟩ σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3000⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionUnpausePostMap σ I) k C := by
  obtain ⟨_, _, rd2853⟩ := auctionUnpauseX_toInternalUnpause (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  obtain ⟨_, _, rd1126⟩ := auctionUnpauseRoutine_success (σ := σ) (g := g)
    (ret := ⟨1126⟩) (R := [⟨413⟩, auctionSelWord I]) hperm hpaused
    (by jump_dest) (by simp) rd2853
  let σ1 := auctionUnpausePostMap σ I
  have hstartPost : auctionSlotWord ⟨209⟩ σ1 I = auctionSlotWord ⟨209⟩ σ I := by
    simpa [σ1, auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide)
  have hstart1 : auctionSlotWord ⟨209⟩ σ1 I = ⟨0⟩ := by
    rw [hstartPost]
    exact hstart
  obtain ⟨_, _, rd3000⟩ := auctionUnpauseX_toCreateAuction_startZero
    (σInit := σ) (σ := σ1) (σ₀ := σ₀) (g := g) (ret := ⟨413⟩)
    (R := [auctionSelWord I]) (mem := auctionEventMem I)
    (aw := UInt256.ofNat 5) (rdata := ByteArray.empty) hstart1 (by simp) rd1126
  exact ⟨_, _, by simpa [σ1] using rd3000⟩

theorem auctionX_unpause_toCreateAuction_settled {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (howner : UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hpaused : auctionPausedWord σ I ≠ ⟨0⟩)
    (hstart : auctionSlotWord ⟨209⟩ σ I ≠ ⟨0⟩)
    (hsettled : auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨415⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3000⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, auctionUnpausePostMap σ I) k C := by
  obtain ⟨_, _, rd2853⟩ := auctionUnpauseX_toInternalUnpause (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  obtain ⟨_, _, rd1126⟩ := auctionUnpauseRoutine_success (σ := σ) (g := g)
    (ret := ⟨1126⟩) (R := [⟨413⟩, auctionSelWord I]) hperm hpaused
    (by jump_dest) (by simp) rd2853
  let σ1 := auctionUnpausePostMap σ I
  have hstartPost : auctionSlotWord ⟨209⟩ σ1 I = auctionSlotWord ⟨209⟩ σ I := by
    simpa [σ1, auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨209⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide)
  have hsettledPost : auctionSlotWord ⟨211⟩ σ1 I = auctionSlotWord ⟨211⟩ σ I := by
    simpa [σ1, auctionUnpausePostMap, auctionSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨211⟩ ⟨51⟩
        (auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I)) (by decide)
  have hstart1 : auctionSlotWord ⟨209⟩ σ1 I ≠ ⟨0⟩ := by
    intro hz
    exact hstart (by simpa [hstartPost] using hz)
  have hsettled1 : auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ1 I) ≠ ⟨0⟩ := by
    intro hz
    exact hsettled (by simpa [hsettledPost] using hz)
  obtain ⟨_, _, rd3000⟩ := auctionUnpauseX_toCreateAuction_settled
    (σInit := σ) (σ := σ1) (σ₀ := σ₀) (g := g) (ret := ⟨413⟩)
    (R := [auctionSelWord I]) (mem := auctionEventMem I)
    (aw := UInt256.ofNat 5) (rdata := ByteArray.empty) hstart1 hsettled1 (by simp) rd1126
  exact ⟨_, _, by simpa [σ1] using rd3000⟩

set_option maxHeartbeats 1000000 in

theorem auctionUnpauseBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 3))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 3) rfl _hsel
  have hdispatch := auctionDispatch_unpause _hsel
  have hdecode := auctionDecode_unpause (I := I) hsz4
  have hreach := auctionReachUnpauseBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerWord :
        auctionSlotWord ⟨151⟩ σ_evm I = auctionSlotWord ⟨151⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨151⟩ ⟨0⟩
    by_cases howner :
        UInt256.land (auctionSlotWord ⟨151⟩ σ_evm I) solcAddrMask = auctionSourceWord I
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask =
            auctionSourceWord evmS.executionEnv := by
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [hownerWord] using howner
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
          auctionSourceWord] using hmap
      have hpausedWord :
          auctionSlotWord ⟨51⟩ σ_evm I = auctionSlotWord ⟨51⟩ σ_solm I :=
        accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨51⟩ ⟨0⟩
      by_cases hpausedZero : auctionPausedWord σ_evm I = ⟨0⟩
      · have hzeroSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ =
              ⟨0⟩ := by
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [auctionPausedWord, hpausedWord] using hpausedZero
          simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount] using hmap
        have hbody := auctionUnpauseBodyReverts_paused evmS
          (by simp only [evmS, initState]; exact hwv) hownerSolm hzeroSolm
        exact (auctionX_unpause_revert_paused (g := Sat256.ofUInt256 g)
            hwv howner hpausedZero hreach)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
      · have hpausedSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ ≠
              ⟨0⟩ := by
          intro h
          apply hpausedZero
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount] using h
          simpa [auctionPausedWord, hpausedWord] using hmap
        by_cases hnoCreate :
            auctionSlotWord ⟨209⟩ σ_evm I ≠ ⟨0⟩ ∧
              auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_evm I) = ⟨0⟩
        · obtain ⟨hstart, hsettled⟩ := hnoCreate
          have hstartWord :
              auctionSlotWord ⟨209⟩ σ_evm I = auctionSlotWord ⟨209⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨209⟩ ⟨0⟩
          have hsettledWord :
              auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I :=
            accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨211⟩ ⟨0⟩
          have hstartSolm :
              Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩ := by
            have hmap : auctionSlotWord ⟨209⟩ σ_solm I ≠ ⟨0⟩ := by
              intro hs
              exact hstart (by simp [hstartWord, hs])
            simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount] using hmap
          have hsettledSolm :
              auctionPackedSettledWord
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
                ⟨0⟩ := by
            have hmap :
                auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_solm I) = ⟨0⟩ := by
              simpa [hsettledWord] using hsettled
            simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount] using hmap
          have hbody := auctionUnpauseBodyReturns_noCreate evmS
            (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hstartSolm
            hsettledSolm
          have hpostAccountsEvm :
              accountMapEquiv (auctionUnpausePostMap σ_evm I)
                (auctionUnpausePostState evmE).accountMap := by
            simpa [evmE] using
              (auctionUnpausePostMap_accountMap (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g))
          have hpostState :
              EVMStateEquiv (auctionUnpausePostState evmE) (auctionUnpausePostState evmS) := by
            simpa [evmE, evmS] using
              (auctionUnpausePostState_equiv (cA := cA) (gh := gh) (bl := bl)
                (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) _hAccounts)
          exact (auctionX_unpause_success_noCreate (g := Sat256.ofUInt256 g)
              _hperm hwv howner hpausedZero hstart hsettled hreach)
            |>.reEquivExecutionGenEVMStateEquiv _hcode hdispatch hdecode hbody
              (by simp [auctionUnpausePostState, evmE, initState, storageStore_createdAccounts])
              hpostAccountsEvm
              hpostState
              (returnEquiv.fallthrough rfl rfl (by native_decide))
        · -- Remaining case: `unpause()` must enter `_createAuction`.
          have hcond :
              evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
                (auctionUnpausePostState evmS)
                (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
                  (.storage (aField "settled"))) = .ok (.bool true) := by
            simpa [evmS] using
              evalExpr_unpausePost_createCond_true_of_not_noCreate
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) _hAccounts hnoCreate
          obtain ⟨_, _, rd3000⟩ :
              ∃ k C, RD auctionBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3000⟩
                [⟨1163⟩, ⟨413⟩, auctionSelWord I]
                (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty
                (cA, auctionUnpausePostMap σ_evm I) k C := by
            by_cases hstartZero : auctionSlotWord ⟨209⟩ σ_evm I = ⟨0⟩
            · exact auctionX_unpause_toCreateAuction_startZero
                (g := Sat256.ofUInt256 g) _hperm hwv howner hpausedZero
                hstartZero hreach
            · have hsettledNe :
                  auctionPackedSettledWord (auctionSlotWord ⟨211⟩ σ_evm I) ≠ ⟨0⟩ := by
                intro hsettled
                exact hnoCreate ⟨hstartZero, hsettled⟩
              exact auctionX_unpause_toCreateAuction_settled
                (g := Sat256.ofUInt256 g) _hperm hwv howner hpausedZero
                hstartZero hsettledNe hreach
          by_cases hdepthMax : I.depth = 1024
          · let mintTargetSolm : EVM.Address := EVM.address (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad (auctionUnpausePostState evmS)
                  (auctionUnpausePostState evmS).executionEnv.codeOwner ⟨201⟩)
                solcAddrMask).toNat))
            let evmCallSolm : EVM.State :=
              { auctionUnpausePostState evmS with
                substate := ((auctionUnpausePostState evmS).addAccessedAccount
                  mintTargetSolm).substate }
            have hdepthPost : (auctionUnpausePostState evmS).executionEnv.depth = 1024 := by
              simpa [auctionUnpausePostState, evmS, initState, storageStore_executionEnv]
                using hdepthMax
            have hcallSolm :
                typedCallViaEVM auctionConfig (auctionUnpausePostState evmS)
                  mintTargetSolm "mint" 0 [] (false, evmCallSolm, ByteArray.empty) true := by
              exact callNotMade_depthLimit
                (cfg := auctionConfig) (evm := auctionUnpausePostState evmS)
                (tgt := mintTargetSolm) (name := "mint") (args := [])
                (calldata := (auctionUnpauseMintSelMem I).readWithPadding 128 4)
                (callPerm := true) (auctionUnpauseMintEncode_eq I) hdepthPost
            have hbody := auctionUnpauseBodyReverts_create_callFailure_empty evmS evmCallSolm
              (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hcond
              (by simpa [mintTargetSolm, evmCallSolm] using hcallSolm)
            exact (auctionCreateAuction_callDepthLimitRevert
                (g := Sat256.ofUInt256 g) hdepthMax rd3000)
              |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
          · have hdepthLt : I.depth.val < 1024 := by
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hneVal : I.depth.val ≠ 1024 := by
                intro hv
                exact hdepthMax (Fin.ext hv)
              omega
            obtain ⟨cA', σ', z, o, A', _, _, rd3067, hcallE, hosz⟩ :=
              auctionCreateAuction_postMintCall _hperm hdepthLt rd3000
            by_cases hsuccess :
                ∃ nounId : UInt256,
                  z = true ∧
                    ABI.decodeReturnValue? uint256 o =
                      some (.int (Int.ofNat nounId.toNat)) ∧
                    (UInt256.ofNat I.header.timestamp).toNat +
                        (auctionSlotWord ⟨206⟩ σ' I).toNat < UInt256.size
            · obtain ⟨nounId, hz, hdec, haddE⟩ := hsuccess
              subst z
              let evmCallE : EVM.State :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }
              obtain ⟨σ'_solm, A'_solm, hcallS, hcallState⟩ :=
                auctionUnpauseMintCall_transport
                  (cA := cA) (gh := gh) (bl := bl)
                  (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (cA' := cA') (σ' := σ') (z := true) (o := o) (A' := A')
                  _hAccounts hcallE
              let evmCallS : EVM.State :=
                { auctionUnpausePostState evmS with
                  accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
              have haddS :
                  (auctionCreateAuctionStartWord evmCallS).toNat +
                      (auctionCreateAuctionDurationWord evmCallS).toNat < UInt256.size := by
                have hstart :
                    auctionCreateAuctionStartWord evmCallE =
                      auctionCreateAuctionStartWord evmCallS := by
                  simp [auctionCreateAuctionStartWord, hcallState.executionEnv, evmCallE,
                    evmCallS, auctionUnpausePostState, storageStore_executionEnv, evmS,
                    initState]
                have hduration :
                    auctionCreateAuctionDurationWord evmCallE =
                      auctionCreateAuctionDurationWord evmCallS := by
                  simpa [auctionCreateAuctionDurationWord] using
                    hcallState.storageLoad_codeOwner ⟨206⟩
                have haddE' :
                    (auctionCreateAuctionStartWord evmCallE).toNat +
                        (auctionCreateAuctionDurationWord evmCallE).toNat < UInt256.size := by
                  simpa [evmCallE, auctionCreateAuctionStartWord,
                    auctionCreateAuctionDurationWord, initState, auctionSlotWord,
                    Solm.EVM.storageLoad, State.lookupAccount] using haddE
                simpa [hstart, hduration] using haddE'
              have hbody := auctionUnpauseBodyReturns_create_success evmS evmCallS
                (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hcond
                (by simpa [evmS, evmCallS] using hcallS) hdec haddS
              have rdret := auctionCreateAuction_mintCallSuccessTail
                (σTarget := auctionUnpausePostMap σ_evm I) (σ := σ')
                (g := Sat256.ofUInt256 g) _hperm hosz hdec haddE
                (by simpa using rd3067)
              have hpostAccounts :
                  accountMapEquiv
                    (auctionCreateAuctionSuccessPostMap σ' I nounId
                      (UInt256.ofNat I.header.timestamp)
                      (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ' I))
                    (auctionCreateAuctionSuccessPostState evmCallE nounId).accountMap := by
                apply accountMapEquiv.of_eq
                simp [auctionCreateAuctionSuccessPostMap, auctionCreateAuctionSuccessPostState,
                  auctionCreateAuctionStartWord, auctionCreateAuctionDurationWord,
                  auctionCreateAuctionEndWord, evmCallE, initState, storageStore_accountMap,
                  storageStore_executionEnv, auctionSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage]
              have hpostState :
                  EVMStateEquiv (auctionCreateAuctionSuccessPostState evmCallE nounId)
                    (auctionCreateAuctionSourceSuccessPostState evmCallS nounId) := by
                have h1 := auctionCreateAuctionSuccessPostState_equiv
                  (evm₁ := evmCallE) (evm₂ := evmCallS)
                  (nounId₁ := nounId) (nounId₂ := nounId) hcallState rfl
                have h2 := auctionCreateAuctionSuccessPostState_sourceStateEquiv evmCallS nounId
                exact ⟨h1.executionEnv.trans h2.executionEnv,
                  h1.createdAccounts.trans h2.createdAccounts,
                  accountMapEquiv.trans h1.accountMap h2.accountMap⟩
              exact rdret.reEquivExecutionGenEVMStateEquiv _hcode hdispatch hdecode hbody
                (by simp [evmCallE, auctionCreateAuctionSuccessPostState,
                  storageStore_createdAccounts])
                hpostAccounts
                hpostState
                (returnEquiv.fallthrough rfl rfl (by native_decide))
            · by_cases hfailEmpty : z = false ∧ o = ByteArray.empty
              · obtain ⟨hz, ho⟩ := hfailEmpty
                subst z
                subst o
                obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                  auctionUnpauseMintCall_transport
                    (cA := cA) (gh := gh) (bl := bl)
                    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    (cA' := cA') (σ' := σ') (z := false) (o := ByteArray.empty)
                    (A' := A') _hAccounts hcallE
                let evmCallS : EVM.State :=
                  { auctionUnpausePostState evmS with
                    accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                have hbody := auctionUnpauseBodyReverts_create_callFailure_empty evmS evmCallS
                  (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hcond
                  (by simpa [evmS, evmCallS] using hcallS)
                exact (auctionCreateAuction_mintCallFailureEmptyRevert
                    (by simpa using rd3067) (by simp))
                  |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
              · by_cases hdecodeFail :
                    z = true ∧ ABI.decodeReturnValue? uint256 o = none
                · obtain ⟨hz, hdecNone⟩ := hdecodeFail
                  subst z
                  obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                    auctionUnpauseMintCall_transport
                      (cA := cA) (gh := gh) (bl := bl)
                      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (cA' := cA') (σ' := σ') (z := true) (o := o)
                      (A' := A') _hAccounts hcallE
                  let evmCallS : EVM.State :=
                    { auctionUnpausePostState evmS with
                      accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                  have hbody := auctionUnpauseBodyReverts_create_decodeFailure evmS evmCallS
                    (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hcond
                    (by simpa [evmS, evmCallS] using hcallS) hdecNone
                  exact (auctionCreateAuction_mintCallSuccessDecodeRevert
                      (σTarget := auctionUnpausePostMap σ_evm I) (σ := σ')
                      hosz hdecNone (by simpa using rd3067))
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                · by_cases hoverCase :
                      ∃ nounId : UInt256,
                        z = true ∧
                          ABI.decodeReturnValue? uint256 o =
                            some (.int (Int.ofNat nounId.toNat)) ∧
                          UInt256.size ≤
                            (UInt256.ofNat I.header.timestamp).toNat +
                              (auctionSlotWord ⟨206⟩ σ' I).toNat
                  · obtain ⟨nounId, hz, hdec, hoverE⟩ := hoverCase
                    subst z
                    let evmCallE : EVM.State :=
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ', substate := A', createdAccounts := cA' }
                    obtain ⟨σ'_solm, A'_solm, hcallS, hcallState⟩ :=
                      auctionUnpauseMintCall_transport
                        (cA := cA) (gh := gh) (bl := bl)
                        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        (cA' := cA') (σ' := σ') (z := true) (o := o)
                        (A' := A') _hAccounts hcallE
                    let evmCallS : EVM.State :=
                      { auctionUnpausePostState evmS with
                        accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                    have hoverS :
                        UInt256.size ≤
                          (auctionCreateAuctionStartWord evmCallS).toNat +
                            (auctionCreateAuctionDurationWord evmCallS).toNat := by
                      have hstart :
                          auctionCreateAuctionStartWord evmCallE =
                            auctionCreateAuctionStartWord evmCallS := by
                        simp [auctionCreateAuctionStartWord, hcallState.executionEnv, evmCallE,
                          evmCallS, auctionUnpausePostState, storageStore_executionEnv, evmS,
                          initState]
                      have hduration :
                          auctionCreateAuctionDurationWord evmCallE =
                            auctionCreateAuctionDurationWord evmCallS := by
                        simpa [auctionCreateAuctionDurationWord] using
                          hcallState.storageLoad_codeOwner ⟨206⟩
                      have hoverE' :
                          UInt256.size ≤
                            (auctionCreateAuctionStartWord evmCallE).toNat +
                              (auctionCreateAuctionDurationWord evmCallE).toNat := by
                        simpa [evmCallE, auctionCreateAuctionStartWord,
                          auctionCreateAuctionDurationWord, initState, auctionSlotWord,
                          Solm.EVM.storageLoad, State.lookupAccount] using hoverE
                      simpa [hstart, hduration] using hoverE'
                    have hbody := auctionUnpauseBodyReverts_create_addOverflow evmS evmCallS
                      (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm hcond
                      (by simpa [evmS, evmCallS] using hcallS) hdec hoverS
                    exact (auctionCreateAuction_mintCallSuccessAddOverflowRevert
                        (σTarget := auctionUnpausePostMap σ_evm I) (σ := σ')
                        hosz hdec hoverE
                        (by simpa using rd3067))
                      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                  · by_cases hshort : o.size < 4
                    · have hzFalse : z = false := by
                        cases z
                        · rfl
                        · exfalso
                          have hdecNone : ABI.decodeReturnValue? uint256 o = none := by
                            have hnone := decodeReturnValue_uint256_none_short
                              (returndata := o) (by omega : o.size < 32)
                            simpa [uint256] using hnone
                          exact hdecodeFail ⟨rfl, hdecNone⟩
                      subst z
                      obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                        auctionUnpauseMintCall_transport
                          (cA := cA) (gh := gh) (bl := bl)
                          (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := Sat256.ofUInt256 g)
                          (cA' := cA') (σ' := σ') (z := false) (o := o)
                          (A' := A') _hAccounts hcallE
                      let evmCallS : EVM.State :=
                        { auctionUnpausePostState evmS with
                          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                      have hbody := auctionUnpauseBodyReverts_create_callFailure_short evmS
                        evmCallS
                        (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm
                        hcond (by simpa [evmS, evmCallS] using hcallS) hshort
                      exact (auctionCreateAuction_mintCallFailureShortRevert
                          (by simpa using rd3067) hshort hosz (by simp))
                        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                    · have hlen : 4 ≤ o.size := Nat.le_of_not_gt hshort
                      have hzFalse : z = false := by
                        cases z
                        · rfl
                        · exfalso
                          cases hdecOpt : ABI.decodeReturnValue? uint256 o with
                          | none =>
                              exact hdecodeFail ⟨rfl, hdecOpt⟩
                          | some ret =>
                              obtain ⟨nounId, hdec⟩ :=
                                auctionDecodeReturn_uint256_some_exists hdecOpt
                              by_cases hadd :
                                  (UInt256.ofNat I.header.timestamp).toNat +
                                      (auctionSlotWord ⟨206⟩ σ' I).toNat < UInt256.size
                              · exact hsuccess ⟨nounId, rfl, hdec, hadd⟩
                              · exact hoverCase
                                  ⟨nounId, rfl, hdec, Nat.le_of_not_gt hadd⟩
                      subst z
                      by_cases hnonError : o.extract 0 4 ≠ errorStringSelector
                      · obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                          auctionUnpauseMintCall_transport
                            (cA := cA) (gh := gh) (bl := bl)
                            (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            (cA' := cA') (σ' := σ') (z := false) (o := o)
                            (A' := A') _hAccounts hcallE
                        let evmCallS : EVM.State :=
                          { auctionUnpausePostState evmS with
                            accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                        have hbody := auctionUnpauseBodyReverts_create_callFailure_nonError evmS
                          evmCallS
                          (by simp only [evmS, initState]; exact hwv) hownerSolm hpausedSolm
                          hcond (by simpa [evmS, evmCallS] using hcallS) hlen hnonError
                        let mintFailureMem :=
                          o.write 0 (auctionUnpauseMintSelMem I) 128
                            ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
                        obtain ⟨preSel, hword, hneq⟩ :=
                          auctionMintFailureSelector_bridge
                            (o := o) (mem := mintFailureMem) hlen hnonError
                        exact (auctionCreateAuction_mintCallFailureSelectorRevert
                            (sel := UInt256.shiftRight preSel ⟨224⟩)
                            (by simpa [mintFailureMem] using rd3067) hlen hosz hword rfl
                            (u256_sub_ne_zero_of_ne hneq) (by simp))
                          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                      · have hselError : o.extract 0 4 = errorStringSelector := by
                          by_contra hsel
                          exact hnonError hsel
                        by_cases hshortString : o.size < 68
                        · obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                            auctionUnpauseMintCall_transport
                              (cA := cA) (gh := gh) (bl := bl)
                              (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                              (A := A) (I := I) (g := Sat256.ofUInt256 g)
                              (cA' := cA') (σ' := σ') (z := false) (o := o)
                              (A' := A') _hAccounts hcallE
                          let evmCallS : EVM.State :=
                            { auctionUnpausePostState evmS with
                              accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
                          have hbody :=
                            auctionUnpauseBodyReverts_create_callFailure_errorStringShort evmS
                              evmCallS
                              (by simp only [evmS, initState]; exact hwv) hownerSolm
                              hpausedSolm hcond (by simpa [evmS, evmCallS] using hcallS)
                              hlen hselError hshortString
                          let mintFailureMem :=
                            o.write 0 (auctionUnpauseMintSelMem I) 128
                              ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
                          obtain ⟨preSel, hword, hshr⟩ :=
                            auctionMintFailureErrorSelector_bridge
                              (o := o) (mem := mintFailureMem) hlen hselError
                          exact (auctionCreateAuction_mintCallFailureErrorStringShortRevert
                              (by simpa [mintFailureMem] using rd3067) hlen hshortString hosz
                              hword hshr (by simp))
                            |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                        · have hlong : 68 ≤ o.size := Nat.le_of_not_gt hshortString
                          have hsmallOut : o.size < (2 : Nat) ^ 138 :=
                            typedMintCall_output_size_lt_2pow138 hcallE (by omega)
                          have hsmallPayload :
                              (o.extract 4 o.size).size < (2 : Nat) ^ 255 := by
                            have hsub : (o.extract 4 o.size).size ≤ o.size := by
                              rw [ByteArray.size_extract]
                              omega
                            exact lt_of_le_of_lt hsub
                              (lt_trans hsmallOut (by norm_num))
                          let evmCallE : EVM.State :=
                            { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σ', substate := A', createdAccounts := cA' }
                          obtain ⟨σ'_solm, A'_solm, hcallS, _hcallState⟩ :=
                            auctionUnpauseMintCall_transport
                              (cA := cA) (gh := gh)
                              (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) (cA' := cA')
                              (σ' := σ') (z := false) (o := o) (A' := A')
                              _hAccounts hcallE
                          let evmCallS : EVM.State :=
                            { auctionUnpausePostState evmS with
                              accountMap := σ'_solm, substate := A'_solm,
                              createdAccounts := cA' }
                          let mintFailureMem :=
                            o.write 0 (auctionUnpauseMintSelMem I) 128
                              ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
                          obtain ⟨preSel, hword, hshr⟩ :=
                            auctionMintFailureErrorSelector_bridge
                              (o := o) (mem := mintFailureMem) hlen hselError
                          obtain ⟨_, _, rd5926⟩ :=
                            auctionCreateAuction_mintCallFailureErrorStringToDecoder
                              (by simpa [mintFailureMem] using rd3067) hlen hosz hword hshr
                              (by simp)
                          obtain ⟨_, _, rd5939⟩ :=
                            auctionCreateAuction_errorStringDecoderLongGuard rd5926 hlong hosz
                              (by simp)
                          have hmload64 :=
                            auctionMintFailureMemSel_mload64 I (by omega : 32 ≤ o.size) hosz
                          obtain ⟨_, _, rd5942⟩ :=
                            auctionCreateAuction_errorStringDecoderLoadFreePtr rd5939
                              (by simpa [mintFailureMem] using hmload64) (by simp)
                          obtain ⟨_, _, rd5951⟩ :=
                            auctionCreateAuction_errorStringDecoderPrepareCopy rd5942 (by simp)
                          obtain ⟨_, _, rd5952⟩ :=
                            auctionCreateAuction_errorStringDecoderReturndataCopy rd5951 rfl
                              hlong hosz (by simp)
                          obtain ⟨off, hoff⟩ := readNat?_exists_of_length
                            (bytes := (o.extract 4 o.size).toList) (off := 0) (by
                              rw [byteArray_toList_eq, Array.length_toList]
                              change 0 + 32 ≤ (o.extract 4 o.size).size
                              rw [ByteArray.size_extract]
                              omega)
                          have hoffLt : off < UInt256.size := readNat?_some_lt_uint256 hoff
                          have hmloadOff :=
                            auctionErrorStringCopy_mloadOffset I hlong hosz hsmallOut hoff
                          obtain ⟨_, _, rd5954⟩ :=
                            auctionCreateAuction_errorStringDecoderLoadOffset rd5952
                              (by simpa [mintFailureMem] using hmloadOff) (by simp)
                          by_cases hoffMax : off ≤ ABI.solcMaxU64
                          · by_cases hoffBound : off + 36 ≤ o.size
                            · obtain ⟨_, _, rd5987⟩ :=
                                auctionCreateAuction_errorStringDecoderOffsetBoundsOk rd5954
                                  (by simpa [UInt256.toNat_ofNat_of_lt hoffLt] using hoffMax)
                                  (by simpa [UInt256.toNat_ofNat_of_lt hoffLt]
                                    using hoffBound)
                                  hosz (by simp)
                              obtain ⟨len, hlenWord⟩ := readNat?_exists_of_length
                                (bytes := (o.extract 4 o.size).toList) (off := off) (by
                                  rw [byteArray_toList_eq, Array.length_toList]
                                  change off + 32 ≤ (o.extract 4 o.size).size
                                  rw [ByteArray.size_extract]
                                  omega)
                              have hlenLt : len < UInt256.size :=
                                readNat?_some_lt_uint256 hlenWord
                              have hmloadLen :=
                                auctionErrorStringCopy_mloadLength I hlong hosz hsmallOut
                                  hoffBound hlenWord
                              by_cases hlenMax : len ≤ ABI.solcMaxU64
                              · obtain ⟨_, _, rd6011⟩ :=
                                  auctionCreateAuction_errorStringDecoderLoadLengthOk rd5987
                                    (by simpa [mintFailureMem] using hmloadLen)
                                    (by simpa [UInt256.toNat_ofNat_of_lt hlenLt]
                                      using hlenMax)
                                    (by simp)
                                by_cases hpayloadBound : off + len + 36 ≤ o.size
                                · have hgtPayload :=
                                    errorStringPayloadBoundsGuard_zero hosz hsmallOut
                                      hoffMax hlenMax hpayloadBound
                                  obtain ⟨_, _, rd6037⟩ :=
                                    auctionCreateAuction_errorStringDecoderPayloadBoundsOk
                                      rd6011 (by simpa using hgtPayload) (by simp)
                                  by_cases halloc :
                                      errorStringNewFreeNat off len ≤ ABI.solcMaxU64
                                  · obtain ⟨payload, hpayloadRead⟩ := readBytes?_exists_of_length
                                      (bytes := (o.extract 4 o.size).toList)
                                      (off := off + 32) (len := len) (by
                                        rw [byteArray_toList_eq, Array.length_toList]
                                        change (off + 32) + len ≤
                                          (o.extract 4 o.size).size
                                        rw [ByteArray.size_extract]
                                        omega)
                                    have hdecSome :
                                        ABI.decodeReturnValue? .string (o.extract 4 o.size) =
                                          some (.bytes (ByteArray.mk payload.toArray)) :=
                                      decodeReturnValue_string_some_of_reads hsmallPayload hoff
                                        hoffMax hlenWord hlenMax hpayloadRead
                                    have hgtNewFree :=
                                      errorStringNewFreeWord_gt_max64_zero hoffMax hlenMax
                                        halloc
                                    have hltNewFree :=
                                      errorStringNewFreeWord_lt_128_zero hoffMax hlenMax
                                    let copyLen :=
                                      UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat o.size
                                    let memSel := o.write 0 mintFailureMem 0 4
                                    let memCopy := o.write 4 memSel 128 copyLen.toNat
                                    let aw64 :=
                                      UInt256.ofNat
                                        (MachineState.M (UInt256.ofNat 5).toNat
                                          (⟨64⟩ : UInt256).toNat 32)
                                    let awCopy :=
                                      UInt256.ofNat (MachineState.M aw64.toNat 128 copyLen.toNat)
                                    let awOff :=
                                      UInt256.ofNat
                                        (MachineState.M awCopy.toNat
                                          (⟨128⟩ : UInt256).toNat 32)
                                    let awLen :=
                                      UInt256.ofNat
                                        (MachineState.M awOff.toNat
                                          ((⟨128⟩ : UInt256) + UInt256.ofNat off).toNat 32)
                                    let offW := UInt256.ofNat off
                                    let lenW := UInt256.ofNat len
                                    let payloadLenW := (offW + lenW) + (⟨32⟩ : UInt256)
                                    let roundedLenW :=
                                      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                                        (payloadLenW + ⟨31⟩)
                                    let newFree := (⟨128⟩ : UInt256) + roundedLenW
                                    let memFree :=
                                      (UInt256.toByteArray newFree).write 0 memCopy 64 32
                                    let awFree :=
                                      UInt256.ofNat
                                        (MachineState.M awLen.toNat
                                          (⟨64⟩ : UInt256).toNat 32)
                                    obtain ⟨_, _, rd3143⟩ :=
                                      auctionCreateAuction_errorStringDecoderCopyToReturn
                                        (mem := memCopy) (aw := awLen) (fmp := (⟨128⟩ : UInt256))
                                        (off := UInt256.ofNat off) (len := UInt256.ofNat len)
                                        rd6037 (by simpa using hgtNewFree)
                                        (by simpa using hltNewFree)
                                        (by simp)
                                    have hawDecoded :=
                                      auctionErrorStringCopy_awDecoded_bounds hlong hsmallOut
                                        hoffBound hosz
                                    have hawLenBounds :
                                        3 ≤ awLen.toNat ∧ awLen.toNat * 32 < UInt256.size := by
                                      simpa [copyLen, aw64, awCopy, awOff, awLen]
                                        using hawDecoded
                                    have hmload64Pause :
                                        (if (⟨64⟩ : UInt256).toNat ≥ memFree.size ∨
                                            (⟨64⟩ : UInt256) ≥ awFree * ⟨32⟩ then ⟨0⟩
                                          else UInt256.ofNat
                                            (fromByteArrayBigEndian
                                              (memFree.readWithPadding
                                                (⟨64⟩ : UInt256).toNat 32))) =
                                          newFree := by
                                      simpa [memFree, awFree] using
                                        errorStringMemFree_mload64_of_aw memCopy awLen newFree
                                          hawLenBounds.1 hawLenBounds.2
                                    have hnewFreeNat :
                                        newFree.toNat = errorStringNewFreeNat off len := by
                                      simpa [offW, lenW, payloadLenW, roundedLenW, newFree] using
                                        errorStringNewFreeWord_toNat hoffMax hlenMax
                                    have hnewFreeGe : 96 ≤ newFree.toNat := by
                                      rw [hnewFreeNat]
                                      simp [errorStringNewFreeNat]
                                      omega
                                    have hnewFreeLe : newFree.toNat ≤ ABI.solcMaxU64 := by
                                      rw [hnewFreeNat]
                                      exact halloc
                                    have hmemFree96 : 96 ≤ memFree.size := by
                                      have hgap : 64 - memCopy.size < USize.size :=
                                        lt_of_le_of_lt (Nat.sub_le _ _)
                                          (by native_decide : 64 < USize.size)
                                      have hsz :=
                                        toByteArray_write_size_ge_off_add32 newFree memCopy 64
                                          hgap
                                      dsimp [memFree]
                                      omega
                                    have hreadFree64 :
                                        memFree.readWithPadding 64 32 =
                                          UInt256.toByteArray newFree := by
                                      dsimp [memFree]
                                      exact toByteArray_write_read_back_of_gap newFree memCopy 64
                                        (lt_of_le_of_lt (Nat.sub_le _ _)
                                          (by native_decide : 64 < USize.size))
                                    have hawFreeBounds :
                                        3 ≤ awFree.toNat ∧ awFree.toNat * 32 < UInt256.size := by
                                      have haddr64 :
                                          (⟨64⟩ : UInt256).toNat ≤ ABI.solcMaxU64 + 68 := by
                                        native_decide
                                      have h :=
                                        auctionAwMstore32_bounds (aw := awLen)
                                          (addr := (⟨64⟩ : UInt256)) hawLenBounds.1
                                          hawLenBounds.2 haddr64
                                      simpa [awFree] using h
                                    have hmload64Event :
                                        (if (⟨64⟩ : UInt256).toNat ≥
                                              (auctionEventMemFrom memFree I newFree).size ∨
                                            (⟨64⟩ : UInt256) ≥
                                              (UInt256.ofNat
                                                (MachineState.M
                                                  (UInt256.ofNat
                                                    (MachineState.M awFree.toNat
                                                      (⟨64⟩ : UInt256).toNat 32)).toNat
                                                  newFree.toNat 32)) * ⟨32⟩ then
                                            ⟨0⟩
                                          else UInt256.ofNat
                                            (fromByteArrayBigEndian
                                              ((auctionEventMemFrom memFree I newFree)
                                                |>.readWithPadding
                                                  (⟨64⟩ : UInt256).toNat 32))) =
                                          newFree := by
                                      exact auctionEventMemFrom_mload64_of_base I hmemFree96
                                        hreadFree64 hawFreeBounds.1 hawFreeBounds.2
                                        hnewFreeGe hnewFreeLe
                                    have hmload64Err :
                                        (if (⟨64⟩ : UInt256).toNat ≥
                                              (auctionPausablePausedMem3From memFree newFree).size ∨
                                            (⟨64⟩ : UInt256) ≥
                                              auctionPausablePausedAw3From awFree newFree *
                                                ⟨32⟩ then ⟨0⟩
                                          else UInt256.ofNat
                                            (fromByteArrayBigEndian
                                              ((auctionPausablePausedMem3From memFree newFree)
                                                |>.readWithPadding
                                                  (⟨64⟩ : UInt256).toNat 32))) =
                                          newFree := by
                                      exact auctionPausablePausedMem3From_mload64_of_base
                                        hmemFree96 hreadFree64 hawFreeBounds.1 hawFreeBounds.2
                                        hnewFreeGe hnewFreeLe
                                    have hptr :
                                        (⟨128⟩ : UInt256) + UInt256.ofNat off ≠ ⟨0⟩ := by
                                      intro hz
                                      have hptrNat :
                                          ((⟨128⟩ : UInt256) + UInt256.ofNat off).toNat =
                                            128 + off := by
                                        rw [uadd_toNat,
                                          show (⟨128⟩ : UInt256).toNat = 128 from by decide,
                                          UInt256.toNat_ofNat_of_lt hoffLt]
                                        rw [Nat.mod_eq_of_lt]
                                        norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
                                        omega
                                      have hzNat := congrArg UInt256.toNat hz
                                      rw [hptrNat] at hzNat
                                      norm_num at hzNat
                                    obtain ⟨_, _, rd3655⟩ :=
                                      auctionCreateAuction_errorStringDecodedToPause rd3143 hptr
                                        (by simp)
                                    have hpausedWordCall :
                                        auctionPausedWord σ' I =
                                          UInt256.land
                                            (Solm.EVM.storageLoad evmCallS
                                              evmCallS.executionEnv.codeOwner ⟨51⟩)
                                            ⟨255⟩ := by
                                      have hslot :
                                          auctionSlotWord ⟨51⟩ σ' I =
                                            Solm.EVM.storageLoad evmCallS
                                              evmCallS.executionEnv.codeOwner ⟨51⟩ := by
                                        have h :=
                                          _hcallState.storageLoad_codeOwner ⟨51⟩
                                        simpa [evmCallE, evmCallS, initState, auctionSlotWord,
                                          Solm.EVM.storageLoad, State.lookupAccount] using h
                                      rw [auctionPausedWord, hslot]
                                    have hadd32Nat :
                                        ((⟨32⟩ : UInt256) + newFree).toNat =
                                          32 + newFree.toNat := by
                                      rw [uadd_toNat,
                                        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
                                      rw [Nat.mod_eq_of_lt]
                                      norm_num [ABI.solcMaxU64, UInt256.size] at hnewFreeLe ⊢
                                      omega
                                    have hlen32 :
                                        UInt256.sub ((⟨32⟩ : UInt256) + newFree) newFree =
                                          ⟨32⟩ := by
                                      apply u256_inj
                                      rw [usub_toNat]
                                      · rw [hadd32Nat,
                                          show (⟨32⟩ : UInt256).toNat = 32 from by decide]
                                        omega
                                      · rw [hadd32Nat]
                                        omega
                                    have hadd100Nat :
                                        ((⟨100⟩ : UInt256) + newFree).toNat =
                                          100 + newFree.toNat := by
                                      rw [uadd_toNat,
                                        show (⟨100⟩ : UInt256).toNat = 100 from by decide]
                                      rw [Nat.mod_eq_of_lt]
                                      norm_num [ABI.solcMaxU64, UInt256.size] at hnewFreeLe ⊢
                                      omega
                                    have hlen100 :
                                        UInt256.sub ((⟨100⟩ : UInt256) + newFree) newFree =
                                          ⟨100⟩ := by
                                      apply u256_inj
                                      rw [usub_toNat]
                                      · rw [hadd100Nat,
                                          show (⟨100⟩ : UInt256).toNat = 100 from by decide]
                                        omega
                                      · rw [hadd100Nat]
                                        omega
                                    by_cases hpausedZeroCall :
                                        UInt256.land
                                            (Solm.EVM.storageLoad evmCallS
                                              evmCallS.executionEnv.codeOwner ⟨51⟩)
                                            ⟨255⟩ =
                                          ⟨0⟩
                                    · have hzeroSource : auctionPausedWord σ' I = ⟨0⟩ := by
                                        simpa [hpausedWordCall] using hpausedZeroCall
                                      have hbody :=
                                        auctionUnpauseBodyReturns_create_callFailure_errorString
                                          evmS evmCallS
                                          (by simp only [evmS, initState]; exact hwv)
                                          hownerSolm hpausedSolm hcond
                                          (by simpa [evmS, evmCallS] using hcallS)
                                          hlen hselError hlong hsmallPayload hoff hoffMax
                                          hoffBound hlenWord hlenMax hpayloadBound halloc
                                          hdecSome hpausedZeroCall
                                      obtain ⟨_, _, _, _, rd2850⟩ :=
                                        auctionPauseRoutine_success_from_mem
                                          (g := Sat256.ofUInt256 g) _hperm hzeroSource
                                          (ret := (⟨2850⟩ : UInt256))
                                          (R := [(⟨128⟩ : UInt256) + UInt256.ofNat off,
                                            ⟨1163⟩, ⟨413⟩, auctionSelWord I])
                                          (by native_decide) hmload64Pause hmload64Event hlen32
                                          (by simp)
                                          (by
                                            simpa [memFree, awFree, newFree, roundedLenW,
                                              payloadLenW, offW, lenW] using rd3655)
                                      have rdret :=
                                        auctionCreateAuction_errorStringPauseReturnTail rd2850
                                      have hpostAccounts :
                                          accountMapEquiv (auctionPausePostMap σ' I)
                                            (auctionPausePostState evmCallE).accountMap := by
                                        apply accountMapEquiv.of_eq
                                        simp [auctionPausePostMap, auctionPausePostState,
                                          evmCallE, initState, storageStore_accountMap,
                                          auctionSlotWord, Solm.EVM.storageLoad,
                                          State.lookupAccount, Account.lookupStorage]
                                      have hpostState :
                                          EVMStateEquiv (auctionPausePostState evmCallE)
                                            (auctionPausePostState evmCallS) := by
                                        exact _hcallState.storageStore_codeOwner ⟨51⟩ (by
                                          have hslot :=
                                            _hcallState.storageLoad_codeOwner ⟨51⟩
                                          simpa [auctionPausePostState, evmCallE, evmCallS,
                                            initState, auctionSlotWord, Solm.EVM.storageLoad,
                                            State.lookupAccount] using
                                              congrArg auctionPausedSetTrueWord hslot)
                                      exact rdret.reEquivExecutionGenEVMStateEquiv _hcode
                                        hdispatch hdecode hbody
                                        (by simp [auctionPausePostState, evmCallE, initState,
                                          storageStore_createdAccounts])
                                        hpostAccounts
                                        hpostState
                                        (returnEquiv.fallthrough rfl rfl (by native_decide))
                                    · have hnzSource : auctionPausedWord σ' I ≠ ⟨0⟩ := by
                                        intro hzero
                                        exact hpausedZeroCall
                                          (by simpa [hpausedWordCall] using hzero)
                                      have hbody :=
                                        auctionUnpauseBodyReverts_create_callFailure_errorStringPaused
                                          evmS evmCallS
                                          (by simp only [evmS, initState]; exact hwv)
                                          hownerSolm hpausedSolm hcond
                                          (by simpa [evmS, evmCallS] using hcallS)
                                          hlen hselError hlong hsmallPayload hoff hoffMax
                                          hoffBound hlenWord hlenMax hpayloadBound halloc
                                          hdecSome hpausedZeroCall
                                      exact (auctionPauseRoutine_revert_paused_from_mem
                                          (g := Sat256.ofUInt256 g) _hperm hnzSource
                                          (ret := (⟨2850⟩ : UInt256))
                                          (R := [(⟨128⟩ : UInt256) + UInt256.ofNat off,
                                            ⟨1163⟩, ⟨413⟩, auctionSelWord I])
                                          hmload64Pause hmload64Err hlen100 (by simp)
                                          (by
                                            simpa [memFree, awFree, newFree, roundedLenW,
                                              payloadLenW, offW, lenW] using rd3655))
                                        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                                  · have hallocGt :
                                        ABI.solcMaxU64 < errorStringNewFreeNat off len :=
                                      Nat.lt_of_not_ge halloc
                                    have hgtNewFree :=
                                      errorStringNewFreeWord_gt_max64_one hoffMax hlenMax
                                        hallocGt
                                    have hguard :
                                        UInt256.lor
                                            (UInt256.gt
                                              ((⟨128⟩ : UInt256) +
                                                UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                                                  ((((UInt256.ofNat off + UInt256.ofNat len) +
                                                            ⟨32⟩ : UInt256) + ⟨31⟩)))
                                              (⟨0xffffffffffffffff⟩ : UInt256))
                                            (UInt256.lt
                                              ((⟨128⟩ : UInt256) +
                                                UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                                                  ((((UInt256.ofNat off + UInt256.ofNat len) +
                                                            ⟨32⟩ : UInt256) + ⟨31⟩)))
                                              (⟨128⟩ : UInt256)) ≠
                                          ⟨0⟩ := by
                                      intro hz
                                      rw [hgtNewFree] at hz
                                      exact u256_lor_one_ne_zero _ hz
                                    have hbody :=
                                      auctionUnpauseBodyReverts_create_callFailure_errorStringAllocU64
                                        evmS evmCallS
                                        (by simp only [evmS, initState]; exact hwv)
                                        hownerSolm hpausedSolm hcond
                                        (by simpa [evmS, evmCallS] using hcallS)
                                        hlen hselError hlong hsmallPayload hoff hoffMax
                                        hoffBound hlenWord hlenMax hpayloadBound hallocGt
                                    exact
                                      (auctionCreateAuction_errorStringDecoderCopyToReturnAllocFail
                                          rd6037 hguard (by simp))
                                        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                                · have hpayloadBoundGt : o.size < off + len + 36 :=
                                    Nat.lt_of_not_ge hpayloadBound
                                  have hgtPayload :=
                                    errorStringPayloadBoundsGuard_one hosz hsmallOut
                                      hoffMax hlenMax hpayloadBoundGt
                                  have hguard :
                                      UInt256.gt
                                          ((((⟨128⟩ : UInt256) + UInt256.ofNat off) +
                                              UInt256.ofNat len) + ⟨32⟩)
                                          (((⟨128⟩ : UInt256) + UInt256.ofNat o.size) +
                                            UInt256.lnot (⟨3⟩ : UInt256)) ≠
                                        ⟨0⟩ := by
                                    rw [hgtPayload]
                                    decide
                                  obtain ⟨_, _, rd3143⟩ :=
                                    auctionCreateAuction_errorStringDecoderPayloadBoundsFail
                                      rd6011 hguard (by simp)
                                  have hbody :=
                                    auctionUnpauseBodyReverts_create_callFailure_errorStringPayloadBounds
                                      evmS evmCallS
                                      (by simp only [evmS, initState]; exact hwv)
                                      hownerSolm hpausedSolm hcond
                                      (by simpa [evmS, evmCallS] using hcallS)
                                      hlen hselError hlong hsmallPayload hoff hoffMax
                                      hoffBound hlenWord hlenMax hpayloadBoundGt
                                  exact
                                    (auctionCreateAuction_errorStringDecodedNullRevert rd3143
                                        hosz (by simp))
                                      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                              · have hlenMaxGt : ABI.solcMaxU64 < len :=
                                  Nat.lt_of_not_ge hlenMax
                                have hgtLen :
                                    UInt256.gt (UInt256.ofNat len)
                                        (⟨0xffffffffffffffff⟩ : UInt256) =
                                      ⟨1⟩ := by
                                  apply ugt_one
                                  rw [UInt256.toNat_ofNat_of_lt hlenLt]
                                  change ABI.solcMaxU64 < len
                                  exact hlenMaxGt
                                have hguard :
                                    UInt256.gt (UInt256.ofNat len)
                                        (⟨0xffffffffffffffff⟩ : UInt256) ≠
                                      ⟨0⟩ := by
                                  rw [hgtLen]
                                  decide
                                obtain ⟨_, _, rd3143⟩ :=
                                  auctionCreateAuction_errorStringDecoderLoadLengthFail rd5987
                                    (by simpa [mintFailureMem] using hmloadLen) hguard
                                    (by simp)
                                have hbody :=
                                  auctionUnpauseBodyReverts_create_callFailure_errorStringLengthMax
                                    evmS evmCallS
                                    (by simp only [evmS, initState]; exact hwv)
                                    hownerSolm hpausedSolm hcond
                                    (by simpa [evmS, evmCallS] using hcallS)
                                    hlen hselError hlong hsmallPayload hoff hoffMax
                                    hoffBound hlenWord hlenMaxGt
                                exact
                                  (auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz
                                      (by simp))
                                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                            · have hoffBoundGt : o.size < off + 36 :=
                                Nat.lt_of_not_ge hoffBound
                              have hoffAddNat :
                                  (UInt256.ofNat off + (⟨36⟩ : UInt256)).toNat =
                                    off + 36 := by
                                rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hoffLt,
                                  show (⟨36⟩ : UInt256).toNat = 36 from by decide]
                                rw [Nat.mod_eq_of_lt]
                                norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
                                omega
                              have hgtLen :
                                  UInt256.gt
                                      (UInt256.ofNat off + (⟨36⟩ : UInt256))
                                      (UInt256.ofNat o.size) =
                                    ⟨1⟩ := by
                                apply ugt_one
                                rw [hoffAddNat, UInt256.toNat_ofNat_of_lt hosz]
                                exact hoffBoundGt
                              have hguard :
                                  UInt256.lor
                                      (UInt256.gt (UInt256.ofNat off)
                                        (⟨0xffffffffffffffff⟩ : UInt256))
                                      (UInt256.gt
                                        (UInt256.ofNat off + (⟨36⟩ : UInt256))
                                        (UInt256.ofNat o.size)) ≠
                                    ⟨0⟩ := by
                                intro hz
                                rw [hgtLen] at hz
                                rw [u256_lor_comm] at hz
                                exact u256_lor_one_ne_zero _ hz
                              obtain ⟨_, _, rd3143⟩ :=
                                auctionCreateAuction_errorStringDecoderOffsetBoundsFail rd5954
                                  hguard (by simp)
                              have hbody :=
                                auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetBounds
                                  evmS evmCallS
                                  (by simp only [evmS, initState]; exact hwv)
                                  hownerSolm hpausedSolm hcond
                                  (by simpa [evmS, evmCallS] using hcallS)
                                  hlen hselError hlong hsmallPayload hoff hoffMax hoffBoundGt
                              exact
                                (auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz
                                    (by simp))
                                  |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
                          · have hoffMaxGt : ABI.solcMaxU64 < off := Nat.lt_of_not_ge hoffMax
                            have hgtMax :
                                UInt256.gt (UInt256.ofNat off)
                                    (⟨0xffffffffffffffff⟩ : UInt256) =
                                  ⟨1⟩ := by
                              apply ugt_one
                              rw [UInt256.toNat_ofNat_of_lt hoffLt]
                              change ABI.solcMaxU64 < off
                              exact hoffMaxGt
                            have hguard :
                                UInt256.lor
                                    (UInt256.gt (UInt256.ofNat off)
                                      (⟨0xffffffffffffffff⟩ : UInt256))
                                    (UInt256.gt
                                      (UInt256.ofNat off + (⟨36⟩ : UInt256))
                                      (UInt256.ofNat o.size)) ≠
                                  ⟨0⟩ := by
                              intro hz
                              rw [hgtMax] at hz
                              exact u256_lor_one_ne_zero _ hz
                            obtain ⟨_, _, rd3143⟩ :=
                              auctionCreateAuction_errorStringDecoderOffsetBoundsFail rd5954
                                hguard (by simp)
                            have hbody :=
                              auctionUnpauseBodyReverts_create_callFailure_errorStringOffsetMax
                                evmS evmCallS
                                (by simp only [evmS, initState]; exact hwv)
                                hownerSolm hpausedSolm hcond
                                (by simpa [evmS, evmCallS] using hcallS)
                                hlen hselError hlong hsmallPayload hoff hoffMaxGt
                            exact
                              (auctionCreateAuction_errorStringDecodedNullRevert rd3143 hosz
                                  (by simp))
                                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask ≠
            auctionSourceWord evmS.executionEnv := by
        intro h
        apply howner
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
            auctionSourceWord] using h
        simpa [hownerWord] using hmap
      have hbody := auctionUnpauseBodyReverts_owner evmS
        (by simp only [evmS, initState]; exact hwv) hownerSolm
      exact (auctionX_unpause_revert_owner (g := Sat256.ofUInt256 g) hwv howner hreach)
        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · have hbody := auctionUnpauseBodyReverts_callvalue
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simpa only [initState] using hwv)
    exact (auctionX_unpause_callvalue_ne hreach hwv)
      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction
