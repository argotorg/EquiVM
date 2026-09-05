import Benchmarks.Auction.CreateBidRefund
import Benchmarks.Auction.SettleAuctionTransitions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem accountMapEquiv_balance_word {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) :
    ((σ.find? addr).elim (⟨0⟩ : UInt256) (fun acc => acc.balance)) =
      ((τ.find? addr).elim (⟨0⟩ : UInt256) (fun acc => acc.balance)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact hστ.2.1

theorem auctionCreateBidRefundFallbackWethNoCodeRevertAnyMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner marker aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) =
        ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
        auctionSelWord I]
      mem aw o (cA', σ') k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memSel := (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
    mem freePtr.toNat 32
  let awSel : UInt256 := UInt256.ofNat (MachineState.M awFree.toNat freePtr.toNat 32)
  let freePtr2 :=
    if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree2 : UInt256 :=
    UInt256.ofNat (MachineState.M awSel.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [⟨0⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩,
          auctionSelWord I])
      mem aw o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awSel - Cₘ awFree) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload (Cₘ awFree2 - Cₘ awSel) freePtr2 awFree2 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  exact auctionExtcodesizeGuardMissingPush0 (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417
    (by simpa [weth] using hwethCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem auctionCreateBidTransitionReverts_refundLowLevelNotMadeWethNoCode
    (evm : EVM.State) (I : ExecutionEnv)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnotMade :
      ¬ (EVM.wordOfInt (Int.ofNat
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat) ≤
          ((auctionCreateBidEnterState evm).accountMap.find?
            (auctionCreateBidEnterState evm).executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
        (auctionCreateBidEnterState evm).executionEnv.depth ≠ 1024))
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord (auctionCreateBidEnterState evm).accountMap
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨202⟩)
            solcAddrMask) =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (auctionCreateBidStore I)
      createBidTransition.body .reverted := by
  let evmEnter := auctionCreateBidEnterState evm
  let recipient := AccountAddress.ofNat
    (auctionPackedBidderWord
      (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat
  let target := EVM.address recipient
  let amount := Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨208⟩
  let evmRefund := { evmEnter with substate := (evmEnter.addAccessedAccount target).substate }
  have hrefund :
      callViaEVM evmEnter target (Int.ofNat amount.toNat) ByteArray.empty
        (false, evmRefund, ByteArray.empty) true := by
    apply callViaEVM.callNotMade
    · rfl
    · rfl
    · simpa [evmEnter, target, recipient, amount] using hnotMade
  have hwethLookupZero :
      (UInt256.ofNat (((evmRefund.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0 := by
    let wethSolm :=
      UInt256.land (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner ⟨202⟩)
        solcAddrMask
    have hwethAtRefund :
        Reasoning.Theory.uniswapExtCodeSizeWord evmRefund.accountMap wethSolm = ⟨0⟩ := by
      simpa [evmRefund, evmEnter, target, recipient, amount, wethSolm] using hwethCode
    have hzero :=
      auctionUniswapExtCodeSizeWord_zero_lookup_code_zero
        (σ := evmRefund.accountMap) (target := wethSolm)
        (addr := AccountAddress.ofUInt256 wethSolm) rfl hwethAtRefund
    have haddr : AccountAddress.ofNat wethSolm.toNat = AccountAddress.ofUInt256 wethSolm := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [State.lookupAccount, wethSolm, haddr] using hzero
  exact auctionCreateBidTransitionReverts_refundLowLevelFailureWethNoCode evm evmRefund I
    hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder
    (by simpa [evmEnter, target, recipient, amount] using hrefund)
    hwethLookupZero

end Auction
