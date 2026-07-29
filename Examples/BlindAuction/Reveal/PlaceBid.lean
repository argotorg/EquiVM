import Examples.BlindAuction.Reveal.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000
namespace BlindAuction

def scratch_placeBidStore (bidder : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "value" (.int (Int.ofNat value.toNat))).insert "bidder" (.address bidder)

def scratch_placeBidAfterPending (evm : EVM.State) (oldAddr : AccountAddress)
    (sum : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (pendingReturnsSlot (.address oldAddr)) sum

def scratch_placeBidAfterHigh (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value

def scratch_placeBidAfterBidder (evm : EVM.State) (bidder : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (SimpleAuction.simpleAuctionSetAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (UInt256.ofNat bidder.val))

theorem scratch_addressWord_canonical (a : AccountAddress) :
    (UInt256.ofNat a.val).toNat < EVM.addressModulus := by
  rw [UInt256.toNat_ofNat_of_lt
    (lt_of_lt_of_le a.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt

theorem scratch_placeBidStore_value (bidder : AccountAddress) (value : UInt256) :
    (scratch_placeBidStore bidder value).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_placeBidStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_placeBidStore_bidder (bidder : AccountAddress) (value : UInt256) :
    (scratch_placeBidStore bidder value).get? "bidder" = some (.address bidder) := by
  unfold scratch_placeBidStore
  exact store_get_self _ _ _

theorem scratch_placeBidStore_base_none (bidder : AccountAddress) (value : UInt256)
    {name : Ident} (hname : name ≠ "value") (hname' : name ≠ "bidder") :
    (scratch_placeBidStore bidder value).get? name = none := by
  unfold scratch_placeBidStore
  rw [store_get_ne]
  · rw [store_get_ne]
    · simp
    · simp [beq_eq_false_iff_ne]
      exact fun h => hname h.symm
  · simp [beq_eq_false_iff_ne]
    exact fun h => hname' h.symm

theorem scratch_placeBid_lookup :
    lookupCallable? blindAuctionContract "placeBid" = some placeBidFn.toCallable := by
  rfl

theorem scratch_placeBid_bind (bidder : AccountAddress) (value : UInt256) :
    bindParams? placeBidFn.params [.address bidder, .int (Int.ofNat value.toNat)] =
      some (scratch_placeBidStore bidder value) := by
  rfl

theorem scratch_blindAuctionStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (blindAuctionAddrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (SimpleAuction.simpleAuctionSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  simpa [blindAuctionAddrLoc, SimpleAuction.simpleAuctionAddrLoc] using
    SimpleAuction.simpleAuctionStorageLocStore_address_offset0 evm slot addr hcanon

theorem scratch_eval_placeBid_highestBid
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage highestBidRef) = .ok (.int (Int.ofNat high.toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := highestBidRef)
    (er := { base := "highestBid", steps := [] })
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc ⟨6⟩)]
  · rw [blindAuctionStorageLocLoad_uint256, hhigh]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidRef, uint256St]
  · exact blindAuctionConfig_storage_highestBid

theorem scratch_eval_placeBid_value_le_highestBid_true
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hle : value.toNat ≤ high.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .le (.var "value") (.storage highestBidRef)) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
    (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value), EvalResult.bind, bind]
  rw [scratch_eval_placeBid_highestBid evm bidder value high hhigh]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem scratch_eval_placeBid_value_le_highestBid_false
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hlt : high.toNat < value.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .le (.var "value") (.storage highestBidRef)) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
    (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value), EvalResult.bind, bind]
  rw [scratch_eval_placeBid_highestBid evm bidder value high hhigh]
  have hltInt : (Int.ofNat high.toNat) < Int.ofNat value.toNat := Int.ofNat_lt.mpr hlt
  have hnot : ¬ Int.ofNat value.toNat ≤ Int.ofNat high.toNat := not_le_of_gt hltInt
  simp [evalBinaryOp?, hnot, hlt]
  all_goals decide

theorem scratch_eval_placeBid_highestBidder
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage highestBidderRef) =
        .ok (.address (AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := highestBidderRef)
    (er := { base := "highestBidder", steps := [] })
    (t := .address)
    (loc := blindAuctionAddrLoc ⟨5⟩)]
  · rw [blindAuctionStorageLocLoad_address_offset0, hold]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidderRef, addrSt]
  · exact blindAuctionConfig_storage_highestBidder

theorem scratch_eval_placeBid_highestBidder_ne_zero_false
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .ne (.storage highestBidderRef) zeroAddr) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_highestBidder evm bidder value old hold,
    EvalResult.bind, bind]
  simp [zeroAddr, addrSt, evalExpr?, hzero, evalBinaryOp?, castValue?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, AccountAddress.ofNat]
  all_goals decide

theorem scratch_eval_placeBid_highestBidder_ne_zero_true
    (evm : EVM.State) (bidder : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.binary .ne (.storage highestBidderRef) zeroAddr) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_highestBidder evm bidder value old hold,
    EvalResult.bind, bind]
  by_cases haddr :
      AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat = (0 : AccountAddress)
  · exfalso
    apply hnonzero
    apply u256_inj
    have hcanon := solcAddrMask_result_canonical old
    have hmod : (UInt256.land old solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land old solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hnat := congrArg Fin.val haddr
    simp [AccountAddress.ofNat, hmod] at hnat
    exact hnat
  · have hnotdiv : ¬ AccountAddress.size ∣ (UInt256.land old solcAddrMask).toNat := by
      intro hdiv
      have hcanon := solcAddrMask_result_canonical old
      have hltSize : (UInt256.land old solcAddrMask).toNat < AccountAddress.size := by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
      obtain ⟨k, hk⟩ := hdiv
      cases k with
      | zero =>
          apply hnonzero
          apply u256_inj
          simp [hk]
      | succ k =>
          have hle : AccountAddress.size ≤ (UInt256.land old solcAddrMask).toNat := by
            rw [hk]
            nlinarith [show 0 < AccountAddress.size by decide]
          omega
    simp [zeroAddr, addrSt, evalExpr?, evalBinaryOp?, castValue?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, AccountAddress.ofNat, haddr, hnotdiv]
    all_goals decide
  all_goals decide

theorem scratch_evalStorageRef_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (pendingReturnsRef (.storage highestBidderRef)) =
    .ok { base := "pendingReturns", steps := [.mindex (.address oldAddr)] } := by
  subst oldAddr
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, pendingReturnsRef,
    scratch_eval_placeBid_highestBidder evm bidder value old hold, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem scratch_eval_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old pending : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (.storage (pendingReturnsRef (.storage highestBidderRef))) =
        .ok (.int (Int.ofNat pending.toNat)) := by
  rw [evalExpr_storage_scalar (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (slot := pendingReturnsRef (.storage highestBidderRef))
    (er := { base := "pendingReturns", steps := [.mindex (.address oldAddr)] })
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc (pendingReturnsSlot (.address oldAddr)))]
  · rw [blindAuctionStorageLocLoad_uint256, hpending]
  · exact scratch_placeBidStore_base_none bidder value (by decide) (by decide)
  · exact scratch_evalStorageRef_placeBid_pendingReturns evm bidder oldAddr value old hold holdAddr
  · simp [storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?,
      pendingReturnsRef, uint256St]
  · exact blindAuctionConfig_storage_pendingReturns (.address oldAddr)

theorem scratch_eval_placeBid_pending_add
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old high pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (u256 (.binary .add (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) =
        .ok (.int (Int.ofNat (pending.toNat + high.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_pendingReturns evm bidder oldAddr value old pending hold
      holdAddr hpending,
    scratch_eval_placeBid_highestBid evm bidder value high hhigh,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((pending.toNat : Int) + (high.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  have hlt : ¬ ((2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int)) := by
    norm_num [UInt256.size] at hsum ⊢
    omega
  have hif :
      ¬ ((pending.toNat : Int) + (high.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hnonneg hneg
    · apply hlt
      norm_num at hge ⊢
      exact hge
  simp only [uint256Int]
  rw [if_neg hif]
  rfl
  all_goals decide

theorem scratch_eval_placeBid_pending_add_revert
    (evm : EVM.State) (bidder oldAddr : AccountAddress) (value old high pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hover : UInt256.size ≤ pending.toNat + high.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      (u256 (.binary .add (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) = .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [scratch_eval_placeBid_pendingReturns evm bidder oldAddr value old pending hold
      holdAddr hpending,
    scratch_eval_placeBid_highestBid evm bidder value high hhigh,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((pending.toNat : Int) + (high.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  have hge : (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int) := by
    norm_num [UInt256.size] at hover ⊢
    omega
  have hif :
      (pending.toNat : Int) + (high.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (pending.toNat : Int) + (high.toNat : Int) := by
    right
    norm_num at hge ⊢
    exact hge
  simp only [uint256Int]
  rw [if_pos hif]
  all_goals decide

theorem scratch_assign_placeBid_pendingReturns
    (evm : EVM.State) (bidder oldAddr : AccountAddress)
    (value old pending high : UInt256)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage (pendingReturnsRef (.storage highestBidderRef))
      (.int (Int.ofNat (pending.toNat + high.toNat))) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterPending evm oldAddr (UInt256.ofNat (pending.toNat + high.toNat))) := by
  unfold scratch_placeBidAfterPending
  have hsumToNat : (UInt256.ofNat (pending.toNat + high.toNat)).toNat =
      pending.toNat + high.toNat := UInt256.toNat_ofNat_of_lt hsum
  exact assignStorageRef_storage_scalar
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (pendingReturnsSlot (.address oldAddr)) (UInt256.ofNat (pending.toNat + high.toNat)))
    (slot := pendingReturnsRef (.storage highestBidderRef))
    (er := { base := "pendingReturns", steps := [.mindex (.address oldAddr)] })
    (ty := uint256St)
    (loc := blindAuctionUint256Loc (pendingReturnsSlot (.address oldAddr)))
    (n := Int.ofNat (pending.toNat + high.toNat))
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (scratch_evalStorageRef_placeBid_pendingReturns evm bidder oldAddr value old hold holdAddr)
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, pendingReturnsRef])
    (blindAuctionConfig_storage_pendingReturns (.address oldAddr))
    (by
      simpa [hsumToNat] using
        blindAuctionStorageLocStore_uint256_natCast evm
          (pendingReturnsSlot (.address oldAddr))
          (UInt256.ofNat (pending.toNat + high.toNat)))

theorem scratch_assign_placeBid_highestBid
    (evm : EVM.State) (bidder : AccountAddress) (value : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage highestBidRef (.int (Int.ofNat value.toNat)) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterHigh evm value) := by
  unfold scratch_placeBidAfterHigh
  exact assignStorageRef_storage_scalar
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ value)
    (slot := highestBidRef)
    (er := { base := "highestBid", steps := [] })
    (ty := uint256St)
    (loc := blindAuctionUint256Loc ⟨6⟩)
    (n := Int.ofNat value.toNat)
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidRef])
    blindAuctionConfig_storage_highestBid
    (blindAuctionStorageLocStore_uint256_natCast evm ⟨6⟩ value)

theorem scratch_assign_placeBid_highestBidder
    (evm : EVM.State) (bidder : AccountAddress) (value : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
      .storage highestBidderRef (.address bidder) =
    .ok ({ contract := blindAuctionContract, locals := scratch_placeBidStore bidder value },
      scratch_placeBidAfterBidder evm bidder) := by
  unfold scratch_placeBidAfterBidder
  have haddrOfNat : AccountAddress.ofNat (UInt256.ofNat bidder.val).toNat = bidder := by
    apply Fin.ext
    rw [UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le bidder.isLt (by decide : AccountAddress.size ≤ UInt256.size))]
    simp [AccountAddress.ofNat, Nat.mod_eq_of_lt bidder.isLt]
  have hstore :
      storageLocStore evm (blindAuctionAddrLoc ⟨5⟩) (.address bidder) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
          (SimpleAuction.simpleAuctionSetAddressWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            (UInt256.ofNat bidder.val))) := by
    simpa [haddrOfNat] using
      scratch_blindAuctionStorageLocStore_address_offset0 evm ⟨5⟩ (UInt256.ofNat bidder.val)
        (scratch_addressWord_canonical bidder)
  exact assignStorageRef_storage_scalar_value
    (cfg := blindAuctionConfig)
    (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm := evm)
    (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (SimpleAuction.simpleAuctionSetAddressWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) (UInt256.ofNat bidder.val)))
    (slot := highestBidderRef)
    (er := { base := "highestBidder", steps := [] })
    (ty := addrSt)
    (loc := blindAuctionAddrLoc ⟨5⟩)
    (value := .address bidder)
    (scratch_placeBidStore_base_none bidder value (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, blindAuctionContract, storageDecls, highestBidderRef, addrSt])
    blindAuctionConfig_storage_highestBidder
    (by trivial)
    hstore

theorem scratch_blindAuctionPlaceBidBodyReturns_false
    (evm : EVM.State) (bidder : AccountAddress) (value high : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hle : value.toNat ≤ high.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        evm (some [(.bool false)])) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  refine ExecBlock.consReturn ?_
  refine ExecStmt.iteTrue ?_ ?_
  · exact scratch_eval_placeBid_value_le_highestBid_true evm bidder value high hhigh hle
  · exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem scratch_blindAuctionPlaceBidBodyReturns_true_zero
    (evm : EVM.State) (bidder : AccountAddress) (value high old : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder)
        (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
    [ .ite (.binary .le (.var "value") (.storage highestBidRef))
        [ .return [(.boolLit false)] ] [],
      .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
        [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
            (u256 (.binary .add
              (.storage (pendingReturnsRef (.storage highestBidderRef)))
              (.storage highestBidRef))) ] [],
      .assign .storage highestBidRef (.var "value"),
      .assign .storage highestBidderRef (.var "bidder"),
      .return [(.boolLit true)] ]
    (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
      (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder)
      (some [(.bool true)]))
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_value_le_highestBid_false evm bidder value high hhigh hlt)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_highestBidder_ne_zero_false evm bidder value old hold hzero)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterHigh evm value) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_int evm (scratch_placeBidStore bidder value) "value"
        (Int.ofNat value.toNat) (scratch_placeBidStore_value bidder value))
      (scratch_assign_placeBid_highestBid evm bidder value)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) bidder) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_value (scratch_placeBidAfterHigh evm value)
        (scratch_placeBidStore bidder value) "bidder" (.address bidder)
        (scratch_placeBidStore_bidder bidder value))
      (scratch_assign_placeBid_highestBidder (scratch_placeBidAfterHigh evm value) bidder value)
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem scratch_blindAuctionPlaceBidBodyReturns_true_nonzero
    (evm : EVM.State) (bidder oldAddr : AccountAddress)
    (value high old pending : UInt256)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm
      (scratch_placeBidStore bidder value) placeBidFn.body
      (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
        (scratch_placeBidAfterBidder
          (scratch_placeBidAfterHigh
            (scratch_placeBidAfterPending evm oldAddr
              (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder)
        (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  unfold placeBidFn
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value } evm
    [ .ite (.binary .le (.var "value") (.storage highestBidRef))
        [ .return [(.boolLit false)] ] [],
      .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
        [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
            (u256 (.binary .add
              (.storage (pendingReturnsRef (.storage highestBidderRef)))
              (.storage highestBidRef))) ] [],
      .assign .storage highestBidRef (.var "value"),
      .assign .storage highestBidderRef (.var "bidder"),
      .return [(.boolLit true)] ]
    (.returned { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value }
      (scratch_placeBidAfterBidder
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder)
      (some [(.bool true)]))
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := evm) ?_ ?_
  · exact ExecStmt.iteFalse
      (scratch_eval_placeBid_value_le_highestBid_false evm bidder value high hhigh hlt)
      ExecBlock.nil
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterPending evm oldAddr
      (UInt256.ofNat (pending.toNat + high.toNat))) ?_ ?_
  · refine ExecStmt.iteTrue
      (scratch_eval_placeBid_highestBidder_ne_zero_true evm bidder value old hold hnonzero) ?_
    refine ExecBlock.consNormal
      (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
      (evm' := scratch_placeBidAfterPending evm oldAddr
        (UInt256.ofNat (pending.toNat + high.toNat))) ?_
      (ExecBlock.nil (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
        (evm := scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))))
    exact ExecStmt.assign
      (scratch_eval_placeBid_pending_add evm bidder oldAddr value old high pending hhigh hold
        holdAddr hpending hsum)
      (scratch_assign_placeBid_pendingReturns evm bidder oldAddr value old pending high hold
        holdAddr hsum)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterHigh
      (scratch_placeBidAfterPending evm oldAddr
        (UInt256.ofNat (pending.toNat + high.toNat))) value) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_int (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat)))
        (scratch_placeBidStore bidder value) "value" (Int.ofNat value.toNat)
        (scratch_placeBidStore_value bidder value))
      (scratch_assign_placeBid_highestBid
        (scratch_placeBidAfterPending evm oldAddr (UInt256.ofNat (pending.toNat + high.toNat)))
        bidder value)
  refine ExecBlock.consNormal
    (solm' := { contract := blindAuctionContract, locals := scratch_placeBidStore bidder value })
    (evm' := scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value) bidder) ?_ ?_
  · exact ExecStmt.assign
      (evalExpr_reveal_var_value
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value)
        (scratch_placeBidStore bidder value) "bidder" (.address bidder)
        (scratch_placeBidStore_bidder bidder value))
      (scratch_assign_placeBid_highestBidder
        (scratch_placeBidAfterHigh
          (scratch_placeBidAfterPending evm oldAddr
            (UInt256.ofNat (pending.toNat + high.toNat))) value)
        bidder value)
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

/-! ### Scratch placeBid EVM-side routine -/

def scratch_placeBidHighestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨6⟩ ⟨0⟩)

def scratch_placeBidHighestBidderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨5⟩ ⟨0⟩)

def scratch_placeBidStoreHighMap (σ : AccountMap) (I : ExecutionEnv) (value : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨6⟩ value

def scratch_placeBidStoreBidderMap (σ : AccountMap) (I : ExecutionEnv) (bidder : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨5⟩
    (SimpleAuction.simpleAuctionSetAddressWord
      (scratch_placeBidHighestBidderWord σ I) bidder)

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_false {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hle : value.toNat ≤ (scratch_placeBidHighestBidWord σ I).toNat)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨0⟩ :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨0⟩ := ugt_zero hle
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1544 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiNT (by decide)]
  have rd1655 := evm_run rd1544 with [pop, push0, push2 ⟨1654⟩,
    jump (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

theorem scratch_blindAuctionCheckedAddNoOverflowGt (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (b + a) = ⟨0⟩ := by
  have hsum : (b + a).toNat = b.toNat + a.toNat := by
    rw [uadd_toNat]
    have hfit' : b.toNat + a.toNat < UInt256.size := by omega
    exact Nat.mod_eq_of_lt hfit'
  have hle : a.toNat ≤ (b + a).toNat := by
    rw [hsum]
    omega
  exact ugt_zero hle

theorem scratch_blindAuctionCheckedAddOverflowGt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (b + a) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ b.toNat + a.toNat := by omega
  have hsum_lt2 : b.toNat + a.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (b.toNat + a.toNat) % UInt256.size =
      b.toNat + a.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : (b + a).toNat = b.toNat + a.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (a > b + a)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show a.toNat > (b + a).toNat
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2045⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret ((b + a) :: R)
      mem aw rdata acc k' C' := by
  have hgt := scratch_blindAuctionCheckedAddNoOverflowGt a b hfit
  have rd2052₀ := evm_run rd with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd2052 := rd2052₀
  rw [hgt] at rd2052
  have rd2056 := evm_run rd2052 with [iszero, push2 ⟨1654⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd2056 with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

theorem scratch_blindAuctionCheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2064⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata acc k' C' := by
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd2071₀ := evm_run rd with [jumpdest, dup2, dup2, sub, dup2, dup2, gt]
  have rd2071 := rd2071₀
  rw [hgt] at rd2071
  have rd2072₀ := evm_run rd2071 with [iszero]
  have rd2072 := rd2072₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2072
  have rd1654 := evm_run rd2072 with [push2 ⟨1654⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd1654 with [jumpdest, swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_refundAdd_toPlaceCond {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret fake value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1247⟩
      [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hfit : refund.toNat + deposit.toNat < UInt256.size) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, fake, value, slot, i, deposit + refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1252₀ := evm_run rd with [jumpdest, push1 ⟨1⟩, dup5, add]
  obtain ⟨_, _, rd1253₀⟩ := rd1252₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1253⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1253⟩
      [deposit, secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [hdeposit] using rd1253₀⟩
  have rd2045 := evm_run rd1253 with [push2 ⟨1262⟩, swap1, dup8, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1262⟩ :=
    scratch_blindAuctionCheckedAddOk
      (a := refund) (b := deposit) (ret := ⟨1262⟩)
      (R := [secret, fake, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd2045 hfit (by jump_dest) (by simp)
  have rd1265 := evm_run rd1262 with [jumpdest, swap6, pop]
  exact ⟨_, _, by simpa using rd1265⟩

theorem scratch_blindAuctionRevealX_placeCond_fake_toZero {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1283 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd1283 with [iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_depositLt_toZero {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hlt : deposit.toNat < value.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1315⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1273 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiNT (by decide), pop, dup3, dup5, push1 ⟨1⟩, add]
  obtain ⟨_, _, rd1280₀⟩ := rd1273.sload (by decide) (by evm_ov)
  have hdeposit' :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (⟨1⟩ + slot) ⟨0⟩) = deposit := by
    simpa [u256_add_comm] using hdeposit
  have hltw : UInt256.lt deposit value = ⟨1⟩ := ult_one hlt
  have rd1281₀ := evm_run rd1280₀ with [lt]
  have rd1281 := rd1281₀
  rw [hdeposit', hltw] at rd1281
  have rd1283 := evm_run rd1281 with [iszero, jumpdest]
  exact ⟨_, _, evm_run rd1283 with [iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_place_toRoutine {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hge : value.toNat ≤ deposit.toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1534⟩
      [value, UInt256.ofNat I.source.val, ⟨1297⟩, secret, ⟨0⟩, value, slot, i, refund,
        len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1273 := evm_run rd with [dup2, iszero, dup1, iszero, push2 ⟨1282⟩,
    jumpiNT (by decide), pop, dup3, dup5, push1 ⟨1⟩, add]
  obtain ⟨_, _, rd1280₀⟩ := rd1273.sload (by decide) (by evm_ov)
  have hdeposit' :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (⟨1⟩ + slot) ⟨0⟩) = deposit := by
    simpa [u256_add_comm] using hdeposit
  have hltw : UInt256.lt deposit value = ⟨0⟩ := ult_zero hge
  have rd1281₀ := evm_run rd1280₀ with [lt]
  have rd1281 := rd1281₀
  rw [hdeposit', hltw] at rd1281
  have rd1288 := evm_run rd1281 with [iszero, jumpdest, iszero, push2 ⟨1315⟩,
    jumpiNT (by decide)]
  exact ⟨_, _, evm_run rd1288 with [push2 ⟨1297⟩, caller, dup5, push2 ⟨1534⟩,
    jump (by jump_dest)]⟩

theorem scratch_blindAuctionRevealX_placeCond_fake_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨1⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1315⟩ := scratch_blindAuctionRevealX_placeCond_fake_toZero rd
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeCond_depositLt_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hlt : deposit.toNat < value.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1315⟩ :=
    scratch_blindAuctionRevealX_placeCond_depositLt_toZero rd hdeposit hlt
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeBidFalse_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1297⟩
      [⟨0⟩, secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1315 := evm_run rd with [jumpdest, iszero, push2 ⟨1315⟩,
    jumpiT one_ne_zero_uint (by jump_dest)]
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_blindAuctionRevealX_placeBidTrue_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1297⟩
      [⟨1⟩, secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  have rd1303 := evm_run rd with [jumpdest, iszero, push2 ⟨1315⟩, jumpiNT (by decide)]
  have rd2064 := evm_run rd1303 with [push2 ⟨1312⟩, dup4, dup8, push2 ⟨2064⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1312⟩ :=
    scratch_blindAuctionCheckedSubOk
      (a := refund) (b := value) (ret := ⟨1312⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd2064 hrefund (by jump_dest) (by simp)
  have rd1315 := evm_run rd1312 with [jumpdest, swap6, pop]
  exact scratch_blindAuctionRevealX_zeroBlinded_toNext rd1315 hperm

theorem scratch_placeBidPackedBidderWord_eq_setAddress (old bidder : UInt256)
    (hcanon : bidder.toNat < EVM.addressModulus) :
    UInt256.lor (UInt256.land bidder solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      SimpleAuction.simpleAuctionSetAddressWord old bidder := by
  unfold SimpleAuction.simpleAuctionSetAddressWord
  rw [Reasoning.Theory.u256_land_comm (UInt256.lnot solcAddrMask) old]
  rw [solcAddrMask_clean hcanon]
  exact u256_lor_comm bidder (UInt256.land old (UInt256.lnot solcAddrMask))

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_zero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask = ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      mem aw rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap σ I value) I bidder) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have rd1564 := rd1564₀
  have hzero' :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) = ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) = ⟨0⟩
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hzero
  rw [hzero'] at rd1564
  have rd1619 := evm_run rd1564 with [
    iszero, push2 ⟨1618⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest, pop,
    push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R) mem aw rdata
      (cA, scratch_placeBidStoreHighMap σ I value) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreHighMap] using rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, scratch_placeBidStoreHighMap σ I value) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.or rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap σ I value) I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R) mem aw rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap σ I value) I bidder) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

noncomputable def scratch_placeBidPendingKeyMem (mem : ByteArray) (key : UInt256) : ByteArray :=
  (UInt256.toByteArray key).write 0 mem 0 32

noncomputable def scratch_placeBidPendingHashMem (mem : ByteArray) (key : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0
    (scratch_placeBidPendingKeyMem mem key) 32 32

theorem scratch_placeBidPendingKeyMem_size (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingKeyMem mem key).size = 96 := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  norm_num

theorem scratch_placeBidPendingHashMem_size (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingHashMem mem key).size = 96 := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    scratch_placeBidPendingKeyMem_size mem key hmem, toByteArray_size]
  norm_num

theorem scratch_placeBidPendingKeyMem_read0 (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingKeyMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  rw [show (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key from by
    apply ByteArray.ext
    rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
    show (UInt256.toByteArray key).data.size ≤ 32
    rw [show (UInt256.toByteArray key).data.size = (UInt256.toByteArray key).size from rfl,
      toByteArray_size]]

set_option maxHeartbeats 1000000 in
theorem scratch_placeBidPendingHashMem_read0_64 (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [scratch_placeBidPendingHashMem_size mem key hmem]; norm_num)]
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
    (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega)]
  let M := scratch_placeBidPendingKeyMem mem key
  let S := UInt256.toByteArray (⟨7⟩ : UInt256)
  change (M.extract 0 32 ++ S.extract 0 32 ++ M.extract (32 + 32) M.size).extract
        0 (0 + 64) =
      UInt256.toByteArray key ++ S
  rw [show 0 + 64 = 64 by norm_num]
  rw [byteArray_extract_two_chunks_0]
  · have hM0 : M.extract 0 32 = UInt256.toByteArray key := by
      dsimp [M]
      rw [← readWithPadding_eq_extract (scratch_placeBidPendingKeyMem mem key) 0
        (by rw [scratch_placeBidPendingKeyMem_size mem key hmem]; omega)]
      exact scratch_placeBidPendingKeyMem_read0 mem key hmem
    have hSself : S.extract 0 32 = S := by
      dsimp [S]
      rw [show 32 = (UInt256.toByteArray (⟨7⟩ : UInt256)).size by rw [toByteArray_size]]
      exact byteArray_extract_self _
    rw [hM0, hSself]
  · rw [ByteArray.size_extract]
    dsimp [M]
    rw [scratch_placeBidPendingKeyMem_size mem key hmem]
    norm_num
  · rw [ByteArray.size_extract]
    dsimp [S]
    rw [toByteArray_size]
    norm_num

theorem scratch_placeBidPendingKeyMem_size_ge32 (mem : ByteArray) (key : UInt256) :
    32 ≤ (scratch_placeBidPendingKeyMem mem key).size := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem scratch_placeBidPendingHashMem_size_ge64 (mem : ByteArray) (key : UInt256) :
    64 ≤ (scratch_placeBidPendingHashMem mem key).size := by
  have hkeySize : 32 ≤ (scratch_placeBidPendingKeyMem mem key).size :=
    scratch_placeBidPendingKeyMem_size_ge32 mem key
  unfold scratch_placeBidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      hkeySize,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem scratch_placeBidPendingKeyMem_read0_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingKeyMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingKeyMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem scratch_placeBidPendingHashMem_read0_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (scratch_placeBidPendingKeyMem_size_ge32 mem key) (by omega)]
  exact scratch_placeBidPendingKeyMem_read0_any mem key

theorem scratch_placeBidPendingHashMem_read32_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 32 32 =
      UInt256.toByteArray (⟨7⟩ : UInt256) := by
  unfold scratch_placeBidPendingHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (scratch_placeBidPendingKeyMem_size_ge32 mem key)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨7⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem scratch_placeBidPendingHashMem_read0_64_any (mem : ByteArray) (key : UInt256) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray (⟨7⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (scratch_placeBidPendingHashMem_size_ge64 mem key)]
  have hleft :
      (scratch_placeBidPendingHashMem mem key).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        exact le_trans (by norm_num : 32 ≤ 64)
          (scratch_placeBidPendingHashMem_size_ge64 mem key)),
      scratch_placeBidPendingHashMem_read0_any]
  have hright :
      (scratch_placeBidPendingHashMem mem key).extract 32 64 =
        UInt256.toByteArray (⟨7⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32 (scratch_placeBidPendingHashMem_size_ge64 mem key),
      scratch_placeBidPendingHashMem_read32_any]
  rw [show (scratch_placeBidPendingHashMem mem key).extract 0 64 =
      (scratch_placeBidPendingHashMem mem key).extract 0 32 ++
        (scratch_placeBidPendingHashMem mem key).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem scratch_placeBidPendingKeccak (mem : ByteArray) (key : UInt256)
    (hmem : mem.size = 96) (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((scratch_placeBidPendingHashMem mem key).readWithPadding 0 64))) =
      pendingReturnsSlot (.address (AccountAddress.ofNat key.toNat)) := by
  rw [scratch_placeBidPendingHashMem_read0_64 mem key hmem]
  unfold pendingReturnsSlot blindAuctionMappingSlot
  have hkey : keyValueToWord (.address (AccountAddress.ofNat key.toNat)) = key := by
    apply u256_inj
    unfold keyValueToWord AccountAddress.ofNat
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hkey]
  exact mappingSlot_single key ⟨7⟩

theorem scratch_placeBidPendingKeccak_any (mem : ByteArray) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((scratch_placeBidPendingHashMem mem key).readWithPadding 0 64))) =
      pendingReturnsSlot (.address (AccountAddress.ofNat key.toNat)) := by
  rw [scratch_placeBidPendingHashMem_read0_64_any mem key]
  unfold pendingReturnsSlot blindAuctionMappingSlot
  have hkey : keyValueToWord (.address (AccountAddress.ofNat key.toNat)) = key := by
    apply u256_inj
    unfold keyValueToWord AccountAddress.ofNat
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  rw [hkey]
  exact mappingSlot_single key ⟨7⟩

def scratch_placeBidPendingSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  pendingReturnsSlot
    (.address (AccountAddress.ofNat
      (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask).toNat))

def scratch_placeBidPendingWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (scratch_placeBidPendingSlot σ I) ⟨0⟩)

def scratch_placeBidStorePendingMap (σ : AccountMap) (I : ExecutionEnv) (sum : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (scratch_placeBidPendingSlot σ I) sum

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_nonzero {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hnonzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder) k' C' := by
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hmaskNonzero :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hnonzero
  have rd1564 := rd1564₀
  have rd1565₀ := evm_run rd1564 with [iszero]
  have rd1565 := rd1565₀
  rw [isZero_eq_zero_of_ne hmaskNonzero] at rd1565
  have rd1571 := evm_run rd1565 with [push2 ⟨1618⟩, jumpiNT (by decide), push1 ⟨6⟩]
  obtain ⟨_, _, rd1572₀⟩ := rd1571.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1572⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1572⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1572₀⟩
  have rd1574 := evm_run rd1572 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd1575₀⟩ := rd1574.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1575⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1575⟩
      (scratch_placeBidHighestBidderWord σ I :: scratch_placeBidHighestBidWord σ I ::
        ⟨0⟩ :: value :: bidder :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1575₀⟩
  have rd1587₀ := evm_run rd1575 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have hmask :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) =
        UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) =
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
    exact Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
  have rd1587 := rd1587₀
  rw [hmask] at rd1587
  have rd1588 := evm_run rd1587 with [
    raw mstore 0
      (scratch_placeBidPendingKeyMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1593 := evm_run rd1588 with [
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore 0
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        change (UInt256.toByteArray (⟨7⟩ : UInt256)).write 0
            (scratch_placeBidPendingKeyMem mem
              (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask)) 32 32 =
          scratch_placeBidPendingHashMem mem
            (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask)
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have hkeyCanon := solcAddrMask_result_canonical
    (scratch_placeBidHighestBidderWord σ I)
  have hslot := scratch_placeBidPendingKeccak mem
    (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask) hmem hkeyCanon
  have rd1597 := evm_run rd1593 with [
    raw keccak256 0 (scratch_placeBidPendingSlot σ I) (UInt256.ofNat 3) (by decide)
      mem_cost (by simpa [scratch_placeBidPendingSlot] using hslot) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1598₀⟩ := rd1597.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1599⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1599⟩
      (scratch_placeBidPendingWord σ I :: scratch_placeBidPendingSlot σ I ::
        ⟨0⟩ :: scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidPendingWord, scratch_placeBidPendingSlot] using rd1598₀⟩
  have rd1611 := evm_run rd1599 with [
    swap1, swap2, swap1, push2 ⟨1612⟩, swap1, dup5, swap1, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1612₀⟩ :=
    scratch_blindAuctionCheckedAddOk rd1611 hsum (by jump_dest) (by evm_ov)
  have rd1615 := evm_run rd1612₀ with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1616₀⟩ := rd1615.sstore hperm (by decide) (by evm_ov)
  have rd1619 := evm_run rd1616₀ with [
    pop, pop, jumpdest, pop, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by
      simpa [scratch_placeBidStoreHighMap, scratch_placeBidStorePendingMap] using rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.or rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R)
      (scratch_placeBidPendingHashMem mem
        (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
      (UInt256.ofNat 3) rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨_, _, evm_run rd1655 with [swap3, swap2, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem scratch_RD_placeBid_true_nonzero_anyMem {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat} {value bidder ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode I g s0 ⟨1534⟩ (value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hlt : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hnonzero : UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hbidderCanon : bidder.toNat < EVM.addressModulus)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C',
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
      RD blindAuctionBytecode I g s0 ret (⟨1⟩ :: R)
        (scratch_placeBidPendingHashMem mem
          (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
        aw3 rdata
        (cA, scratch_placeBidStoreBidderMap
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
          bidder) k' C' := by
  let key := UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
  let memKey := scratch_placeBidPendingKeyMem mem key
  let memHash := scratch_placeBidPendingHashMem mem key
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
  have rd1538 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1539₀⟩ := rd1538.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1539⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1539⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1539₀⟩
  have hgt : UInt256.gt value (scratch_placeBidHighestBidWord σ I) = ⟨1⟩ := ugt_one hlt
  have rd1540₀ := evm_run rd1539 with [dup3, gt]
  have rd1540 := rd1540₀
  rw [hgt] at rd1540
  have rd1554 := evm_run rd1540 with [push2 ⟨1551⟩, jumpiT one_ne_zero_uint (by jump_dest),
    jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd1555₀⟩ := rd1554.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1555⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1555⟩
      (scratch_placeBidHighestBidderWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1555₀⟩
  have rd1564₀ := evm_run rd1555 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hmaskNonzero :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩ := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) ≠ ⟨0⟩
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)]
    exact hnonzero
  have rd1564 := rd1564₀
  have rd1565₀ := evm_run rd1564 with [iszero]
  have rd1565 := rd1565₀
  rw [isZero_eq_zero_of_ne hmaskNonzero] at rd1565
  have rd1571 := evm_run rd1565 with [push2 ⟨1618⟩, jumpiNT (by decide), push1 ⟨6⟩]
  obtain ⟨_, _, rd1572₀⟩ := rd1571.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1572⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1572⟩
      (scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidWord] using rd1572₀⟩
  have rd1574 := evm_run rd1572 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd1575₀⟩ := rd1574.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1575⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1575⟩
      (scratch_placeBidHighestBidderWord σ I :: scratch_placeBidHighestBidWord σ I ::
        ⟨0⟩ :: value :: bidder :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord] using rd1575₀⟩
  have rd1587₀ := evm_run rd1575 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have hmask :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
        (scratch_placeBidHighestBidderWord σ I) =
        UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask := by
    change UInt256.land solcAddrMask (scratch_placeBidHighestBidderWord σ I) =
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
    exact Reasoning.Theory.u256_land_comm solcAddrMask (scratch_placeBidHighestBidderWord σ I)
  have rd1587 := rd1587₀
  rw [hmask] at rd1587
  have rd1588 := evm_run rd1587 with [
    raw mstore (Cₘ aw1 - Cₘ aw) memKey aw1 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw1])
      (by simp [memKey, scratch_placeBidPendingKeyMem, key])
      (by rfl) (by evm_ov)]
  have rd1593 := evm_run rd1588 with [
    push1 ⟨7⟩, push1 ⟨32⟩,
    raw mstore (Cₘ aw2 - Cₘ aw1) memHash aw2 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw2])
      (by
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        simp [memHash, scratch_placeBidPendingHashMem, memKey])
      (by rfl) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have hkeyCanon := solcAddrMask_result_canonical
    (scratch_placeBidHighestBidderWord σ I)
  have hslot := scratch_placeBidPendingKeccak_any mem key hkeyCanon
  have rd1597 := evm_run rd1593 with [
    raw keccak256 (Cₘ aw3 - Cₘ aw2) (scratch_placeBidPendingSlot σ I) aw3 (by decide)
      (fun s haws hstks => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw3,
          show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
      (by simpa [memHash, key, scratch_placeBidPendingSlot] using hslot) (by rfl) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1598₀⟩ := rd1597.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1599⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1599⟩
      (scratch_placeBidPendingWord σ I :: scratch_placeBidPendingSlot σ I ::
        ⟨0⟩ :: scratch_placeBidHighestBidWord σ I :: ⟨0⟩ :: value :: bidder :: ret :: R)
      memHash aw3 rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidPendingWord, scratch_placeBidPendingSlot,
      memHash] using rd1598₀⟩
  have rd1611 := evm_run rd1599 with [
    swap1, swap2, swap1, push2 ⟨1612⟩, swap1, dup5, swap1, push2 ⟨2045⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1612₀⟩ :=
    scratch_blindAuctionCheckedAddOk rd1611 hsum (by jump_dest) (by evm_ov)
  have rd1615 := evm_run rd1612₀ with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd1616₀⟩ := rd1615.sstore hperm (by decide) (by evm_ov)
  have rd1619 := evm_run rd1616₀ with [
    pop, pop, jumpdest, pop, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1625₀⟩ := rd1619.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1625⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1625⟩
      (value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by
      simpa [scratch_placeBidStoreHighMap, scratch_placeBidStorePendingMap, memHash] using
        rd1625₀⟩
  have rd1628 := evm_run rd1625 with [push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd1629₀⟩ := rd1628.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1629⟩
      (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I ::
        ⟨5⟩ :: value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreHighMap
        (scratch_placeBidStorePendingMap σ I
          (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidHighestBidderWord, memHash] using rd1629₀⟩
  have rd1649 := evm_run rd1629 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  have rd1650 := RD.or rd1649 (by decide) (by evm_ov)
  have hpack :
      UInt256.lor
          (UInt256.land bidder (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
          (UInt256.land (UInt256.lnot (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩))
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)
          ) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder :=
    by
      change UInt256.lor (UInt256.land bidder solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (scratch_placeBidHighestBidderWord
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
                I value)
              I)) =
        SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I))
              I value)
            I)
          bidder
      exact scratch_placeBidPackedBidderWord_eq_setAddress
        (scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap σ I
              (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
          I)
        bidder hbidderCanon
  have rd1650' := rd1650
  rw [hpack] at rd1650'
  have rd1651 := evm_run rd1650' with [swap1]
  obtain ⟨_, _, rd1652₀⟩ := rd1651.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd1652⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1652⟩
      (value :: bidder :: ret :: R)
      memHash aw3 rdata
      (cA, scratch_placeBidStoreBidderMap
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap σ I
            (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value) I
        bidder)
      k' C' := by
    exact ⟨_, _, by simpa [scratch_placeBidStoreBidderMap, memHash] using rd1652₀⟩
  have rd1655 := evm_run rd1652 with [push1 ⟨1⟩, jumpdest]
  exact ⟨_, _, by simpa [aw1, aw2, aw3, memHash] using
    (evm_run rd1655 with [swap3, swap2, pop, pop, jump hret])⟩

theorem scratch_revealSourceWord_canonical (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt

theorem scratch_blindAuctionRevealX_placeCond_placeBid_false_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ (scratch_placeBidHighestBidWord σ I).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_false
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hplaceFalse (by jump_dest) (by simp)
  exact scratch_blindAuctionRevealX_placeBidFalse_toNext rd1297 hperm

theorem scratch_blindAuctionRevealX_placeCond_placeBid_true_zero_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceTrue : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderZero :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask = ⟨0⟩)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
        biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap σ I value) I
          (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_true_zero
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hperm hplaceTrue hhighestBidderZero (scratch_revealSourceWord_canonical I)
      (by jump_dest) (by simp)
  exact scratch_blindAuctionRevealX_placeBidTrue_toNext rd1297 hrefund hperm

theorem scratch_blindAuctionRevealX_placeCond_placeBid_true_nonzero_toNext {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {secret value slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen
      fakesEnd valuesLen valuesEnd sel deposit : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1265⟩
      [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hdeposit :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceTrue : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderNonzero :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hsum :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size)
    (hrefund : value.toNat ≤ refund.toNat)
    (hperm : I.perm = true) :
    ∃ k' C',
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) (UInt256.sub refund value) len revealEnd
          biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (scratch_placeBidPendingHashMem mem
          (UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask))
        aw3 rdata
        (cA, sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap σ I
                (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
            I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd1534⟩ :=
    scratch_blindAuctionRevealX_placeCond_place_toRoutine rd hdeposit hdepositGe
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨0⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (⟨32⟩ : UInt256).toNat 32)
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨0⟩ : UInt256).toNat 64)
  obtain ⟨_, _, rd1297⟩ :=
    scratch_RD_placeBid_true_nonzero_anyMem
      (value := value) (bidder := UInt256.ofNat I.source.val) (ret := ⟨1297⟩)
      (R := [secret, ⟨0⟩, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd1534 hperm hplaceTrue hhighestBidderNonzero (scratch_revealSourceWord_canonical I)
      hsum (by jump_dest) (by simp)
  obtain ⟨k', C', rd1014⟩ := scratch_blindAuctionRevealX_placeBidTrue_toNext rd1297 hrefund hperm
  exact ⟨k', C', by simpa [aw1, aw2, aw3] using rd1014⟩

/-! ### Scratch reveal nonempty loop source-side scaffolding -/


end BlindAuction
