import Solm.Benchmarks.Auction.InitializerStorage
import Solm.Benchmarks.Auction.CallState
import Solm.Benchmarks.Auction.SettleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def settledStoreWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨160⟩)))
    (UInt256.shiftLeft ⟨1⟩ ⟨160⟩)

theorem settledStoreWord_toNat (old : UInt256) :
    (settledStoreWord old).toNat =
      old.toNat % 2 ^ 160 + 2 ^ 160 + old.toNat / 2 ^ 168 * 2 ^ 168 := by
  have hm : (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨160⟩)).toNat =
      (2 ^ 160 - 1) ||| (2 ^ 256 - 2 ^ 168) := by native_decide
  have hp : (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩).toNat = 2 ^ 160 := by native_decide
  rw [settledStoreWord, lor_toNat, uland_toNat, hm, hp, Nat.and_or_distrib_left]
  change Nat.lor (Nat.lor (Nat.land old.toNat (2 ^ 160 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 168))) (2 ^ 160) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 168 (by decide) old.val.isLt]
  rw [show Nat.lor (Nat.lor (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 168 * 2 ^ 168))
      (2 ^ 160) = Nat.lor (Nat.lor (old.toNat % 2 ^ 160) (2 ^ 160))
        (old.toNat / 2 ^ 168 * 2 ^ 168) from Nat.or_right_comm _ _ _]
  have hlo : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by decide)
  have hbit : Nat.lor (old.toNat % 2 ^ 160) (2 ^ 160) = old.toNat % 2 ^ 160 + 2 ^ 160 := by
    simpa only [Nat.one_mul] using nat_lor_shift_add _ 1 160 hlo
  rw [hbit]
  exact nat_lor_shift_add _ _ 168 (by omega)

-- GENERALIZES Reasoning.Theory.storageLocStore_bool_true_offset0 to the Auction flag at byte 20.
theorem storageLocStore_settled (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (auctionBoolLocAt slot 20) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (settledStoreWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord auctionBoolLocAt
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof true.toUInt256).1.take 1 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 21) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, settledStoreWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof true.toUInt256).2]
  change _ % 2 ^ 160 + 2 ^ 160 * 1 + 2 ^ 168 * (_ / 2 ^ 168) = _
  omega

def settledState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (settledStoreWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))

def settledAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨211⟩ (settledStoreWord (storedWord σ I ⟨211⟩))

theorem settleStoreSource {evm locals} (ha : locals.get? "auction" = none) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage (aField "settled") (.boolLit true))
      (.ok { contract := auctionContract, locals := locals } (settledState evm)) := by
  apply ExecStmt.assign (value := .bool true) (by simp only [evalExpr?, pure])
  apply assignStorageRef_storage_scalar_value
    (er := { base := "auction", steps := [.field "settled"] })
    (ty := .elem .bool) (loc := auctionBoolLocAt ⟨211⟩ 20) ha
  · simp [aField, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      pure, bind, EvalResult.bind]
  · change storageTypeAt? auctionContract.storage
      { base := "auction", steps := [.field "settled"] } = some (.elem .bool)
    native_decide
  · rfl
  · trivial
  · exact storageLocStore_settled evm ⟨211⟩

-- LIBRARY CANDIDATE: transport the source/RD relation across a storage write.
theorem SourceState.storageWrite {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    (slot value : UInt256) :
    SourceState s0 I cA (sstoreAccountMap I.codeOwner σ slot value)
      (Solm.EVM.storageStore evm I.codeOwner slot value) := by
  refine ⟨?_, (storageStore_executionEnv _ _ _ _).trans hs.env,
    (storageStore_createdAccounts _ _ _ _).trans hs.created, ?_⟩
  · unfold Solm.EVM.storageStore
    cases evm.lookupAccount I.codeOwner <;> exact hs.world
  · rw [storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap _ _ _ hs.accounts

-- LIBRARY CANDIDATE: transport a read-modify-write through the source/RD relation.
theorem SourceState.readModifyWrite {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    (slot : UInt256) (f : UInt256 → UInt256) :
    SourceState s0 I cA (sstoreAccountMap I.codeOwner σ slot (f (storedWord σ I slot)))
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (f (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  rw [hs.storageRead, hs.env]
  exact hs.storageWrite _ _

theorem SourceState.settled {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    SourceState s0 I cA (settledAccounts σ I) (settledState evm) := by
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ =
      storedWord σ I ⟨211⟩ := by
    exact hs.storageRead _
  unfold settledState settledAccounts
  rw [hw, hs.env]
  exact hs.storageWrite _ _

end Auction
