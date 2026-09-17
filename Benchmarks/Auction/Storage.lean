import Benchmarks.Auction.ValueGuard
import Benchmarks.Auction.Returns
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def storedWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

theorem storedWord_equiv {σ₁ σ₂ : AccountMap} (h : accountMapEquiv σ₁ σ₂)
    (I : ExecutionEnv) (slot : UInt256) : storedWord σ₁ I slot = storedWord σ₂ I slot :=
  accountMapEquiv_storage_findD h I.codeOwner slot ⟨0⟩

theorem scalarRead (evm : EVM.State) (locals : Store) (name : Ident)
    (ty : ABI.ElemType) (loc : StorageLoc)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? auctionContract.storage { base := name } = some (.elem ty))
    (hloc : auctionConfig.storage.layout { base := name } = fun _ => some loc) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage { base := name }) = .ok (storageLocLoad evm loc) := by
  apply evalExpr_storage_scalar hbase _ hty hloc
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem loadUint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionUint256Loc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) :=
  storageLocLoad_uint256 evm slot

theorem auctionFieldRead (evm : EVM.State) (locals : Store) (name : Ident)
    (ty : ABI.ElemType) (loc : StorageLoc)
    (hbase : locals.get? "auction" = none)
    (hty : storageTypeAt? auctionContract.storage
      { base := "auction", steps := [.field name] } = some (.elem ty))
    (hloc : auctionConfig.storage.layout
      { base := "auction", steps := [.field name] } = fun _ => some loc) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage (aField name)) = .ok (storageLocLoad evm loc) := by
  apply evalExpr_storage_scalar hbase _ hty hloc
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField,
    EvalResult.bind, pure, bind]

theorem loadAddress (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionAddrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) :=
  storageLocLoad_address_offset0 evm slot

theorem loadUint8 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionUint8LocAt slot 0) =
      .int (Int.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).toNat) :=
  storageLocLoad_uint_offset0 evm slot 1 ⟨8, by decide⟩ (by decide)

theorem loadBool (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (auctionBoolLoc slot) =
      wordToElem .bool
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) :=
  storageLocLoad_bool_offset0 evm slot

theorem loadBoolAt (evm : EVM.State) (slot : UInt256) (offset : Fin 32) :
    storageLocLoad evm (auctionBoolLocAt slot offset) =
      wordToElem .bool
        (UInt256.land (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val))) ⟨255⟩) := by
  unfold storageLocLoad auctionBoolLocAt
  apply congrArg (wordToElem .bool)
  apply u256_inj
  change fromBytes' (((EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract
      offset.val (offset.val + 1)) = _
  rw [List.extract_eq_take_drop]
  simpa only [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val 1
      (by have := offset.isLt; omega) (by decide)

theorem maskTwice (w mask : UInt256) :
    UInt256.land (UInt256.land w mask) mask = UInt256.land w mask := by
  apply u256_inj
  simp only [uland_toNat, Nat.and_assoc, Nat.and_self]

theorem lowByte_bound (w : UInt256) : (UInt256.land w ⟨255⟩).toNat < EVM.twoPow 8 := by
  rw [uland_toNat]
  have h : w.toNat &&& (⟨255⟩ : UInt256).toNat ≤ (⟨255⟩ : UInt256).toNat := Nat.and_le_right
  change w.toNat &&& 255 < 256
  change w.toNat &&& 255 ≤ 255 at h
  omega

end Auction
