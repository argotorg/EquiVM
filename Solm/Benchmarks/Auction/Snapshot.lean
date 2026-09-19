import Solm.Benchmarks.Auction.Storage
import Solm.Benchmarks.Auction.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- The auction's five storage words, with bidder and settled sharing the last word. -/
structure Snapshot where
  nounId : UInt256
  amount : UInt256
  startTime : UInt256
  endTime : UInt256
  packed : UInt256

def snapshotOf (σ : AccountMap) (I : ExecutionEnv) : Snapshot :=
  ⟨storedWord σ I ⟨207⟩, storedWord σ I ⟨208⟩, storedWord σ I ⟨209⟩,
    storedWord σ I ⟨210⟩, storedWord σ I ⟨211⟩⟩

def snapshotOfState (evm : EVM.State) : Snapshot :=
  ⟨Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩,
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩,
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩,
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩,
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩⟩

theorem snapshotOf_equiv {σ₁ σ₂ : AccountMap} (h : accountMapEquiv σ₁ σ₂)
    (I : ExecutionEnv) : snapshotOf σ₁ I = snapshotOf σ₂ I := by
  simp only [snapshotOf, storedWord_equiv h]

def Snapshot.bidderWord (s : Snapshot) : UInt256 := UInt256.land s.packed solcAddrMask
def Snapshot.settledSourceWord (s : Snapshot) : UInt256 := UInt256.div s.packed ⟨2 ^ 160⟩
def Snapshot.settledByte (s : Snapshot) : UInt256 := UInt256.land s.settledSourceWord ⟨255⟩
def Snapshot.settledWord (s : Snapshot) : UInt256 :=
  UInt256.isZero (UInt256.isZero s.settledByte)

def Snapshot.values (s : Snapshot) : List Value :=
  [.int (Int.ofNat s.nounId.toNat), .int (Int.ofNat s.amount.toNat),
    .int (Int.ofNat s.startTime.toNat), .int (Int.ofNat s.endTime.toNat),
    .address (AccountAddress.ofNat s.bidderWord.toNat), wordToElem .bool s.settledByte]

def Snapshot.words (s : Snapshot) : List UInt256 :=
  [s.nounId, s.amount, s.startTime, s.endTime, s.bidderWord, s.settledWord]

theorem snapshotReturnEncoding (s : Snapshot) :
    encodeReturnValues? auctionGetter.returnType s.values = some (wordBytes s.words) := by
  have hu (w : UInt256) :
      encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) = some (EVM.Word.toBytesBE w) :=
    scalarValueEncoding (by native_decide) rfl (uint256ReturnEncoding w)
  have ha : encodeABIValue? addr (.address (AccountAddress.ofNat s.bidderWord.toNat)) =
      some (EVM.Word.toBytesBE s.bidderWord) :=
    scalarValueEncoding (by native_decide) rfl
      (solcAddressReturnEncoding (addrTy := addr) rfl s.packed)
  have hb : encodeABIValue? boolTy (wordToElem .bool s.settledByte) =
      some (EVM.Word.toBytesBE s.settledWord) :=
    scalarValueEncoding (by native_decide) rfl (boolWordReturnEncoding s.settledSourceWord)
  have hhead : abiTupleHeadSize? [uint256, uint256, uint256, uint256, addr, boolTy] =
      some 192 := by native_decide
  rw [wordBytes_eq_list]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, Snapshot.values, Snapshot.words,
    show auctionGetter.returnType = [uint256, uint256, uint256, uint256, addr, boolTy] from rfl,
    encodeABIValuesFrom?, hu, ha, hb, show isDynamicABIType uint256 = false from rfl,
    show isDynamicABIType addr = false from rfl, show isDynamicABIType boolTy = false from rfl,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_assoc]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

end Auction
