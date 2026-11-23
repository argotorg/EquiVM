import EVM.Types
import EVM.Lemmas
import Stele.Value
import Stele.Result

-- TODO: get rid of these maybe
import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Wheels

namespace Stele

open ABI

namespace EVM

/-
 - Storage access definitions and helpers.
 -
 - This file defines **raw storage slot access functions**,
 - **packed load/store** of values at a given storage location,
 - and a **storage layout** abstraction for higher-level storage access.
 -/

-- The two following functions implement storage access
-- However their semantics are not equivalent to actual evm semantics,
-- as they do not affect substate.
-- This is because the number of storage reads of a slot in the bytecode
-- may not equal the number of times said slot appears in expressions
-- This fact may also make equivalence proofs a bit trickier

def storageLoad (self : EVM.State) (a : EVM.Address) (key : EVM.Word) : EVM.Word :=
  -- (getAccount σ a).storage.getD (word key) 0
  self.lookupAccount a |>.option ⟨0⟩ (Ethereum.Account.lookupStorage (k := key))

def storageStore (self : EVM.State) (a : EVM.Address) (key value : EVM.Word) : EVM.State :=
  self.lookupAccount a |>.option self λ acc ↦
    self.setAccount a (Ethereum.Account.updateStorage acc key value)

def transientLoad (self : EVM.State) (a : EVM.Address) (key : EVM.Word) : EVM.Word :=
  self.lookupAccount a |>.option ⟨0⟩ (Ethereum.Account.lookupTransientStorage (k := key))

def transientStore (self : EVM.State) (a : EVM.Address) (key value : EVM.Word) : EVM.State :=
  self.lookupAccount a |>.option self fun acc ↦
    self.setAccount a (Ethereum.Account.updateTransientStorage acc key value)

end EVM

/-! ## Storage maps

A contract's persistent storage and its transient storage are both maps from words to words
(`Ethereum.Storage`, absent keys reading as zero). Storage backends work on such a map only: the
semantics hands them the executing account's storage (`EVM.ownStorage`) and writes the result
back (`EVM.setOwnStorage`), so a backend cannot read or change anything else. -/

/-- A storage map: a contract's persistent or transient storage. -/
abbrev SlotMap := Ethereum.Storage

/-- The word at `key`, zero if absent (`SLOAD`/`TLOAD`). -/
def SlotMap.load (s : SlotMap) (key : EVM.Word) : EVM.Word :=
  s.getD key ⟨0⟩

/-- Write `value` at `key` (`SSTORE`/`TSTORE`); a zero word removes the key, as in the EVM. -/
def SlotMap.store (s : SlotMap) (key value : EVM.Word) : SlotMap :=
  if value == default then s.erase key else s.insert key value

@[simp] theorem SlotMap.load_store_self (s : SlotMap) (key value : EVM.Word) :
    (s.store key value).load key = value := by
  unfold SlotMap.load SlotMap.store
  by_cases h : (value == default) = true
  · rw [if_pos h, Std.ExtTreeMap.getD_erase_self]
    exact (eq_of_beq h).symm
  · rw [if_neg h, Std.ExtTreeMap.getD_insert_self]

theorem SlotMap.load_store_ne (s : SlotMap) {key key' : EVM.Word} (value : EVM.Word)
    (hne : key' ≠ key) : (s.store key value).load key' = s.load key' := by
  have hcmp : compare key key' ≠ .eq := by
    intro h
    exact hne (Std.LawfulEqCmp.eq_of_compare h).symm
  unfold SlotMap.load SlotMap.store
  split
  · rw [Std.ExtTreeMap.getD_erase, if_neg hcmp]
  · rw [Std.ExtTreeMap.getD_insert, if_neg hcmp]

namespace EVM

/-- The executing account's persistent storage (empty if the account does not exist). -/
def ownStorage (self : EVM.State) : SlotMap :=
  self.lookupAccount self.executionEnv.codeOwner |>.option ∅ (·.storage)

/-- Replace the executing account's persistent storage (no change if the account does not
    exist). -/
def setOwnStorage (self : EVM.State) (s : SlotMap) : EVM.State :=
  self.lookupAccount self.executionEnv.codeOwner |>.option self fun acc ↦
    self.setAccount self.executionEnv.codeOwner { acc with storage := s }

/-- The executing account's transient storage (empty if the account does not exist). -/
def ownTransient (self : EVM.State) : SlotMap :=
  self.lookupAccount self.executionEnv.codeOwner |>.option ∅ (·.tstorage)

/-- Replace the executing account's transient storage (no change if the account does not
    exist). -/
def setOwnTransient (self : EVM.State) (s : SlotMap) : EVM.State :=
  self.lookupAccount self.executionEnv.codeOwner |>.option self fun acc ↦
    self.setAccount self.executionEnv.codeOwner { acc with tstorage := s }

@[simp] theorem ownStorage_load (self : EVM.State) (key : EVM.Word) :
    (ownStorage self).load key = storageLoad self self.executionEnv.codeOwner key := by
  unfold ownStorage storageLoad SlotMap.load
  cases self.lookupAccount self.executionEnv.codeOwner <;> rfl

@[simp] theorem ownTransient_load (self : EVM.State) (key : EVM.Word) :
    (ownTransient self).load key = transientLoad self self.executionEnv.codeOwner key := by
  unfold ownTransient transientLoad SlotMap.load
  cases self.lookupAccount self.executionEnv.codeOwner <;> rfl

@[simp] theorem setOwnStorage_store (self : EVM.State) (key value : EVM.Word) :
    setOwnStorage self ((ownStorage self).store key value) =
      storageStore self self.executionEnv.codeOwner key value := by
  unfold setOwnStorage ownStorage storageStore SlotMap.store Ethereum.Account.updateStorage
  cases self.lookupAccount self.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option]; split <;> rfl

@[simp] theorem setOwnTransient_store (self : EVM.State) (key value : EVM.Word) :
    setOwnTransient self ((ownTransient self).store key value) =
      transientStore self self.executionEnv.codeOwner key value := by
  unfold setOwnTransient ownTransient transientStore SlotMap.store
    Ethereum.Account.updateTransientStorage
  cases self.lookupAccount self.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option]; split <;> rfl

end EVM




-- Think: maybe have offset/size be optional,
-- so that whole-slot values
-- (mapping/dynarray roots) are differentiated?
-- Think: Is Fin32 unnecassary if we keep hbound?
structure StorageLoc where
  slot    : EVM.Word      -- storage slot in which item is stored
  offset  : Fin 32        -- offset within that slot in bytes
  size    : Fin 33        -- size within that slot in bytes
  hbound  : offset.val + size.val - 1 < 32
                          -- proof that we are withing slot bounds
  bitOffset : Option (Fin 8) := .none -- offset within byte in bits; Needed for packed bytes
  type    : ElemType      -- A value to be loaded from storage must be a primitive
  deriving Repr


-- TODO: maybe create lemmas to prove that the following 2 are equivalent to the bitmasking done by solidity?
-- Or will it prove more convenient to actually define the loads through such bitmasking?
-- In that case maybe the loads should be also be layout-parametric..

-- May not actually need the proof that there is no wraparound
def storageLocLoad (self : SlotMap) (loc : StorageLoc) : Value :=
  let slot := self.load loc.slot
  let ⟨slotBytes, hprevStorageRefSize⟩ := EVM.Word.toBytesLEWithSizeProof slot -- LITTLE ENDIAN! easier extraction
  let startByte := loc.offset.val
  let endByte := loc.offset.val + loc.size.val
  let bytes := slotBytes.extract startByte endByte
  have hbyteSize : bytes.length <= 32 := by
    unfold bytes startByte endByte; simp
    apply Or.inl (by apply Nat.le_of_lt_succ; simp)
  have hresSize : Ethereum.fromBytes' bytes < Ethereum.UInt256.size := by
    apply lt_of_lt_of_le (b := 2^(8 * bytes.length))
    · exact EVM.fromBytes'_le
    · simp [Ethereum.UInt256.size]
      apply le_trans (b := 2^(8 * 32))
      · apply Nat.pow_le_pow_right
        · simp
        · omega
      · simp
  let word : EVM.Word := ⟨Ethereum.fromBytes' bytes, hresSize⟩
  match loc.bitOffset with
  | .some bo => wordToElem loc.type (word.shiftRight ⟨Fin.castLE (by simp [Ethereum.UInt256.size]) bo⟩ : EVM.Word)
  | .none => wordToElem loc.type word

def storageLocWriteWord (slot : EVM.Word) (startByte : Nat)
    (bitOffset : Option (Fin 8)) (valueWord : EVM.Word) : EVM.Word :=
  match bitOffset with
  | .none => valueWord
  | .some bo =>
      let lowBits := 2 ^ bo.val
      let previousLowBits := (slot.toNat / 2 ^ (8 * startByte)) % lowBits
      EVM.word (valueWord.toNat * lowBits + previousLowBits)

-- TODO: Should the given value be restricted to fit in the location?
def storageLocStore (self : SlotMap) (loc : StorageLoc) (value : Value) : Option SlotMap := do
  let slot := self.load loc.slot
  -- LITTLE ENDIAN (`toBytes' ++ zero-pad`) — the *correct* LE serialization, matching
  -- `storageLocLoad` byte-for-byte so that load∘store round-trips and a whole-slot `uint256`
  -- store of `v` writes exactly `v` (the EVM `SSTORE` word).
  let ⟨slotBytes, hprevStorageRefSize⟩ := EVM.Word.toBytesLEWithSizeProof slot
  let valueWord <- valueToWord value
  let startByte := loc.offset.val
  let endByte := loc.offset.val + loc.size.val
  let writeWord := storageLocWriteWord slot startByte loc.bitOffset valueWord
  let ⟨valueBytes, hvalueSize⟩ := EVM.Word.toBytesLEWithSizeProof writeWord

  let previousStart := slotBytes.take startByte
  let previousEnd := slotBytes.drop endByte

  let resList := previousStart ++ (valueBytes.take loc.size.val) ++ previousEnd
  let resWord := Ethereum.fromBytes' resList

  have hbyteSize : resList.length = 32 := by
    unfold resList;
    simp
    have hprevStartLen : previousStart.length = startByte := by
      simp [previousStart]; rw [hprevStorageRefSize]; omega
    have hprevEndLen : previousEnd.length = 32 - endByte := by
      simp [previousEnd]; rw [hprevStorageRefSize]
    rw [hprevStartLen, hprevEndLen]
    rw [Nat.min_eq_left]
    · simp [startByte, endByte];
      rw [← Nat.add_assoc, ← Nat.add_sub_assoc]
      simp
      suffices loc.offset.val + loc.size - 1 < 32 from by omega
      exact loc.hbound
    · rw [hvalueSize]; omega
  have hresSize : Ethereum.fromBytes' resList < Ethereum.UInt256.size := by
    apply lt_of_lt_of_le (b := 2^(8 * resList.length))
    · exact EVM.fromBytes'_le
    · simp [Ethereum.UInt256.size]
      apply le_trans (b := 2^(8 * 32))
      · apply Nat.pow_le_pow_right
        · simp
        · omega
      · simp
  let resUInt256 : Ethereum.UInt256 := ⟨Ethereum.fromBytes' resList, hresSize⟩
  self.store loc.slot resUInt256

/-- Where a storage reference lives. This is a pure function of the reference: anything whose
    physical position depends on the current state (the short/long encoding of Solidity bytes)
    is left symbolic here and resolved by the backend. -/
inductive StorageAddr where
  /-- A primitive value at fixed bits of a fixed slot. -/
  | leaf : StorageLoc -> StorageAddr
  /-- The header slot of a dynamically-sized value (dynamic array length, bytes/string header). -/
  | anchor : EVM.Word -> StorageAddr
  /-- The `index`-th byte of the bytes/string value whose header is at slot `header`. -/
  | byte : (header : EVM.Word) -> (index : Nat) -> StorageAddr
  deriving Repr

/-- Locate a storage reference. Representation-sensitive operations, including Solidity
    bytes and strings, belong to `StorageBackend` rather than this locator. -/
abbrev StorageLayout := EvaledStorageRef -> Option StorageAddr

/-- Storage operations selected by a configuration. They act on one storage map only: the
    semantics passes the executing account's persistent or transient storage and stores the
    result back. `locate?` is for proofs and diagnostics; execution uses the operations
    themselves. -/
structure StorageBackend where
  read : EvaledStorageRef -> StorageType -> SlotMap -> EvalResult Value
  write : EvaledStorageRef -> StorageType -> Value -> SlotMap -> EvalResult SlotMap
  clear : EvaledStorageRef -> StorageType -> SlotMap -> EvalResult SlotMap
  length : EvaledStorageRef -> StorageType -> SlotMap -> EvalResult Nat
  push : EvaledStorageRef -> StorageType -> Option Value -> SlotMap -> EvalResult SlotMap
  pop : EvaledStorageRef -> StorageType -> SlotMap -> EvalResult SlotMap
  locate? : StorageLayout := fun _ => none

/-- No storage declarations are configured. Accesses report an invalid storage reference. -/
def StorageBackend.empty : StorageBackend where
  read := fun _ _ _ ↦ .error .storageError
  write := fun _ _ _ _ ↦ .error .storageError
  clear := fun _ _ _ ↦ .error .storageError
  length := fun _ _ _ ↦ .error .storageError
  push := fun _ _ _ _ ↦ .error .storageError
  pop := fun _ _ _ ↦ .error .storageError


def intTypeSize (t : IntType) : Fin 33 :=
  match t with
  | .uint ⟨bw,hbw⟩ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩
  | .sint ⟨bw,hbw⟩ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩

def fixedTypeSize (t : FixedType) : Fin 33 :=
  match t with
  | .ufixed ⟨bw,hbw⟩ _ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩
  | .fixed ⟨bw,hbw⟩ _ => ⟨bw/8,  by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩
