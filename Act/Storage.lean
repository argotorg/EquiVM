import EVM.Types
import EVM.Lemmas
import Act.Value

-- TODO: I'd like to get rid of these maybe
import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Wheels

namespace Act

open ABI

namespace EVM

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

end EVM 



/- This is to avoid a failure that happens for some reason
 - - TODO: investigate
 -/
-- Didn't work.
-- opaque localKEC (d : data) : ByteArray
-- axiom localKEC_ffiKEC : ∀ d, localKEC d = ffi.KEC d


-- TODO: DYNAMIC ARRAYS need to also have a length field, at least for solidity!

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
  type    : ElemType      -- A value to be loaded from storage must be a primitive
  deriving Repr


-- TODO: maybe create lemmas to prove that the following 2 are equivalent to the bitmasking done by solidity?
-- Or will it prove more convenient to actually define the loads through such bitmasking?
-- In that case maybe the loads should be also be layout-parametric..

-- May not actually need the proof that there is no wraparound
def storageLocLoad (self : EVM.State) (loc : StorageLoc) : Value :=
  let slot := EVM.storageLoad self self.executionEnv.codeOwner loc.slot
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
  let word := ⟨Ethereum.fromBytes' bytes, hresSize⟩
  wordToElem loc.type word

-- TODO: Should the given value be restricted to fit in the location?
def storageLocStore (self : EVM.State) (loc : StorageLoc) (value : Value) : Option EVM.State := do
  let slot := EVM.storageLoad self self.executionEnv.codeOwner loc.slot
  let ⟨slotBytes, hprevStorageRefSize⟩ := EVM.UInt256.toBytesWithSizeProof slot -- LITTLE ENDIAN! easier extraction
  let valueWord <- valueToWord value
  let ⟨valueBytes, hvalueSize⟩ := EVM.UInt256.toBytesWithSizeProof valueWord
  let startByte := loc.offset.val
  let endByte := loc.offset.val + loc.size.val

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
  EVM.storageStore self self.executionEnv.codeOwner loc.slot resUInt256

inductive EvaledStorageRefStep where
  | field : Ident -> EvaledStorageRefStep
  | tupleElem : Nat -> EvaledStorageRefStep
  | mindex : KeyValue -> EvaledStorageRefStep
  | aindex : KeyValue -> EvaledStorageRefStep
  deriving DecidableEq, Inhabited

structure EvaledStorageRef where
  base : Ident
  steps : List EvaledStorageRefStep := []
  deriving DecidableEq, Inhabited

structure StorageLayout where
  layout : EvaledStorageRef -> Option StorageLoc
  -- Note: The above definition may need to also carry some assumptions if
  -- we want have a type system on top of these semantics,
  -- e.g. access within array bounds returns `.some v`

  -- TODO: Note: the above definition would not cover schemas where the
  -- location in storage would depend on storage values along the way
  -- which is actually done for compacted bytes and string values..
  -- Ignoring this for now..

-- TODO: move
def keyValueToWord : KeyValue -> EVM.Word
  | .int i => EVM.wordOfInt i
  | .bool b => b.toUInt256
  | .address a =>
    { val := (@Fin.castLE Ethereum.AccountAddress.size
                          Ethereum.UInt256.size
                            (by unfold Ethereum.AccountAddress.size Ethereum.UInt256.size; simp) a : Fin Ethereum.UInt256.size) }

def intTypeSize (t : IntType) : Fin 33 :=
  match t with
  | .uint ⟨bw,hbw⟩ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩
  | .sint ⟨bw,hbw⟩ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩

def fixedTypeSize (t : FixedType) : Fin 33 :=
  match t with
  | .ufixed ⟨bw,hbw⟩ _ => ⟨bw/8, by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩
  | .fixed ⟨bw,hbw⟩ _ => ⟨bw/8,  by apply Nat.lt_succ_of_le; apply Nat.div_le_of_le_mul; simp; omega⟩

