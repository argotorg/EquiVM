import Benchmarks.CompoundIII.Comet.UserBasicFields
import Benchmarks.CompoundIII.Comet.NegativePrincipal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

structure UserBasicData where
  principal : UInt256
  index : UInt256
  accrued : UInt256
  assets : UInt256
  reserved : UInt256
  index_lt : index.toNat < 2^64
  accrued_lt : accrued.toNat < 2^64
  assets_lt : assets.toNat < 2^16
  reserved_lt : reserved.toNat < 2^8

def userBasicData (word : UInt256) : UserBasicData :=
  { principal := word
    index := userBasicFieldWord word 0
    accrued := userBasicFieldWord word 1
    assets := userBasicFieldWord word 2
    reserved := userBasicFieldWord word 3
    index_lt := packedUint_lt word _ (by decide)
    accrued_lt := packedUint_lt word _ (by decide)
    assets_lt := packedUint_lt word _ (by decide)
    reserved_lt := packedUint_lt word _ (by decide) }

def userBasicValues (basic : UserBasicData) : List (Ident × Value) :=
  [("principal", .int (signed104 basic.principal)),
    ("baseTrackingIndex", .int basic.index.toNat),
    ("baseTrackingAccrued", .int basic.accrued.toNat),
    ("assetsIn", .int basic.assets.toNat), ("_reserved", .int basic.reserved.toNat)]

def userBasicValue (basic : UserBasicData) : Value :=
  .struct "UserBasic" (userBasicValues basic)

def userBasicTypes : List (Ident × StorageType) :=
  [("principal", .elem (.int (.sint ⟨104, by decide⟩))),
    ("baseTrackingIndex", .elem (.int (.uint ⟨64, by decide⟩))),
    ("baseTrackingAccrued", .elem (.int (.uint ⟨64, by decide⟩))),
    ("assetsIn", .elem (.int (.uint ⟨16, by decide⟩))),
    ("_reserved", .elem (.int (.uint ⟨8, by decide⟩)))]

def userBasicType : StorageType := .struct "UserBasic" userBasicTypes

end Benchmarks.CompoundIII.Comet
