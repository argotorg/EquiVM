import Benchmarks.Midnight.AliasStorage

/-! Packed settlement-fee fields shared by their getters and interpolation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketStateType : StorageType :=
  match (contract.storage[1]!).ty with
  | .mapping _ ty => ty
  | _ => .elem .bool

def marketStateRef (id : UInt256) : EvaledStorageRef :=
  { base := "marketState", steps :=
    [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))] }

def marketFeeWord (evm : EVM.State) (id : UInt256) : UInt256 :=
  Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id + ⟨2⟩)

def marketTickSpacing (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat 144)) (UInt256.ofNat 255)

def settlementFeeWord (word : UInt256) (i : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat (16 * i))) (UInt256.ofNat 65535)

theorem settlementFeeWord_lt (word : UInt256) (i : Nat) :
    (settlementFeeWord word i).toNat < EVM.twoPow 16 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem settlementFeeWord_zero (word : UInt256) :
    settlementFeeWord word 0 = UInt256.land word (UInt256.ofNat 65535) := by
  unfold settlementFeeWord
  rw [show 16 * 0 = 0 from rfl, shiftRight_zero]

theorem settlementFeeFieldNames : ∀ i : Fin 7,
    "settlementFeeCbp" ++ toString i.val =
      ["settlementFeeCbp0", "settlementFeeCbp1", "settlementFeeCbp2", "settlementFeeCbp3",
        "settlementFeeCbp4", "settlementFeeCbp5", "settlementFeeCbp6"][i.val]'i.isLt := by
  decide +kernel

def settlementFeeFieldLoc (id : UInt256) (i : Fin 7) : StorageLoc := {
  slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩
  offset := ⟨2 * i.val, by omega⟩
  size := 2
  hbound := by change 2 * i.val + 2 - 1 < 32; omega
  type := .int (.uint ⟨16, by decide⟩) }

theorem settlementFeeField_type (i : Fin 7) :
    storageTypeStep? marketStateType (.field ("settlementFeeCbp" ++ toString i.val)) =
      some (.elem (.int (.uint ⟨16, by decide⟩))) := by
  rw [settlementFeeFieldNames i]
  rcases i with ⟨i, hi⟩
  interval_cases i <;> rfl

theorem settlementFeeField_layout (id : UInt256) (i : Fin 7) :
    midnightStorageLayout { (marketStateRef id) with steps := (marketStateRef id).steps ++
      [.field ("settlementFeeCbp" ++ toString i.val)] } =
      some (.leaf (settlementFeeFieldLoc id i)) := by
  rw [settlementFeeFieldNames i]
  rcases i with ⟨i, hi⟩
  interval_cases i <;>
    change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩
      offset := _, size := 2, hbound := _, type := .int (.uint ⟨16, by decide⟩) }) = _ <;>
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32] <;> rfl

theorem settlementFeeField_load (evm : EVM.State) (id : UInt256) (i : Fin 7) :
    storageLocLoad evm (settlementFeeFieldLoc id i) =
      .int (settlementFeeWord (marketFeeWord evm id) i.val).toNat := by
  unfold settlementFeeFieldLoc settlementFeeWord marketFeeWord
  rw [storageLocLoad_uint_offset evm _ ⟨2 * i.val, by omega⟩ 2 ⟨16, by decide⟩
    (by decide) (by omega) (by decide), div_byteOffset_eq_shiftRight]
  congr 6
  change 8 * (2 * i.val) = 16 * i.val
  omega

theorem evalMarketAliasFee {frame : Frame} {evm : EVM.State} {id : UInt256}
    (i : Fin 7)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm (.storage { base := "_marketState", steps :=
      [.field ("settlementFeeCbp" ++ toString i.val)] }) =
      .ok (.int (settlementFeeWord (marketFeeWord evm id) i.val).toNat) := by
  exact evalStorageAliasField hget (settlementFeeField_type i) rfl
    (settlementFeeField_layout id i) (settlementFeeField_load evm id i)

theorem evalMarketAliasTickSpacing {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm
      (.storage { base := "_marketState", steps := [.field "tickSpacing"] }) =
      .ok (.int (marketTickSpacing (marketFeeWord evm id)).toNat) := by
  apply evalStorageAliasField (loc := {
      slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩, offset := 18, size := 1,
      hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }) hget rfl rfl ?_ ?_
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩,
      offset := 18, size := 1, hbound := by decide, type := .int (.uint ⟨8, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint8_offset18 evm _

end Benchmarks.Midnight
