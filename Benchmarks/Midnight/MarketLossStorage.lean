import Benchmarks.Midnight.MarketBalanceFields

/-! Reading and writing the market's loss factor through its storage alias. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem marketLoss_layout (id : UInt256) :
    midnightStorageLayout { (marketStateRef id) with steps :=
      (marketStateRef id).steps ++ [.field "lossFactor"] } =
      some (.leaf (uint128HighLoc (solcMappingSlot ⟨1⟩ id))) := by
  change some (StorageAddr.leaf {
    slot := solcMappingSlot ⟨1⟩
      (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
    offset := 16, size := 16, hbound := _, type := .int packedUInt128Int }) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  rfl

theorem evalMarketAliasLoss {frame : Frame} {evm : State} {id : UInt256}
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm (.storage { base := "_marketState", steps := [.field "lossFactor"] }) =
      .ok (.int (marketLossWord evm id).toNat) := by
  apply evalStorageAliasField (loc := uint128HighLoc (solcMappingSlot ⟨1⟩ id))
    hm rfl rfl (marketLoss_layout id)
  exact storageLocLoad_uint128_high evm _

theorem assignMarketAliasLoss {frame : Frame} {evm : State} {id : UInt256} (value : UInt256)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage
      { base := "_marketState", steps := [.field "lossFactor"] } (.int value.toNat) =
      .ok (frame, storeHigh128 evm (solcMappingSlot ⟨1⟩ id) value) := by
  apply assignStorageAliasField (loc := uint128HighLoc (solcMappingSlot ⟨1⟩ id))
    hm rfl rfl (marketLoss_layout id)
  exact storageLocStore_uint128_high_word evm _ value

-- LIBRARY CANDIDATE: subtraction from the uint128 maximum in a checked uint256 expression.
theorem evalComplement128As256 {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int word.toNat)) (hw : word.toNat < 2 ^ 128) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.intLit (2 ^ 128 - 1)) expr)) =
      .ok (.int (complement128 word).toNat) := by
  apply evalExpr_uint256_sub (a := uint128Mask) (b := word) ?_ he
  · change word.toNat ≤ 340282366920938463463374607431768211455
    omega
  · norm_num [evalExpr?, pure, uint256Value,
      show uint128Mask.toNat = 340282366920938463463374607431768211455 from rfl]

end Benchmarks.Midnight
