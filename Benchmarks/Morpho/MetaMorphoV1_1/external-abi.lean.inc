/-! ## External-call ABI, audited against the pinned Blue and OpenZeppelin interfaces

The runtime calls extSloads for supplyShares/lastUpdate; those are inlined library helpers.
Only the external boundary encodes named memory structs as ABI tuples.
-/

private def uint256ABI : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
private def uint128ABI : ABIType := .elem (.int (.uint ⟨128, by decide⟩))
private def wordABI : ABIType := .elem (.bytes ⟨31, by decide⟩)
private def paramsABI : ABIType :=
  .tuple [.elem .address, .elem .address, .elem .address, .elem .address, uint256ABI]
private def marketABI : ABIType := .tuple (List.replicate 6 uint128ABI)
private def positionABI : ABIType := .tuple [uint256ABI, uint128ABI, uint128ABI]

private def structToABI (v : Value) : Value :=
  match v with
  | .struct _ fields => .tuple (fields.map Prod.snd)
  | _ => v

private def asStruct (tag : String) (names : List String) (vs : List Value) :
    Option (List Value) :=
  match vs with
  | [.tuple fields] =>
      if fields.length = names.length then some [.struct tag (names.zip fields)] else none
  | _ => none

private def externalSignature (name : String) : Option (Nat × List ABIType × List ABIType) :=
  match name with
  | "supply" => some (0xa99aad89,
      [paramsABI, uint256ABI, uint256ABI, .elem .address, .bytes], [uint256ABI, uint256ABI])
  | "withdraw" => some (0x5c2bea49,
      [paramsABI, uint256ABI, uint256ABI, .elem .address, .elem .address], [uint256ABI, uint256ABI])
  | "position" => some (0x93c52062, [wordABI, .elem .address], [positionABI])
  | "market" => some (0x5c60e39a, [wordABI], [marketABI])
  | "idToMarketParams" => some (0x2c3c9157, [wordABI], [paramsABI])
  | "accrueInterest" => some (0x151c1ade, [paramsABI], [])
  | "extSloads" => some (0x7784c685, [.dynamicArray wordABI], [.dynamicArray wordABI])
  | "borrowRateView" => some (0x8c00bf6b, [paramsABI, marketABI], [uint256ABI])
  | "decimals" => some (0x313ce567, [], [.elem (.int (.uint ⟨8, by decide⟩))])
  | "balanceOf" => some (0x70a08231, [.elem .address], [uint256ABI])
  | "transfer" => some (0xa9059cbb, [.elem .address, uint256ABI], [.elem .bool])
  | "transferFrom" => some (0x23b872dd,
      [.elem .address, .elem .address, uint256ABI], [.elem .bool])
  | "approve" => some (0x095ea7b3, [.elem .address, uint256ABI], [.elem .bool])
  | _ => none

def externalABI : ExternalCallABI where
  encode? := fun name args => do
    let (selector, params, _) ← externalSignature name
    let selectorData := ByteArray.mk ((EVM.Word.ofNat selector).toBytesBE.drop 28).toArray
    ABI.encodeCallWithSelector? selectorData params (args.map structToABI)
  decode? := fun name out => do
    let (_, _, rets) ← externalSignature name
    let values ← if rets.isEmpty then some [] else ABI.decodeReturnValues? rets out
    match name with
    | "market" =>
        asStruct "Market" ["totalSupplyAssets", "totalSupplyShares", "totalBorrowAssets",
          "totalBorrowShares", "lastUpdate", "fee"] values
    | "idToMarketParams" =>
        asStruct "MarketParams" ["loanToken", "collateralToken", "oracle", "irm", "lltv"] values
    | "position" => asStruct "Position" ["supplyShares", "borrowShares", "collateral"] values
    | _ => some values

