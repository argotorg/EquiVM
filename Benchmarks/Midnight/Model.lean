import Stele.Semantics
import Stele.TransientStorage

/-!
Value representations and configuration for Midnight's ABI, transient locks, and SSTORE2.
The tuple/struct adapters change representation only; ABI validation precedes the adapters.
-/

open Stele ABI

namespace Benchmarks.Midnight.Model

def u256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
def u128 : ABIType := .elem (.int (.uint ⟨128, by decide⟩))
def addr : ABIType := .elem .address
def b32 : ABIType := .elem (.bytes ⟨31, by decide⟩)

def collateralABI : ABIType := .tuple [addr, u256, u256, addr]

def marketABI : ABIType :=
  .tuple [u256, addr, addr, .dynamicArray collateralABI, u256, u256, addr, addr]

def offerABI : ABIType :=
  .tuple [marketABI, .elem .bool, addr, u256, u256, u256, b32, addr, .bytes,
    addr, addr, .elem .bool, u128, u128, u256]

mutual
  def abiValue : Value → Value
    | .struct _ fs => .tuple (abiFields fs)
    | .tuple vs => .tuple (abiValues vs)
    | .array vs => .array (abiValues vs)
    | v => v

  def abiValues : List Value → List Value
    | [] => []
    | v :: vs => abiValue v :: abiValues vs

  def abiFields : List (String × Value) → List Value
    | [] => []
    | (_, v) :: fs => abiValue v :: abiFields fs
end

def collateralValue : Value → Value
  | .tuple vs => .struct "CollateralParams"
      (["token", "lltv", "liquidationCursor", "oracle"].zip vs)
  | v => v

def marketValue : Value → Value
  | .tuple [chainId, midnight, loanToken, .array params, maturity, threshold, enter, liquidator] =>
      .struct "Market" [
        ("chainId", chainId), ("midnight", midnight), ("loanToken", loanToken),
        ("collateralParams", .array (params.map collateralValue)), ("maturity", maturity),
        ("rcfThreshold", threshold), ("enterGate", enter), ("liquidatorGate", liquidator)]
  | v => v

def offerValue : Value → Value
  | .tuple (market :: rest) => .struct "Offer"
      (("market", marketValue market) ::
        (["buy", "maker", "start", "expiry", "tick", "group", "callback", "callbackData",
          "receiverIfMakerIsSeller", "ratifier", "reduceOnly", "maxUnits", "maxAssets",
          "continuousFeeCap"].zip rest))
  | v => v

-- multicall keeps its nested bytes in calldata: signed tail bounds and wrapping
-- offsets at pcs 3590–3652 admit aliases that a conventional ABI decoder rejects.
-- Other arguments are fully decoded before their first observable effect.
def calldataMode : DecodeMode :=
  .solc08Calldata [(0xac9650d8, [{ materialize := [] }])]

def collateralCount? : Value → Option Nat
  | .tuple [_, _, _, .array collaterals, _, _, _, _] => some collaterals.length
  | _ => none

-- Closed input-length guards from the uint64 allocation checks in the entry
-- decoders (pcs 18389–18499, 18574–18818, 19016–19112, 10425–10529).
-- These are necessary conditions for completing argument decoding. No memory
-- state is represented: sizes are computed from already decoded values.
def inputSizesFit (locals : Store) : Bool := Id.run do
  if let some market := locals["market"]? then
    let some n := collateralCount? market | return false
    if !(1120 + 160 * n < 2^64) then return false
  if let some offer := locals["offer"]? then
    match offer, locals["ratifierData"]?, locals["takerCallbackData"]? with
    | .tuple [market, _, _, _, _, _, _, _, .bytes callbackData, _, _, _, _, _, _],
        some (.bytes ratifierData), some (.bytes takerData) =>
      let some n := collateralCount? market | return false
      if !(1696 + 160 * n + paddedSize callbackData.size + paddedSize ratifierData.size +
          paddedSize takerData.size < 2^64) then return false
    | _, _, _ => return false
  return true

def decodeCalldata (names : List Ident) (types : List ABIType) (bytes : ByteArray) :
    Option Store := do
  let locals ← ABI.decodeCalldataWithMode calldataMode names types bytes
  if !inputSizesFit locals then none else do
  let locals := match locals["market"]? with
    | some v => locals.insert "market" (marketValue v)
    | none => locals
  let locals := match locals["offer"]? with
    | some v => locals.insert "offer" (offerValue v)
    | none => locals
  pure locals

def sstore2Prefix : ByteArray := ⟨#[0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3]⟩

def creationCode (name : Ident) (args : List Value) : Option ByteArray := do
  if name != "SSTORE2" then none else
    let encoded ← ABI.encodeReturnValues? [marketABI] (abiValues args)
    pure (sstore2Prefix ++ encoded)

-- The entire transient word is tested for zero by TLOAD/ISZERO. A byte-sized bool backend
-- would incorrectly ignore high bits in arbitrary transient pre-states.
def lockLayout (ref : EvaledStorageRef) : Option StorageAddr := do
  if ref.base != "locks" then none else
    match ref.steps with
    | [.mindex (.int base), .mindex (.fixedBytes _ key), .mindex (.address user)] =>
        let encoded := key.toByteArray ++ (EVM.word user.toNat).toByteArray ++
          (EVM.wordOfInt base).toByteArray
        let slot := Ethereum.uInt256OfByteArray (Ethereum.KEC encoded)
        pure (.leaf {
          slot := slot
          offset := 0
          size := 32
          type := .int (.uint ⟨256, by decide⟩)
          hbound := by decide })
    | _ => none

def transientBackend : StorageBackend := solidityTransientStorageBackend lockLayout

end Benchmarks.Midnight.Model
