import Benchmarks.Midnight.LiquidatorGateABI

/-! The two entry gates use one address argument and a canonical Boolean reply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

inductive TakeGateKind where
  | credit
  | debt
  deriving DecidableEq

def TakeGateKind.name : TakeGateKind → Ident
  | .credit => "canIncreaseCredit"
  | .debt => "canIncreaseDebt"

def TakeGateKind.selector : TakeGateKind → ByteArray
  | .credit => ⟨#[0x58, 0xac, 0x9f, 0x9e]⟩
  | .debt => ⟨#[0xfe, 0x9b, 0xf9, 0x56]⟩

def TakeGateKind.selectorWord (kind : TakeGateKind) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.ofNat (match kind with | .credit => 0x58ac9f9e | .debt => 0xfe9bf956))
    (UInt256.ofNat 224)

def takeGateCalldata (kind : TakeGateKind) (user : AccountAddress) : ByteArray :=
  kind.selector ++ (UInt256.ofNat user.val).toByteArray

theorem TakeGateKind.selectorWord_bytes (kind : TakeGateKind) :
    kind.selectorWord.toByteArray.extract 0 4 = kind.selector := by
  cases kind <;> decide +kernel

theorem encodeTakeGate (kind : TakeGateKind) (user : AccountAddress) :
    config.externalABI.encode? kind.name [.address user] = some (takeGateCalldata kind user) := by
  have ha := encodeABIValue_accountAddress user
  cases kind <;>
    simp only [TakeGateKind.name, config, externalABI, Model.abiValues, Model.abiValue,
      String.reduceEq, if_false, if_true, encodeCallWithSelector?, encodeABIValues?,
      abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Bool.false_eq_true, bind,
      Option.bind, encodeABIValuesFrom?, ha, List.nil_append, List.append_nil, takeGateCalldata,
      TakeGateKind.selector, word_toBytesBE_toByteArray_eq_toByteArray]

theorem decodeTakeGate (kind : TakeGateKind) (out : ByteArray) :
    config.externalABI.decode? kind.name out =
      if 32 ≤ out.size ∧ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) then
        some [wordToElem .bool (calldataWord out 0)] else none := by
  cases kind <;> exact decodeReturnBoolSlice out

end Benchmarks.Midnight
