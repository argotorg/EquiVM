import Solidity.Value
import ABI.Encode

/-!
# Revert payloads

`Error(string)` (selector `0x08c379a0`), `Panic(uint256)` (`0x4e487b71`) and custom errors
(selector of the error signature followed by the ABI encoding of the arguments).  `require(c)`
and `revert()` revert with empty data.
-/

namespace Solidity

def errorStringSelector : ByteArray := ⟨#[0x08, 0xc3, 0x79, 0xa0]⟩
def panicSelector : ByteArray := ⟨#[0x4e, 0x48, 0x7b, 0x71]⟩

def panicData (code : Nat) : ByteArray :=
  panicSelector ++ (Ethereum.UInt256.ofNat code).toByteArray

def Panic.data (p : Panic) : ByteArray := panicData p.code

/-- `abi.encodeWithSelector(Error.selector, msg)`. -/
def errorStringData (msg : ByteArray) : ByteArray :=
  errorStringSelector ++ ((ABI.encodeABIValues? [.string] [.bytes msg]).getD []).toByteArray

def selectorOf (sigStr : String) : ByteArray := (ffi.KEC sigStr.toUTF8).extract 0 4

/-- `abi.encodeWithSelector(E.selector, args)` for a custom error. -/
def customErrorData (sigStr : String) (tys : List ABI.ABIType) (args : List Solm.Value) :
    Option ByteArray :=
  ABI.encodeCallWithSelector? (selectorOf sigStr) tys args

end Solidity
