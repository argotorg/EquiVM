import Solidity.Test.Harness
import Solidity.Test.Specs.Ecrecover
import Solidity.Test.Fixtures.EcrecoverSolc

/-! # Differential cases: `ecrecover`. -/

namespace Solidity.Test.Ecrecover

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.ecrecoverCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.ecrecoverRuntimeHex

def b32 (n : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

/-- A valid secp256k1 signature (go-ethereum's `TestRecoverSanity` vector, recovery id 1). -/
def msgHash : Nat := 0xce0677bb30baa8cf067c88db9811f4333d131bf8bcf12fe7065d211dce971008
def sigR : Nat := 0x90f27b8b488db00b00606796d2987f6a5f59ae62ea05effe84fef5b8b0e54998
def sigS : Nat := 0x4a691139ad57a3f0b906637673aa2f63d1f55cb1a69199d4009eea23ceaddc93

def args (h v r s : Nat) : List ABI.ABIValue := [b32 h, .int v, b32 r, b32 s]

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime }

def cases : List Case :=
  [ rt "valid" { call := some ("recNonZero(bytes32,uint8,bytes32,bytes32)", args msgHash 28 sigR sigS), expect := .success },
    rt "valid-store" { call := some ("recStore(bytes32,uint8,bytes32,bytes32)", args msgHash 28 sigR sigS), expect := .success },
    rt "wrong-v" { call := some ("recNonZero(bytes32,uint8,bytes32,bytes32)", args msgHash 5 sigR sigS), expect := .revert },
    rt "wrong-v-zero-address" { call := some ("rec(bytes32,uint8,bytes32,bytes32)", args msgHash 5 sigR sigS), expect := .success },
    rt "other-recid" { call := some ("rec(bytes32,uint8,bytes32,bytes32)", args msgHash 27 sigR sigS), expect := .success },
    rt "zero-sig" { call := some ("rec(bytes32,uint8,bytes32,bytes32)", args 0 27 0 0), expect := .success },
    rt "high-s" { call := some ("rec(bytes32,uint8,bytes32,bytes32)", args msgHash 28 sigR (2 ^ 256 - 1)), expect := .success },
    rt "nonpayable" { call := some ("rec(bytes32,uint8,bytes32,bytes32)", args msgHash 28 sigR sigS), value := 1, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "Ecrecover", program := _root_.Ecrecover.SoliditySpec.program, target := "Ec", cases := cases }

end Solidity.Test.Ecrecover
