import Solidity.Test.Harness
import Solidity.Test.Specs.Calldata
import Solidity.Test.Fixtures.CalldataSolc

/-! # Differential cases: calldata words that are not canonical, `using` on an interface type.

`Copies`: a calldata array or struct parameter keeps its words; solc validates a word when an
element or field is read, when the object is ABI-encoded (`abi.encode`, an external call, an
event, an error), when it is copied to storage and when a struct or an array of dynamic arrays or
structs is copied to memory; an array of value-type words (or of static arrays of them) is copied
to memory with cleanup.  `Attach`: `using Lib for IT` with a call through a value of the interface
type.  `Calldata/known` pins two deviations: a calldata-typed return with a word that is not
canonical has no derivation (solc reverts); an enum array copied to memory is checked at the copy
(solc checks an element when it is read); the headers of the inner arrays of a calldata array of
dynamic arrays are checked when the call is decoded (solc checks them when the inner array is
used: `Panic(0x32)` for an index into a misplaced header, `Panic(0x41)` for an absurd length copied
to memory). -/

namespace Solidity.Test.Calldata

open Solidity.Test Ethereum

def tokRuntime : ByteArray := bytesOfHex Fixtures.tokRuntimeHex
def attachRuntime : ByteArray := bytesOfHex Fixtures.attachRuntimeHex
def copiesRuntime : ByteArray := bytesOfHex Fixtures.copiesRuntimeHex
def knownRuntime : ByteArray := bytesOfHex Fixtures.knownRuntimeHex

def M : Nat := 2 ^ 256 - 1
def TOK : Nat := 0x70C
def A (n : Nat) : ABI.ABIValue := .address (addr n)
def arr (xs : List Int) : ABI.ABIValue := .array (xs.map (.int ·))
def words (ws : List Nat) : ByteArray := ws.foldl (fun b w => b ++ wordBytes w) ByteArray.empty

def mk (code : ByteArray) (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := code, call := some (sig, args) }

/-- A call with the argument words as given (not necessarily canonical). -/
def rawCall (code : ByteArray) (sig : String) (ws : List Nat) (tag : String := "") : Case :=
  { name := s!"{sig} raw {tag}", code := code, calldata := selectorOfSig sig ++ words ws }

/-! ## Attach -/

def mkA (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { mk attachRuntime sig args tag with accounts := [(addr TOK, account (code := tokRuntime))] }

def attachCases : List Case :=
  [ { mkA "viaMember(address)" [A TOK] with expect := .success },
    { mkA "viaLib(address)" [A TOK] with expect := .success },
    { mkA "own(address)" [A TOK] with expect := .success },
    { mkA "viaMember(address)" [A 0xE0A] "no code" with expect := .revert },
    { mkA "num(uint256)" [.int 21] with expect := .success },
    { mkA "num(uint256)" [.int M] "overflow" with expect := .revert } ]

/-! ## Copies -/

def mkC (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case := mk copiesRuntime sig args tag
def rc (sig : String) (ws : List Nat) (tag : String := "") : Case := rawCall copiesRuntime sig ws tag

/-- A dynamic array of two words, the second one dirty for `uint16`. -/
def dirty16 : List Nat := [0x20, 2, 1, 2 ^ 16]

def copyCases : List Case :=
  [ { rc "pass(uint128[])" [0x20, 2, 1, 2 ^ 128] "dirty" with expect := .success },
    { mkC "pass(uint128[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "enc(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "enc(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "packed(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "packed(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "hashIt(uint16[])" dirty16 "dirty" with expect := .revert },
    { rc "copyLen(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyAdd(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyAdd(uint16[])" [0x20, 2, 1, 2 ^ 16 + 3] "dirty+3" with expect := .success },
    { mkC "copyAdd(uint16[])" [arr [1, 2 ^ 16 - 1]] "overflow" with expect := .revert },
    { rc "copyEnc(uint16[])" [0x20, 2, 1, 2 ^ 16 + 3] "dirty" with expect := .success },
    { rc "copyEq(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "copyBool(bool[])" [0x20, 2, 1, 2] "two" with expect := .success },
    { rc "copyBool(bool[])" [0x20, 2, 1, 0] "zero" with expect := .success },
    { rc "toStore(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "toStore(uint16[])" [arr [1, 2, 3]] "clean" with expect := .success },
    { rc "fwd(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "fwd(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "len(uint16[])" dirty16 "dirty" with expect := .success },
    { rc "first(uint16[])" dirty16 "dirty second" with expect := .success },
    { rc "first(uint16[])" [0x20, 1, 2 ^ 16] "dirty first" with expect := .revert },
    { rc "memLen(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "memLen(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "emitArr(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "emitArr(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rc "revertArr(uint16[])" dirty16 "dirty" with expect := .revert },
    { mkC "revertArr(uint16[])" [arr [1, 2]] "clean" with expect := .revert },
    { rc "fieldY((uint8,uint256))" [300, 1] "dirty x" with expect := .success },
    { rc "fieldX((uint8,uint256))" [300, 1] "dirty x" with expect := .revert },
    { rc "fieldX((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "structCopy((uint8,uint256))" [300, 1] "dirty" with expect := .revert },
    { rc "structCopy((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "structEnc((uint8,uint256))" [300, 1] "dirty" with expect := .revert },
    { rc "structEnc((uint8,uint256))" [3, 1] "clean" with expect := .success },
    { rc "ssY((uint8,uint256)[],uint256)" [0x40, 0, 1, 300, 1] "dirty x" with expect := .success },
    { rc "ssX((uint8,uint256)[],uint256)" [0x40, 0, 1, 300, 1] "dirty x" with expect := .revert },
    { rc "ssCopy((uint8,uint256)[])" [0x20, 1, 300, 1] "dirty" with expect := .revert },
    { rc "ssCopy((uint8,uint256)[])" [0x20, 1, 3, 1] "clean" with expect := .success },
    { rc "fixedOuter(uint8[2][],uint256)" [0x40, 0, 1, 300, 1] "dirty" with expect := .success },
    { rc "fixedOuterCopy(uint8[2][])" [0x20, 1, 300, 1] "dirty" with expect := .success },
    { rc "fixedOuterCopy(uint8[2][])" [0x20, 1, 3, 1] "clean" with expect := .success },
    { rc "fixedCopy(uint16[2])" [1, 2 ^ 16 + 5] "dirty" with expect := .success },
    { rc "addrAt(address[],uint256)" [0x40, 0, 1, 2 ^ 160] "dirty read" with expect := .revert },
    { rc "addrAt(address[],uint256)" [0x40, 0, 2, 1, 2 ^ 160] "dirty not read" with expect := .success },
    { rc "addrCopy(address[])" [0x20, 1, 2 ^ 160 + 7] "dirty" with expect := .success },
    { rc "bytesAt(bytes4[],uint256)" [0x40, 0, 1, 1] "dirty read" with expect := .revert },
    { rc "bytesAt(bytes4[],uint256)" [0x40, 0, 1, 0xdeadbeef <<< 224] "clean" with expect := .success },
    { rc "bytesCopy(bytes4[])" [0x20, 1, (0xdeadbeef <<< 224) + 1] "dirty" with expect := .success },
    { rc "intAt(int64[],uint256)" [0x40, 0, 1, 2 ^ 63] "dirty read" with expect := .revert },
    { rc "intAt(int64[],uint256)" [0x40, 0, 1, M] "minus one" with expect := .success },
    { rc "intAt(int64[],uint256)" [0x40, 1, 2, 2 ^ 63, 5] "dirty not read" with expect := .success },
    { rc "intCopy(int64[])" [0x20, 1, 2 ^ 63] "dirty" with expect := .success },
    { rc "intCopy(int64[])" [0x20, 1, M] "minus one" with expect := .success },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 1, 3] "out of range read" with expect := .revert },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 1, 2] "clean" with expect := .success },
    { rc "enumAt(uint8[],uint256)" [0x40, 0, 2, 2, 7] "out of range not read" with expect := .success },
    { rc "enumCopy(uint8[])" [0x20, 1, 7] "out of range" with expect := .revert },
    { rc "enumCopy(uint8[])" [0x20, 1, 1] "clean" with expect := .success },
    { rc "priceAt(uint128[],uint256)" [0x40, 0, 1, 2 ^ 128] "dirty read" with expect := .revert },
    { rc "priceAt(uint128[],uint256)" [0x40, 0, 2, 1, 2 ^ 128] "dirty not read" with expect := .success },
    { rc "priceCopy(uint128[])" [0x20, 1, 2 ^ 128 + 9] "dirty" with expect := .success } ]

/-! ## Known -/

def retCdKnown : String := "a calldata-typed return with a word that is not canonical has no derivation"
def innerKnown : String := "the headers of the inner arrays of a calldata array of dynamic arrays are checked when the call is decoded; solc checks them when the inner array is used"
def rk (sig : String) (ws : List Nat) (tag : String := "") : Case := rawCall knownRuntime sig ws tag
def enumCopyKnown : String := "an enum array copied to memory is checked at the copy (Panic 0x21); solc checks an element when it is read"

def knownCases : List Case :=
  [ { rawCall knownRuntime "retCd(uint16[])" dirty16 "dirty" with expect := .revert, known := some retCdKnown },
    { mk knownRuntime "retCd(uint16[])" [arr [1, 2]] "clean" with expect := .success },
    { rawCall knownRuntime "enumCopyLen(uint8[])" [0x20, 1, 7] "out of range" with expect := .success, known := some enumCopyKnown },
    { rawCall knownRuntime "enumCopyLen(uint8[])" [0x20, 1, 1] "clean" with expect := .success },
    { rk "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 0x20, 1, 300] "dirty read" with expect := .revert },
    { rk "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 0x20, 2, 3, 300] "dirty not read" with expect := .success },
    { rk "nested(uint8[][],uint256,uint256)" [0x60, 0, 0, 1, 2 ^ 255, 1, 300] "inner offset beyond the data" with
        expect := .revert, known := some innerKnown },
    { rk "nestedCopy(uint8[][])" [0x20, 1, 0x20, 1, 300] "dirty" with expect := .revert },
    { rk "nestedCopy(uint8[][])" [0x20, 1, 0x20, 1, 3] "clean" with expect := .success },
    { rk "nestedCopy(uint8[][])" [0x20, 1, 0x20, 2 ^ 160 + 0xf7e5, 300] "absurd inner length" with
        expect := .revert, known := some innerKnown } ]

def P := _root_.Calldata.SoliditySpec.program

def scenarios : List Scenario :=
  [ { name := "Attach", program := P, target := "Attach", cases := attachCases },
    { name := "Copies", program := P, target := "Copies", cases := copyCases },
    { name := "Calldata/known", program := P, target := "Known", cases := knownCases } ]

end Solidity.Test.Calldata
