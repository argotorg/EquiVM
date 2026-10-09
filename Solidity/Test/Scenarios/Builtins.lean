import Solidity.Test.Harness
import Solidity.Test.Specs.Builtins
import Solidity.Test.Fixtures.BuiltinsSolc

/-! # Differential cases: builtins and conversions.

`Env`: block, tx and msg members, account members, units.  `Hash`: keccak256, sha256, packed
encoding.  `Rip`: ripemd160, only where the EVM model's precompile script runs.  `AbiC`:
abi.encode*, abi.decode, concat.  `AbiFixed`: fixed-size memory arrays through the ABI.  `TypeInfo`:
type(...) members and selectors.  `Conv`: conversions.  `MemOps`: delete on memory, push() as a
reference, push and pop on storage bytes.  `RetUser`: return data that cannot be decoded.  `StoreStr`:
storage strings and byte arrays as arguments of the hash and concat builtins. -/

namespace Solidity.Test.Builtins

open Solidity.Test Ethereum

def envRuntime : ByteArray := bytesOfHex Fixtures.envRuntimeHex
def hashRuntime : ByteArray := bytesOfHex Fixtures.hashRuntimeHex
def ripRuntime : ByteArray := bytesOfHex Fixtures.ripRuntimeHex
def abiRuntime : ByteArray := bytesOfHex Fixtures.abiCRuntimeHex
def fixedRuntime : ByteArray := bytesOfHex Fixtures.abiFixedRuntimeHex
def typeRuntime : ByteArray := bytesOfHex Fixtures.typeInfoRuntimeHex
def convRuntime : ByteArray := bytesOfHex Fixtures.convRuntimeHex
def memRuntime : ByteArray := bytesOfHex Fixtures.memOpsRuntimeHex
def smallCreation : ByteArray := bytesOfHex Fixtures.smallCreationHex
def smallRuntime : ByteArray := bytesOfHex Fixtures.smallRuntimeHex
def oDerCreation : ByteArray := bytesOfHex Fixtures.oDerCreationHex
def retRuntime : ByteArray := bytesOfHex Fixtures.retUserRuntimeHex
def retBadRuntime : ByteArray := bytesOfHex Fixtures.retBadRuntimeHex
def strRuntime : ByteArray := bytesOfHex Fixtures.storeStrRuntimeHex

def MAX : Int := 2 ^ 256 - 1
def A : Solm.Value := .address (addr 0xA11CE)

/-- `bytesN` with `N = k + 1`: the low `N` bytes of `n`. -/
def fb (k : Fin 32) (n : Nat) : Solm.Value := .fixedBytes k ((wordBytes n).toList.drop (31 - k.val))
def bytesN (n : Nat) : ByteArray := ⟨((List.range n).map fun i => UInt8.ofNat (i + 1)).toArray⟩
def str (n : Nat) : Solm.Value := .bytes ⟨((List.range n).map fun i => UInt8.ofNat (97 + i % 26)).toArray⟩
def w (n : Int) : ByteArray := wordBytes (n % 2 ^ 256).toNat

def tU (n : Nat) (h : 0 < n ∧ n ≤ 256 ∧ n % 8 = 0 := by decide) : ABI.ABIType := .elem (.int (.uint ⟨n, h⟩))
def encOf (tys : List ABI.ABIType) (vs : List Solm.Value) : ByteArray :=
  ((ABI.encodeABIValues? tys vs).map fun bs => (⟨bs.toArray⟩ : ByteArray)).getD .empty

def mk (code : ByteArray) (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := code, call := some (sig, args) }

/-! ## Env -/

def hdr (number : Nat) : BlockHeader :=
  { (default : BlockHeader) with
    timestamp := 1700000000, number := number, gasLimit := 30000000,
    beneficiary := addr 0xC01, prevRandao := word 0xabcdef, baseFeePerGas := 7, difficulty := 11 }

def blocksN (n : Nat) : ProcessedBlocks :=
  ((List.range n).map fun i => ({ hash := word (1000 + i), blockHeader := default, σ := ∅ } : ProcessedBlock)).toArray

/-- A contract, a funded account, an account with a nonce only, an empty account. -/
def others : List (EVM.Address × Account) :=
  [(addr 0xB0B, account (balance := 77) (code := hashRuntime)), (addr 0xE0A, account (balance := 5)),
   (addr 0xE0B, account), (addr 0xE0C, account (nonce := 0))]

def who : List (String × Solm.Value) :=
  [("contract", .address (addr 0xB0B)), ("funded", .address (addr 0xE0A)), ("nonce", .address (addr 0xE0B)),
   ("empty", .address (addr 0xE0C)), ("absent", .address (addr 0xDEAD)), ("self", .address (addr 0xC0FFEE)),
   ("sender", A), ("precompile", .address (addr 2))]

def mkE (sig : String) (args : List Solm.Value) (tag : String := "") (number : Nat := 5) : Case :=
  { mk envRuntime sig args tag with
    header := hdr number, blocks := blocksN number, origin := some (addr 0x0816),
    gasPrice := 3, accounts := others, balance := 9 }

def envCases : List Case :=
  [ { mkE "blockInfo()" [] with expect := .success }, { mkE "txInfo()" [] with value := 4, expect := .success },
    { mkE "callData(uint256,bytes)" [.int 7, .bytes (bytesN 5)] with expect := .success },
    { mkE "hashes(uint256)" [.int 3] "3" with expect := .success },
    { mkE "units()" [] with expect := .success }, { mkE "unitMath(uint256)" [.int 3] with expect := .success },
    { mkE "gasOk()" [] with expect := .success } ] ++
  who.flatMap fun (n, a) => [mkE "accounts(address)" [a] n, mkE "codeHashes(address)" [a] n]

def envBoundaries : List Case :=
  ([(0 : Int), 4, 5, 6, MAX].map fun n => mkE "hashes(uint256)" [.int n] s!"{n}") ++
  ([(0 : Int), 43, 44, 45, 298, 299, 300, 301, MAX].map fun n => mkE "hashes(uint256)" [.int n] s!"{n} at 300" 300) ++
  [mkE "hashes(uint256)" [.int 0] "at 0" 0, mkE "hashes(uint256)" [.int 0] "at 1" 1] ++
  ([(0 : Int), 1, MAX / 86400 - 1, MAX / 86400, MAX / 86400 + 1, MAX].map fun x => mkE "unitMath(uint256)" [.int x] s!"{x}") ++
  ([0, 1, 31, 32, 33, 100].map fun n => mkE "callData(uint256,bytes)" [.int MAX, .bytes (bytesN n)] s!"{n}")

/-! ## Hash -/

def mkH (sig : String) (args : List Solm.Value) (tag : String := "") : Case := mk hashRuntime sig args tag

def hashCases : List Case :=
  [ { mkH "hashAll(bytes)" [.bytes (bytesN 5)] with expect := .success },
    { mkH "packed(uint8,int16,address,bool,bytes3)" [.int 200, .int (-2), A, .bool true, fb 2 0x010203] with expect := .success },
    { mkH "packedDyn(string,bytes,int8)" [str 5, .bytes (bytesN 3), .int (-1)] with expect := .success },
    { mkH "packedArr(uint16[],uint8)" [.array [.int 1, .int 65535], .int 9] with expect := .success },
    { mkH "strEq(string,string)" [str 3, str 3] "same" with expect := .success },
    mkH "strEq(string,string)" [str 3, str 4] "other",
    { mkH "pair(bytes32,bytes32)" [fb 31 1, fb 31 2] with expect := .success },
    { mkH "litHash()" [] with expect := .success } ]

def hashBoundaries : List Case :=
  ([0, 1, 31, 32, 33, 55, 56, 64, 100, 200].map fun n => mkH "hashAll(bytes)" [.bytes (bytesN n)] s!"{n}") ++
  [ mkH "packed(uint8,int16,address,bool,bytes3)" [.int 0, .int (-32768), .address (addr 0), .bool false, fb 2 0] "zero",
    mkH "packed(uint8,int16,address,bool,bytes3)" [.int 255, .int 32767, .address (addr (2 ^ 160 - 1)), .bool true, fb 2 0xffffff] "max",
    mkH "packedDyn(string,bytes,int8)" [str 0, .bytes (bytesN 0), .int 127] "empty",
    mkH "packedDyn(string,bytes,int8)" [str 40, .bytes (bytesN 33), .int (-128)] "long",
    mkH "packedArr(uint16[],uint8)" [.array [], .int 0] "empty",
    mkH "packedArr(uint16[],uint8)" [.array [.int 0, .int 1, .int 2, .int 3], .int 255] "four",
    mkH "strEq(string,string)" [str 0, str 0] "empty", mkH "strEq(string,string)" [str 40, str 40] "long",
    mkH "pair(bytes32,bytes32)" [fb 31 0, fb 31 (2 ^ 256 - 1)] "edge" ]

/-! ## Rip -/

/-- Whether the EVM model's ripemd160 precompile works here: it runs a Python script that is found
    only when the harness is started in the `evmlean` package directory. -/
def ripAvailable : Bool :=
  match _root_.RIP160 "abc".toUTF8 with
  | .ok out => hexOfBytes out == "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
  | .error _ => false

def ripCases : List Case :=
  if ripAvailable then
    [ { mk ripRuntime "ripLit()" [] with expect := .success } ] ++
    [0, 1, 55, 56, 100].map fun n => mk ripRuntime "rip(bytes)" [.bytes (bytesN n)] s!"{n}"
  else []

/-! ## AbiC -/

def mkA (sig : String) (args : List Solm.Value) (tag : String := "") : Case := mk abiRuntime sig args tag

def tP : ABI.ABIType := .tuple [tU 128, .elem .bool]
def tQ : ABI.ABIType := .tuple [tU 256, .string, .dynamicArray (tU 8)]
def vP : Solm.Value := .tuple [.int 9, .bool true]
def vQ : Solm.Value := .tuple [.int 5, str 33, .array [.int 1, .int 2, .int 3]]

def abiCases : List Case :=
  [ { mkA "enc(uint256,int8,address,bool,bytes4,uint8)" [.int 7, .int (-3), A, .bool true, fb 3 0x12345678, .int 2]
        with expect := .success },
    { mkA "encDyn(string,bytes,uint256[])" [str 5, .bytes (bytesN 40), .array [.int 1, .int 2, .int 3]] with expect := .success },
    { mkA "encStruct(uint128,bool,string)" [.int 9, .bool true, str 33] with expect := .success },
    { mkA "encNested(uint256)" [.int 7] with expect := .success },
    { mkA "encSel(uint256,address)" [.int 5, A] with expect := .success },
    { mkA "encCall(uint256,address,string)" [.int 5, A, str 3] with expect := .success },
    { mkA "dec(bytes)" [.bytes (w 7 ++ w 0xA11CE ++ w 1)] with expect := .success },
    { mkA "decSmall(bytes)" [.bytes (w 255 ++ w (-5) ++ w (0x12345678 * 2 ^ 224) ++ w 2)] with expect := .success },
    { mkA "decDyn(bytes)" [.bytes (encOf [.string, .dynamicArray (tU 256)] [str 5, .array [.int 1, .int 2]])]
        with expect := .success },
    { mkA "decStruct(bytes)" [.bytes (encOf [tP, tQ] [vP, vQ])] with expect := .success },
    { mkA "roundTrip(uint256,string,int8)" [.int 5, str 40, .int (-7)] with expect := .success },
    { mkA "concatB(bytes,bytes4,bytes)" [.bytes (bytesN 3), fb 3 0xdeadbeef, .bytes (bytesN 40)] with expect := .success },
    { mkA "concatS(string,string)" [str 3, str 4] with expect := .success } ]

def abiBoundaries : List Case :=
  [ mkA "encDyn(string,bytes,uint256[])" [str 0, .bytes (bytesN 0), .array []] "empty",
    mkA "encDyn(string,bytes,uint256[])" [str 32, .bytes (bytesN 31), .array [.int MAX]] "edge",
    mkA "encStruct(uint128,bool,string)" [.int (2 ^ 128 - 1), .bool false, str 0] "edge",
    { mkA "dec(bytes)" [.bytes (w 7 ++ w 0xA11CE)] "short" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (w 7 ++ w (2 ^ 160) ++ w 1)] "dirty address" with expect := .revert },
    { mkA "dec(bytes)" [.bytes (w 7 ++ w 0xA11CE ++ w 2)] "bool 2" with expect := .revert },
    mkA "dec(bytes)" [.bytes (w 7 ++ w 0xA11CE ++ w 1 ++ w 99)] "long",
    { mkA "decSmall(bytes)" [.bytes (w 256 ++ w (-5) ++ w (0x12345678 * 2 ^ 224) ++ w 2)] "uint8 256" with expect := .revert },
    { mkA "decSmall(bytes)" [.bytes (w 255 ++ w (2 ^ 15) ++ w (0x12345678 * 2 ^ 224) ++ w 2)] "int16 high" with expect := .revert },
    { mkA "decSmall(bytes)" [.bytes (w 255 ++ w (-5) ++ w (0x12345678 * 2 ^ 224 + 1) ++ w 2)] "bytes4 dirty" with expect := .revert },
    { mkA "decSmall(bytes)" [.bytes (w 255 ++ w (-5) ++ w (0x12345678 * 2 ^ 224) ++ w 3)] "enum 3" with expect := .revert },
    mkA "decSmall(bytes)" [.bytes (w 0 ++ w (-32768) ++ w 0 ++ w 0)] "low",
    mkA "decDyn(bytes)" [.bytes (encOf [.string, .dynamicArray (tU 256)] [str 0, .array []])] "empty",
    { mkA "decDyn(bytes)" [.bytes (w 0x40 ++ w 0x1000 ++ w 0)] "bad offset" with expect := .revert },
    { mkA "decDyn(bytes)" [.bytes (bytesN 0)] "no data" with expect := .revert },
    { mkA "decStruct(bytes)" [.bytes (w 9 ++ w 2 ++ w 0x60)] "bool 2" with expect := .revert },
    mkA "roundTrip(uint256,string,int8)" [.int MAX, str 0, .int (-128)] "edge",
    mkA "concatB(bytes,bytes4,bytes)" [.bytes (bytesN 0), fb 3 0, .bytes (bytesN 0)] "empty",
    mkA "concatB(bytes,bytes4,bytes)" [.bytes (bytesN 32), fb 3 0xffffffff, .bytes (bytesN 31)] "edge",
    mkA "concatS(string,string)" [str 0, str 0] "empty", mkA "concatS(string,string)" [str 40, str 31] "long",
    mkA "enc(uint256,int8,address,bool,bytes4,uint8)" [.int MAX, .int (-128), .address (addr 0), .bool false, fb 3 0, .int 0] "edge" ] ++
  ([(0 : Int), 1, 2, 3, MAX].map fun n => mkA "encNested(uint256)" [.int n] s!"{n}")

/-! ## AbiFixed -/

def fixedCases : List Case :=
  [ { mk fixedRuntime "encFixed(uint256,uint8)" [.int 5, .int 9] with expect := .success },
    { mk fixedRuntime "decFixed(bytes)" [.bytes (w 5 ++ w 6)] with expect := .success },
    { mk fixedRuntime "decFixed(bytes)" [.bytes (w 5)] "short" with expect := .revert },
    { mk fixedRuntime "encW(uint8)" [.int 3] with expect := .success },
    mk fixedRuntime "encFixed(uint256,uint8)" [.int MAX, .int 0] "overflow" ]

/-! ## TypeInfo -/

def mkT (sig : String) (args : List Solm.Value) (tag : String := "") : Case := mk typeRuntime sig args tag

def typeCases : List Case :=
  [ { mkT "names()" [] with expect := .success }, { mkT "ids()" [] with expect := .success },
    { mkT "topics()" [] with expect := .success }, { mkT "codes()" [] with expect := .success },
    { mkT "limits()" [] with expect := .success }, { mkT "make(uint256)" [.int 5] with expect := .success },
    { mkT "viaType(uint256)" [.int 6] with expect := .success }, { mkT "viaRef(uint256)" [.int 6] with expect := .success },
    mkT "viaType(uint256)" [.int MAX] "overflow",
    mkT "total()" [], mkT "bal(address)" [A], mkT "ext(uint256)" [.int 3] ]

/-! ## Conv -/

def mkC (sig : String) (args : List Solm.Value) (tag : String := "") : Case := mk convRuntime sig args tag

def convCases : List Case :=
  [ { mkC "ints(uint256,int256)" [.int 300, .int (-200)] with expect := .success },
    { mkC "widen(uint8,int8)" [.int 200, .int (-100)] with expect := .success },
    { mkC "fixedB(bytes32,bytes4)" [fb 31 (2 ^ 256 - 0x1234), fb 3 0x12345678] with expect := .success },
    { mkC "fixedU(uint32,uint256)" [.int 0xdeadbeef, .int MAX] with expect := .success },
    { mkC "fixedWiden(bytes2)" [fb 1 0xabcd] with expect := .success },
    { mkC "addrs(address,uint160,bytes20)" [A, .int (2 ^ 160 - 1), fb 19 0xB0B] with expect := .success },
    { mkC "addrWords(address,uint256)" [A, .int MAX] with expect := .success },
    { mkC "addrLits()" [] with expect := .success },
    { mkC "enums(uint8,uint256)" [.int 2, .int 1] with expect := .success },
    { mkC "enumSigned(int8)" [.int 2] with expect := .success },
    { mkC "byteStr(string)" [str 3] with expect := .success },
    { mkC "bytesFixed(bytes)" [.bytes (bytesN 5)] with expect := .success },
    { mkC "lits()" [] with expect := .success }, { mkC "litConvs()" [] with expect := .success },
    { mkC "contracts(address)" [A] with expect := .success },
    { mkC "overload(uint8)" [.int 7] with expect := .success },
    { mkC "bools(uint256)" [.int 5] with expect := .success } ]

def U : List Int := [0, 1, 127, 128, 255, 256, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 127, 2 ^ 255 - 1, 2 ^ 255, MAX]
def I : List Int := [0, 1, -1, 127, 128, -128, -129, 2 ^ 127 - 1, 2 ^ 127, -(2 ^ 127), -(2 ^ 127) - 1, 2 ^ 255 - 1, -(2 ^ 255)]

def convBoundaries : List Case :=
  (U.flatMap fun a => I.map fun b => mkC "ints(uint256,int256)" [.int a, .int b] s!"{a} {b}") ++
  ([(0 : Int), 1, 127, 128, 255].flatMap fun a => [(0 : Int), 1, -1, 127, -128].map fun b =>
    mkC "widen(uint8,int8)" [.int a, .int b] s!"{a} {b}") ++
  ([0, 1, 2 ^ 255, 2 ^ 256 - 1].flatMap fun a => [0, 1, 0x80000000, 0xffffffff].map fun b =>
    mkC "fixedB(bytes32,bytes4)" [fb 31 a, fb 3 b] s!"{a} {b}") ++
  ([(0 : Int), 1, 2 ^ 32 - 1].flatMap fun c => [(0 : Int), 1, MAX].map fun d =>
    mkC "fixedU(uint32,uint256)" [.int c, .int d] s!"{c} {d}") ++
  ([0, 1, 0xff00, 0xffff].map fun a => mkC "fixedWiden(bytes2)" [fb 1 a] s!"{a}") ++
  ([0, 1, 2 ^ 160 - 1].flatMap fun a => [(0 : Int), 1, 2 ^ 160 - 1].map fun u =>
    mkC "addrs(address,uint160,bytes20)" [.address (addr a), .int u, fb 19 (2 ^ 160 - 1 - a)] s!"{a} {u}") ++
  ([(0 : Int), 1, 2 ^ 160 - 1, 2 ^ 160, MAX].map fun x => mkC "addrWords(address,uint256)" [.address (addr 0), .int x] s!"{x}") ++
  ([(0 : Int), 1, 2, 3, 255].flatMap fun x => [(0 : Int), 2, 3, 256, MAX].map fun y =>
    mkC "enums(uint8,uint256)" [.int x, .int y] s!"{x} {y}") ++
  ([(0 : Int), 1, 2, 3, 127, -1, -128].map fun z => mkC "enumSigned(int8)" [.int z] s!"{z}") ++
  ([0, 1, 2, 3, 40].map fun n => mkC "byteStr(string)" [str n] s!"{n}") ++
  ([0, 1, 3, 4, 5, 31, 32, 33, 64].map fun n => mkC "bytesFixed(bytes)" [.bytes (bytesN n)] s!"{n}") ++
  ([(0 : Int), 1, 255].map fun a => mkC "overload(uint8)" [.int a] s!"{a}") ++
  ([(0 : Int), 1, MAX].map fun a => mkC "bools(uint256)" [.int a] s!"{a}") ++
  [mkC "contracts(address)" [.address (addr 0)] "zero", mkC "contracts(address)" [.address (addr 0xC0FFEE)] "self"]

/-! ## MemOps -/

def mkM (sig : String) (args : List Solm.Value) (tag : String := "") : Case := mk memRuntime sig args tag

/-- Slot of `blob` holding `n < 32` bytes `1, 2, …, n` (short form). -/
def shortBlob (n : Nat) : UInt256 := word (natOfBytes (bytesN n ++ ⟨(List.replicate (31 - n) (0 : UInt8)).toArray⟩) * 256 + 2 * n)

/-- Storage of a `blob` holding `n ≥ 32` bytes `1, 2, …, n` (long form, slot 1). -/
def longBlob (n : Nat) : List (UInt256 × UInt256) :=
  let base := natOfBytes (Ethereum.KEC (wordBytes 1))
  (word 1, word (2 * n + 1)) :: (List.range ((n + 31) / 32)).map fun i =>
    let chunk := (bytesN n).extract (32 * i) (32 * i + 32)
    (word (base + i), word (natOfBytes (chunk ++ ⟨(List.replicate (32 - chunk.size) (0 : UInt8)).toArray⟩)))

def memCases : List Case :=
  [ { mkM "delMem(uint256)" [.int 7] with expect := .success },
    { mkM "pushRef(uint256)" [.int 5] with expect := .success },
    { mkM "pushRef(uint256)" [.int 5] "arr of 2" with storage := [(word 0, word 2), (word 2, word 1)], expect := .success },
    { mkM "blobOps(bytes1)" [fb 0 0xaa] with expect := .success },
    mkM "arr(uint256)" [.int 0], mkM "blob()" [], mkM "recs(uint256)" [.int 0] ]

def memBoundaries : List Case :=
  ([(0 : Int), 1, 2, MAX - 1, MAX].map fun x => mkM "delMem(uint256)" [.int x] s!"{x}") ++
  ([(0 : Int), MAX].map fun x => mkM "pushRef(uint256)" [.int x] s!"{x}") ++
  ([1, 28, 29, 30, 31].map fun n =>
    { mkM "blobOps(bytes1)" [fb 0 0xaa] s!"short {n}" with storage := [(word 1, shortBlob n)] }) ++
  ([32, 33, 63, 64, 65].map fun n => { mkM "blobOps(bytes1)" [fb 0 0] s!"long {n}" with storage := longBlob n }) ++
  [ { mkM "blob()" [] "short 31" with storage := [(word 1, shortBlob 31)] },
    { mkM "blob()" [] "long 40" with storage := longBlob 40 } ]

/-! ## RetUser -/

/-- A callee whose return data announces `len` elements (or bytes) and holds one word. -/
def mkR (sig : String) (len : Nat) : Case :=
  { mk retRuntime sig [.address (addr 0xBAD)] s!"{len}" with
    accounts := [(addr 0xBAD, account (code := retBadRuntime) (storage := [(word 0, word len)]))] }

/-- Return data that cannot be decoded: empty revert data for a length beyond the data, `Panic(0x41)`
    once the decoder's allocation overflows. -/
def retCases : List Case :=
  [ { mkR "fetch(address)" 1 with expect := .success }, { mkR "fetch(address)" 2 with expect := .revert },
    { mkR "fetchStr(address)" 32 with expect := .success }, { mkR "fetchStr(address)" 33 with expect := .revert } ] ++
  ([2 ^ 32, 2 ^ 59 - 3, 2 ^ 59, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 255].flatMap fun n =>
    [mkR "fetch(address)" n, mkR "tryFetch(address)" n, mkR "fetchStr(address)" n]) ++
  [mkR "tryFetch(address)" 1, mkR "tryFetch(address)" 2]

/-! ## StoreStr -/

/-- Storage of a `bytes` / `string` variable at `slot` holding the `n` bytes `1, 2, …, n`. -/
def blobStorage (slot n : Nat) : List (UInt256 × UInt256) :=
  if n < 32 then [(word slot, shortBlob n)]
  else
    let base := natOfBytes (Ethereum.KEC (wordBytes slot))
    (word slot, word (2 * n + 1)) :: (List.range ((n + 31) / 32)).map fun i =>
      let chunk := (bytesN n).extract (32 * i) (32 * i + 32)
      (word (base + i), word (natOfBytes (chunk ++ ⟨(List.replicate (32 - chunk.size) (0 : UInt8)).toArray⟩)))

/-- `sname` of `a` bytes (slot 0), `sblob` of `b` bytes (slot 1), `rec = R(9, <a bytes>)` (slots 2, 3)
    and `nums = [7, 8]` (slot 4). -/
def mkS (sig : String) (args : List Solm.Value) (a b : Nat) : Case :=
  { mk strRuntime sig args s!"{a} {b}" with
    storage := blobStorage 0 a ++ blobStorage 1 b ++ [(word 2, word 9)] ++ blobStorage 3 a ++
      [(word 4, word 2), (word (natOfBytes (Ethereum.KEC (wordBytes 4))), word 7),
       (word (natOfBytes (Ethereum.KEC (wordBytes 4)) + 1), word 8)] }

def strCases : List Case :=
  [ { mkS "hashes()" [] 5 3 with expect := .success }, { mkS "cat()" [] 5 3 with expect := .success },
    { mkS "first()" [] 5 3 with expect := .success }, { mkS "pass()" [] 5 3 with expect := .success },
    { mkS "eq(string)" [.bytes (bytesN 5)] 5 3 with expect := .success }, mkS "eq(string)" [.bytes (bytesN 4)] 5 3,
    { mkS "enc()" [] 5 3 with expect := .success }, { mkS "fixedOf()" [] 5 3 with expect := .success },
    mkS "sname()" [] 5 3, mkS "sblob()" [] 5 3, mkS "rec()" [] 5 3, mkS "nums(uint256)" [.int 1] 5 3 ]

def strBoundaries : List Case :=
  ([(0, 0), (31, 31), (32, 32), (40, 33), (0, 40), (64, 0)].flatMap fun (a, b) =>
    [mkS "hashes()" [] a b, mkS "cat()" [] a b, mkS "first()" [] a b, mkS "pass()" [] a b,
     mkS "eq(string)" [.bytes (bytesN a)] a b, mkS "enc()" [] a b, mkS "fixedOf()" [] a b]) ++
  -- an inconsistent encoding (long form with a short length): `Panic(0x22)`
  [ { mk strRuntime "hashes()" [] "bad name" with storage := [(word 0, word 1)], expect := .revert },
    { mk strRuntime "cat()" [] "bad blob" with storage := [(word 1, word 1)], expect := .revert },
    { mk strRuntime "pass()" [] "bad name" with storage := [(word 0, word 63)], expect := .revert },
    { mk strRuntime "enc()" [] "bad rec.s" with storage := [(word 3, word 1)], expect := .revert },
    { mk strRuntime "fixedOf()" [] "bad blob" with storage := [(word 1, word 1)], expect := .revert } ]

/-! ## Scenarios -/

open _root_.Builtins.SoliditySpec in
def scenarios : List Scenario :=
  [ { name := "Env", program := envProgram, target := "Env", cases := envCases },
    { name := "Env/boundaries", program := envProgram, target := "Env", cases := envBoundaries },
    { name := "Hash", program := hashProgram, target := "Hash", cases := hashCases },
    { name := "Hash/boundaries", program := hashProgram, target := "Hash", cases := hashBoundaries },
    { name := "Rip/precompile", program := ripProgram, target := "Rip", cases := ripCases },
    { name := "AbiC", program := abiProgram, target := "AbiC", cases := abiCases },
    { name := "AbiC/boundaries", program := abiProgram, target := "AbiC", cases := abiBoundaries },
    { name := "AbiFixed/arrays", program := fixedProgram, target := "AbiFixed", cases := fixedCases },
    { name := "TypeInfo", program := typeProgram, target := "TypeInfo", cases := typeCases,
      creations := [("Small", smallCreation), ("ODer", oDerCreation)], runtimes := [("Small", smallRuntime)] },
    { name := "Conv", program := convProgram, target := "Conv", cases := convCases },
    { name := "Conv/boundaries", program := convProgram, target := "Conv", cases := convBoundaries },
    { name := "MemOps", program := memProgram, target := "MemOps", cases := memCases },
    { name := "MemOps/boundaries", program := memProgram, target := "MemOps", cases := memBoundaries },
    { name := "RetUser/decode", program := retProgram, target := "RetUser", cases := retCases },
    { name := "StoreStr", program := strProgram, target := "StoreStr", cases := strCases },
    { name := "StoreStr/boundaries", program := strProgram, target := "StoreStr", cases := strBoundaries } ]

end Solidity.Test.Builtins
