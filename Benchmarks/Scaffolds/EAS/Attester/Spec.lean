import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.Scaffolds.EAS.Attester.Immutables

/-!
# EAS Attester benchmark spec

Source-shaped Solm benchmark scaffold for the EAS example `Attester` contract at Solidity
`0.8.26`. The contract has no storage; its constructor data is the immutable `_eas` address,
modeled in `Immutables.lean` and used as the receiver for the four EAS interface calls.

Events and custom-error payloads are omitted, as in the other benchmark specs. The no-return EAS
calls (`revoke`, `multiRevoke`) include solc's `EXTCODESIZE` guard; the return-valued calls rely on
the generated return decoder and therefore do not have an explicit code-size guard in the bytecode.
-/

open Solm ABI
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## Types -/

def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint64 : ABIType := .elem (.int uint64Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def bytes32Array : ABIType := .dynamicArray bytes32
def uint256Array : ABIType := .dynamicArray uint256
def uint256NestedArray : ABIType := .dynamicArray uint256Array
def bytes32NestedArray : ABIType := .dynamicArray bytes32Array

def uint64St : StorageType := .elem (.int uint64Int)
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def zeroAddr : Expr := .cast (.intLit 0) addrSt
def zeroBytes32 : Expr := .cast (.intLit 0) bytes32St

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)

def localRef (name : Ident) : StorageRef := { base := name }
def localIndex (name : Ident) (idx : Expr) : StorageRef :=
  { base := name, steps := [.aindex idx] }

def lenLocal (name : Ident) : Expr :=
  .arrayLength .localVar (localRef name)

def arrGet (name : Ident) (idx : Expr) : Expr :=
  .index (.var name) idx

def arrSet (name : Ident) (idx value : Expr) : Stmt :=
  .assign .localVar (localIndex name idx) value

/-! ## EAS ABI tuple shapes -/

def attestationRequestDataTy : ABIType :=
  .tuple [addr, uint64, boolTy, bytes32, bytesTy, uint256]

def attestationRequestTy : ABIType :=
  .tuple [bytes32, attestationRequestDataTy]

def multiAttestationRequestTy : ABIType :=
  .tuple [bytes32, .dynamicArray attestationRequestDataTy]

def revocationRequestDataTy : ABIType :=
  .tuple [bytes32, uint256]

def revocationRequestTy : ABIType :=
  .tuple [bytes32, revocationRequestDataTy]

def multiRevocationRequestTy : ABIType :=
  .tuple [bytes32, .dynamicArray revocationRequestDataTy]

def attestationRequestDataSt : StorageType :=
  .tuple [addrSt, uint64St, boolSt, bytes32St, .bytes, uint256St]

def attestationRequestSt : StorageType :=
  .tuple [bytes32St, attestationRequestDataSt]

def multiAttestationRequestSt : StorageType :=
  .tuple [bytes32St, .dynamicArray attestationRequestDataSt]

def revocationRequestDataSt : StorageType :=
  .tuple [bytes32St, uint256St]

def revocationRequestSt : StorageType :=
  .tuple [bytes32St, revocationRequestDataSt]

def multiRevocationRequestSt : StorageType :=
  .tuple [bytes32St, .dynamicArray revocationRequestDataSt]

def multiAttestationRequestArrayTy : ABIType :=
  .dynamicArray multiAttestationRequestTy

def multiRevocationRequestArrayTy : ABIType :=
  .dynamicArray multiRevocationRequestTy

/-! ## External ABI -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def attestSelector : ByteArray := selectorBytes 0xf1 0x73 0x25 0xe7
def revokeSelector : ByteArray := selectorBytes 0x46 0x92 0x62 0x67
def multiAttestSelector : ByteArray := selectorBytes 0x44 0xad 0xc9 0x0e
def multiRevokeSelector : ByteArray := selectorBytes 0x4c 0xb7 0xe9 0xe5
def abiEncodeUint256Selector : ByteArray := selectorBytes 0x00 0x00 0x00 0x00

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValue? ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def attesterExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "attest" then
      ABI.encodeCallWithSelector? attestSelector [attestationRequestTy] args
    else if name = "revoke" then
      ABI.encodeCallWithSelector? revokeSelector [revocationRequestTy] args
    else if name = "multiAttest" then
      ABI.encodeCallWithSelector? multiAttestSelector [multiAttestationRequestArrayTy] args
    else if name = "multiRevoke" then
      ABI.encodeCallWithSelector? multiRevokeSelector [multiRevocationRequestArrayTy] args
    else if name = "__abi_encode_uint256" then
      ABI.encodeCallWithSelector? abiEncodeUint256Selector [uint256] args
    else
      none
  decode? := fun name out =>
    if name = "attest" then
      decodeReturn? bytes32 out
    else if name = "multiAttest" then
      decodeReturn? bytes32Array out
    else if name = "revoke" || name = "multiRevoke" then
      decodeVoid? out
    else
      none

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl := []

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0))]

def abiEncodeUint256 (e : Expr) : Expr :=
  .bytesSlice (.abiEncodeCall "__abi_encode_uint256" [e]) (.intLit 4) (.intLit 36)

def easCall (v : AttesterImmutables) (name : Ident) (args : List Expr) (retVar : Ident) : Stmt :=
  .externalCall (easExpr v) name (.intLit 0) args retVar

def checkedEASCallStmts (v : AttesterImmutables) (name : Ident)
    (args : List Expr) (retVar : Ident) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)),
    easCall v name args retVar ]

def attestationData (input : Expr) : Expr :=
  .tupleLit [zeroAddr, .intLit 0, .boolLit true, zeroBytes32, abiEncodeUint256 input, .intLit 0]

def attestationRequest (schema input : Expr) : Expr :=
  .tupleLit [schema, attestationData input]

def revocationData (uid : Expr) : Expr :=
  .tupleLit [uid, .intLit 0]

def revocationRequest (schema uid : Expr) : Expr :=
  .tupleLit [schema, revocationData uid]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "eas", ty := addr }]
    body :=
      nonpayable ++
      [ .require (.binary .ne (.var "eas") zeroAddr),
        .letDecl "imm_eas" (some addr) (.var "eas") ] }

/-! ## Public ABI surface -/

def attestTransition (v : AttesterImmutables) : TransitionDecl :=
  { name := "attest"
    params := [{ name := "schema", ty := bytes32 }, { name := "input", ty := uint256 }]
    returnType := [bytes32]
    body :=
      nonpayable ++
      [ easCall v "attest" [attestationRequest (.var "schema") (.var "input")] "uid",
        .return [.var "uid"] ] }

def revokeTransition (v : AttesterImmutables) : TransitionDecl :=
  { name := "revoke"
    params := [{ name := "schema", ty := bytes32 }, { name := "uid", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      checkedEASCallStmts v "revoke" [revocationRequest (.var "schema") (.var "uid")] "_revoke" }

def multiAttestTransition (v : AttesterImmutables) : TransitionDecl :=
  { name := "multiAttest"
    params :=
      [ { name := "schemas", ty := bytes32Array },
        { name := "schemaInputs", ty := uint256NestedArray } ]
    returnType := [bytes32Array]
    body :=
      nonpayable ++
      [ .letDecl "schemaLength" (some uint256) (lenLocal "schemas"),
        .require
          (.binary .and
            (.binary .ne (.var "schemaLength") (.intLit 0))
            (.binary .eq (.var "schemaLength") (lenLocal "schemaInputs"))),
        .letDecl "multiRequests" (some multiAttestationRequestArrayTy)
          (.newArray multiAttestationRequestSt (.var "schemaLength")),
        .letDecl "i" (some uint256) (.intLit 0),
        .while (.binary .lt (.var "i") (.var "schemaLength"))
          [ .letDecl "inputs" (some uint256Array) (arrGet "schemaInputs" (.var "i")),
            .letDecl "inputLength" (some uint256) (lenLocal "inputs"),
            .require (.binary .ne (.var "inputLength") (.intLit 0)),
            .letDecl "data" (some (.dynamicArray attestationRequestDataTy))
              (.newArray attestationRequestDataSt (.var "inputLength")),
            .letDecl "j" (some uint256) (.intLit 0),
            .while (.binary .lt (.var "j") (.var "inputLength"))
              [ arrSet "data" (.var "j") (attestationData (arrGet "inputs" (.var "j"))),
                .assign .localVar (localRef "j") (add256 (.var "j") (.intLit 1)) ],
            arrSet "multiRequests" (.var "i")
              (.tupleLit [arrGet "schemas" (.var "i"), .var "data"]),
            .assign .localVar (localRef "i") (add256 (.var "i") (.intLit 1)) ],
        easCall v "multiAttest" [.var "multiRequests"] "uids",
        .return [.var "uids"] ] }

def multiRevokeTransition (v : AttesterImmutables) : TransitionDecl :=
  { name := "multiRevoke"
    params :=
      [ { name := "schemas", ty := bytes32Array },
        { name := "schemaUids", ty := bytes32NestedArray } ]
    returnType := []
    body :=
      nonpayable ++
      [ .letDecl "schemaLength" (some uint256) (lenLocal "schemas"),
        .require
          (.binary .and
            (.binary .ne (.var "schemaLength") (.intLit 0))
            (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))),
        .letDecl "multiRequests" (some multiRevocationRequestArrayTy)
          (.newArray multiRevocationRequestSt (.var "schemaLength")),
        .letDecl "i" (some uint256) (.intLit 0),
        .while (.binary .lt (.var "i") (.var "schemaLength"))
          [ .letDecl "uids" (some bytes32Array) (arrGet "schemaUids" (.var "i")),
            .letDecl "uidLength" (some uint256) (lenLocal "uids"),
            .require (.binary .ne (.var "uidLength") (.intLit 0)),
            .letDecl "data" (some (.dynamicArray revocationRequestDataTy))
              (.newArray revocationRequestDataSt (.var "uidLength")),
            .letDecl "j" (some uint256) (.intLit 0),
            .while (.binary .lt (.var "j") (.var "uidLength"))
              [ arrSet "data" (.var "j") (revocationData (arrGet "uids" (.var "j"))),
                .assign .localVar (localRef "j") (add256 (.var "j") (.intLit 1)) ],
            arrSet "multiRequests" (.var "i")
              (.tupleLit [arrGet "schemas" (.var "i"), .var "data"]),
            .assign .localVar (localRef "i") (add256 (.var "i") (.intLit 1)) ],
      ] ++
      checkedEASCallStmts v "multiRevoke" [.var "multiRequests"] "_multiRevoke" }

def transitions (v : AttesterImmutables) : List TransitionDecl :=
  [ attestTransition v,
    multiAttestTransition v,
    multiRevokeTransition v,
    revokeTransition v ]

def contract (v : AttesterImmutables) : ContractDecl :=
  { name := "Attester"
    storage := storageDecls
    ctor := constructorDecl
    functions := []
    transitions := transitions v }

def config (_v : AttesterImmutables) : Config :=
  { storage := storageLayout
    externalABI := attesterExternalABI
    selfDeployment := genSolidityConstructorDeployment constructorDecl.params }

end Benchmarks.EAS.Attester
