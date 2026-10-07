import Benchmarks.EAS.Attester.SpecSyntax
import Benchmarks.EAS.Attester.Immutables
import Solm.SolidityStorage
import Solm.Semantics
import Solm.SolidityLayout

/-!
# EAS Attester specification assembly

`SpecSyntax.lean` is the single authoritative contract body. This module derives its transition
handles and supplies the EAS ABI, empty storage backend, and Solidity constructor-argument codec.
-/

open Solm ABI

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

/-! ## Derived contract and proof handles -/

def contract : ContractDecl := Syntax.contractSyntax
abbrev constructorDecl : ConstructorDecl := contract.ctor
abbrev attestTransition : TransitionDecl := contract.transitions[0]!
abbrev multiAttestTransition : TransitionDecl := contract.transitions[1]!
abbrev multiRevokeTransition : TransitionDecl := contract.transitions[2]!
abbrev revokeTransition : TransitionDecl := contract.transitions[3]!

def storageDecls : List StorageDecl := contract.storage

def storageLayout : StorageLayout := fun _ => none

def config : Config :=
  { storageBackend := solidityStorageBackend storageLayout
    externalABI := attesterExternalABI
    abiDecodeMode := .modern
    selfDeployment := genSolidityConstructorDeployment constructorDecl.params }

end Benchmarks.EAS.Attester
