import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin VestingWallet benchmark spec

Solm specification for `VestingWalletBench`, the concrete payable wrapper with owner `msg.sender`,
start `0`, and duration `365 days`.  Events are omitted.  ERC20 balance reads are static calls;
token release models OpenZeppelin `SafeERC20.safeTransfer` as the raw call plus optional bool
return check used by the compiled bytecode.
-/

open Solm ABI

namespace OpenZeppelinBench.VestingWallet

def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint64 : ABIType := .elem (.int uint64Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def vestingStart : Expr := .intLit 0
def vestingDuration : Expr := .intLit 31536000
def uint64Modulus : Int := (2 : Int) ^ 64

def valueInUInt256 (expr : Expr) : Expr := .inRange uint256Int expr
def wrap64 (expr : Expr) : Expr := .binary .mod expr (.intLit uint64Modulus)

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def balanceOfSelector : ByteArray := selectorBytes 0x70 0xa0 0x82 0x31
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.modern ty out).map (fun v => [v])

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "balanceOf" then
      ABI.encodeCallWithSelector? balanceOfSelector [addr] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "balanceOf" then
      decodeReturn? uint256 out
    else if name = "transfer" then
      decodeReturn? boolTy out
    else
      none

def localRef (name : Ident) : StorageRef := { base := name }

def lenLocal (name : Ident) : Expr :=
  .arrayLength .localVar (localRef name)

def ownerRef : StorageRef := { base := "_owner" }
def releasedRef : StorageRef := { base := "_released" }

def erc20ReleasedRef (token : Expr) : StorageRef :=
  { base := "_erc20Released", steps := [.mindex token] }

def storageDecls : List StorageDecl :=
  [ { name := "_owner", ty := addrSt },
    { name := "_released", ty := uint256St },
    { name := "_erc20Released", ty := .mapping .address uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def erc20ReleasedSlot (token : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord token) ⟨2⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_owner", [] => some (addrLoc ⟨0⟩)
    | "_released", [] => some (wordLoc ⟨1⟩)
    | "_erc20Released", [.mindex token] => some (wordLoc (erc20ReleasedSlot token))
    | _, _ => none

def vestingEnd : Expr :=
  .binary .add vestingStart vestingDuration

def vestingSchedule (totalAllocation timestamp : Expr) : Expr :=
  .ite (.binary .lt timestamp vestingStart)
    (.intLit 0)
    (.ite (.binary .ge timestamp vestingEnd)
      totalAllocation
      (.binary .div
        (valueInUInt256
          (.binary .mul totalAllocation (.binary .sub timestamp vestingStart)))
        vestingDuration))

def nativeTotalAllocation : Expr :=
  valueInUInt256 (.binary .add (.env .selfbalance) (.storage releasedRef))

def tokenTotalAllocation (tokenBalance token : Expr) : Expr :=
  valueInUInt256 (.binary .add tokenBalance (.storage (erc20ReleasedRef token)))

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def requireSafeTransferReturn (token data : Ident) : List Stmt :=
  [ .ite
      (.binary .eq (lenLocal data) (.intLit 0))
      [ .require (.binary .gt (.extCodeSize (.var token)) (.intLit 0)) ]
      [ .letDecl (data ++ "_ok") (some boolTy) (.abiDecode boolTy (.var data)),
        .require (.var (data ++ "_ok")) ] ]

def safeERC20Transfer (token : Ident) (recipient amount : Expr) : List Stmt :=
  [ .letDecl "transferData" (some bytesTy) (.abiEncodeCall "transfer" [recipient, amount]),
    .lowLevelCall (.var token) (.intLit 0) (.var "transferData") "transferSuccess" "transferReturndata",
    .require (.var "transferSuccess") ] ++
  requireSafeTransferReturn token "transferReturndata"

def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [(.storage ownerRef)] ] }

def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage ownerRef) sender),
        .require (.binary .ne (.var "newOwner") zeroAddr),
        .assign .storage ownerRef (.var "newOwner") ] }

def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage ownerRef zeroAddr ] }

def startTransition : TransitionDecl :=
  { name := "start"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [vestingStart] ] }

def durationTransition : TransitionDecl :=
  { name := "duration"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [vestingDuration] ] }

def endTransition : TransitionDecl :=
  { name := "end"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [vestingEnd] ] }

def releasedTransition : TransitionDecl :=
  { name := "released"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage releasedRef)] ] }

def releasedTokenTransition : TransitionDecl :=
  { name := "released"
    params := [{ name := "token", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage (erc20ReleasedRef (.var "token")))] ] }

def vestedAmountTransition : TransitionDecl :=
  { name := "vestedAmount"
    params := [{ name := "timestamp", ty := uint64 }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(vestingSchedule nativeTotalAllocation (.var "timestamp"))] ] }

def vestedAmountTokenTransition : TransitionDecl :=
  { name := "vestedAmount"
    params := [{ name := "token", ty := addr }, { name := "timestamp", ty := uint64 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .externalCall (.var "token") "balanceOf" (.intLit 0) [thisAddr] "tokenBalance" false,
        .return [
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (.var "timestamp"))] ] }

def releasableTransition : TransitionDecl :=
  { name := "releasable"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .letDecl "vested" (some uint256)
          (vestingSchedule nativeTotalAllocation (wrap64 (.env .timestamp))),
        .return [(valueInUInt256 (.binary .sub (.var "vested") (.storage releasedRef)))] ] }

def releasableTokenTransition : TransitionDecl :=
  { name := "releasable"
    params := [{ name := "token", ty := addr }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .externalCall (.var "token") "balanceOf" (.intLit 0) [thisAddr] "tokenBalance" false,
        .letDecl "vested" (some uint256)
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (wrap64 (.env .timestamp))),
        .return [
          (valueInUInt256
            (.binary .sub (.var "vested") (.storage (erc20ReleasedRef (.var "token")))))] ] }

def releaseTransition : TransitionDecl :=
  { name := "release"
    params := []
    returnType := []
    body :=
      nonpayable ++
      [ .letDecl "vested" (some uint256)
          (vestingSchedule nativeTotalAllocation (wrap64 (.env .timestamp))),
        .letDecl "amount" (some uint256)
          (valueInUInt256 (.binary .sub (.var "vested") (.storage releasedRef))),
        .assign .storage releasedRef
          (valueInUInt256 (.binary .add (.storage releasedRef) (.var "amount"))),
        .require (.binary .ge (.env .selfbalance) (.var "amount")),
        .lowLevelCall (.storage ownerRef) (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ] }

def releaseTokenTransition : TransitionDecl :=
  { name := "release"
    params := [{ name := "token", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .externalCall (.var "token") "balanceOf" (.intLit 0) [thisAddr] "tokenBalance" false,
        .letDecl "vested" (some uint256)
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (wrap64 (.env .timestamp))),
        .letDecl "amount" (some uint256)
          (valueInUInt256
            (.binary .sub (.var "vested") (.storage (erc20ReleasedRef (.var "token"))))),
        .assign .storage (erc20ReleasedRef (.var "token"))
          (valueInUInt256
            (.binary .add (.storage (erc20ReleasedRef (.var "token"))) (.var "amount"))) ] ++
      safeERC20Transfer "token" (.storage ownerRef) (.var "amount") }

def receiveTransition : TransitionDecl :=
  { name := "receive"
    params := []
    returnType := []
    body := [] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage ownerRef sender,
        .assign .storage releasedRef (.intLit 0) ] }

def contract : ContractDecl :=
  { name := "VestingWalletBench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ durationTransition,
        endTransition,
        ownerTransition,
        releasableTransition,
        releasableTokenTransition,
        releaseTransition,
        releaseTokenTransition,
        releasedTransition,
        releasedTokenTransition,
        renounceOwnershipTransition,
        startTransition,
        transferOwnershipTransition,
        vestedAmountTokenTransition,
        vestedAmountTransition ]
    receive := some receiveTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.VestingWallet
