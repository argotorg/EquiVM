import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin VestingWallet benchmark spec

Solm specification for `VestingWalletBench`, the concrete payable wrapper with owner `msg.sender`,
start `0`, and duration `365 days`.  Events are omitted.  ERC20 interactions are represented with
Solm external calls; the native-ETH path uses `EnvVar.selfbalance` for `address(this).balance`.
-/

open Solm ABI

namespace OpenZeppelinBench.VestingWallet

def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint64 : ABIType := .elem (.int uint64Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def vestingStart : Expr := .intLit 0
def vestingDuration : Expr := .intLit 31536000

def valueInUInt256 (expr : Expr) : Expr := .inRange uint256Int expr

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

def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := some addr
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage ownerRef) ] }

def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .require (.binary .ne (.var "newOwner") zeroAddr),
        .assign .storage ownerRef (.var "newOwner") ] }

def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage ownerRef zeroAddr ] }

def startTransition : TransitionDecl :=
  { name := "start"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return vestingStart ] }

def durationTransition : TransitionDecl :=
  { name := "duration"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return vestingDuration ] }

def endTransition : TransitionDecl :=
  { name := "end"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return vestingEnd ] }

def releasedTransition : TransitionDecl :=
  { name := "released"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage releasedRef) ] }

def releasedTokenTransition : TransitionDecl :=
  { name := "released"
    params := [{ name := "token", ty := addr }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (erc20ReleasedRef (.var "token"))) ] }

def vestedAmountTransition : TransitionDecl :=
  { name := "vestedAmount"
    params := [{ name := "timestamp", ty := uint64 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (vestingSchedule nativeTotalAllocation (.var "timestamp")) ] }

def vestedAmountTokenTransition : TransitionDecl :=
  { name := "vestedAmount"
    params := [{ name := "token", ty := addr }, { name := "timestamp", ty := uint64 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .externalCall (.var "token") "balanceOf" (.intLit 0) [.env .this] "tokenBalance",
        .return
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (.var "timestamp")) ] }

def releasableTransition : TransitionDecl :=
  { name := "releasable"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "vested" (some uint256)
          (vestingSchedule nativeTotalAllocation (.env .timestamp)),
        .return (valueInUInt256 (.binary .sub (.var "vested") (.storage releasedRef))) ] }

def releasableTokenTransition : TransitionDecl :=
  { name := "releasable"
    params := [{ name := "token", ty := addr }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .externalCall (.var "token") "balanceOf" (.intLit 0) [.env .this] "tokenBalance",
        .letDecl "vested" (some uint256)
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (.env .timestamp)),
        .return
          (valueInUInt256
            (.binary .sub (.var "vested") (.storage (erc20ReleasedRef (.var "token"))))) ] }

def releaseTransition : TransitionDecl :=
  { name := "release"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "vested" (some uint256)
          (vestingSchedule nativeTotalAllocation (.env .timestamp)),
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
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .externalCall (.var "token") "balanceOf" (.intLit 0) [.env .this] "tokenBalance",
        .letDecl "vested" (some uint256)
          (vestingSchedule (tokenTotalAllocation (.var "tokenBalance") (.var "token"))
            (.env .timestamp)),
        .letDecl "amount" (some uint256)
          (valueInUInt256
            (.binary .sub (.var "vested") (.storage (erc20ReleasedRef (.var "token"))))),
        .assign .storage (erc20ReleasedRef (.var "token"))
          (valueInUInt256
            (.binary .add (.storage (erc20ReleasedRef (.var "token"))) (.var "amount"))),
        .externalCall (.var "token") "transfer" (.intLit 0)
          [.storage ownerRef, .var "amount"] "_transferResult" ] }

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
        vestedAmountTransition ] }

def externalABI : ExternalCallABI where
  encode? := defaultEncodeCall?
  decode? := fun name out => if name = "balanceOf" then defaultDecodeReturn? name out else some .unit

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.VestingWallet
