import Solm.Semantics
import Solm.SolidityLayout

/-!
# Compound III CometRewards benchmark spec

Solm benchmark scaffold for Compound III `CometRewards` from the upstream `compound-finance/comet` main branch.

The transition bodies mirror the source-level effects and external ABI calls needed for the
optimized bytecode proof target.
-/

open Solm ABI

namespace Benchmarks.CompoundIII.CometRewards

/-! ## Types -/

def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint64 : ABIType := .elem (.int uint64Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def stringTy : ABIType := .string

def uint64St : StorageType := .elem (.int uint64Int)
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool

def zeroAddr : Expr := .cast (.intLit 0) addrSt
def sender : Expr := .env .caller

def maxUint64 : Int := (2 : Int) ^ 64 - 1
def maxUint256 : Int := (2 : Int) ^ 256 - 1
def factorScale : Int := 1000000000000000000

def u64 (e : Expr) : Expr := .inRange uint64Int e
def u256 (e : Expr) : Expr := .inRange uint256Int e

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def baseAccrualScaleSelector : ByteArray := selectorBytes 0xa2 0x0e 0xd5 0x96
def baseTrackingAccruedSelector : ByteArray := selectorBytes 0xab 0x9b 0xa7 0xf4
def accrueAccountSelector : ByteArray := selectorBytes 0xbf 0xe6 0x9c 0x8d
def decimalsSelector : ByteArray := selectorBytes 0x31 0x3c 0xe5 0x67
def hasPermissionSelector : ByteArray := selectorBytes 0xcd 0xe6 0x80 0x41
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.modern ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def compoundRewardsExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "baseAccrualScale" then
      match args with
      | [] => some baseAccrualScaleSelector
      | _ => none
    else if name = "baseTrackingAccrued" then
      ABI.encodeCallWithSelector? baseTrackingAccruedSelector [addr] args
    else if name = "accrueAccount" then
      ABI.encodeCallWithSelector? accrueAccountSelector [addr] args
    else if name = "decimals" then
      match args with
      | [] => some decimalsSelector
      | _ => none
    else if name = "hasPermission" then
      ABI.encodeCallWithSelector? hasPermissionSelector [addr, addr] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "baseAccrualScale" then
      decodeReturn? uint64 out
    else if name = "baseTrackingAccrued" then
      decodeReturn? uint64 out
    else if name = "accrueAccount" then
      decodeVoid? out
    else if name = "decimals" then
      decodeReturn? (.elem (.int (.uint ⟨8, by decide⟩))) out
    else if name = "hasPermission" then
      decodeReturn? boolTy out
    else if name = "transfer" then
      decodeReturn? boolTy out
    else
      none

/-! ## Storage references -/

def governorRef : StorageRef := { base := "governor" }
def rewardConfigF (comet : Expr) (field : Ident) : StorageRef :=
  { base := "rewardConfig", steps := [.mindex comet, .field field] }

def rewardsClaimedRef (comet account : Expr) : StorageRef :=
  { base := "rewardsClaimed", steps := [.mindex comet, .mindex account] }

/-! ## Storage declarations and layout -/

def RewardConfigStructTy : StorageType :=
  .struct "RewardConfig" [("token", (.elem .address)), ("rescaleFactor", (.elem (.int uint64Int))), ("shouldUpscale", (.elem .bool)), ("multiplier", (.elem (.int uint256Int)))]

def RewardConfigStructDecl : StructDecl :=
  { name := "RewardConfig"
    fields := [{ name := "token", ty := (.elem .address) }, { name := "rescaleFactor", ty := (.elem (.int uint64Int)) }, { name := "shouldUpscale", ty := (.elem .bool) }, { name := "multiplier", ty := (.elem (.int uint256Int)) }] }

def storageDecls : List StorageDecl :=
  [
    { name := "governor", ty := (.elem .address) },
    { name := "rewardConfig", ty := (.mapping .address RewardConfigStructTy) },
    { name := "rewardsClaimed", ty := (.mapping .address (.mapping .address (.elem (.int uint256Int)))) }
  ]

def structs : List StructDecl := [RewardConfigStructDecl]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def slotAdd (slot : Ethereum.UInt256) (n : Nat) : Ethereum.UInt256 :=
  slot + Ethereum.UInt256.ofNat n

def loc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }

def fieldLoc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  loc slot offset size hbound ty

def rewardConfigSlot (comet : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord comet) ⟨1⟩

def rewardsClaimedCometSlot (comet : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord comet) ⟨2⟩

def rewardsClaimedSlot (comet account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) (rewardsClaimedCometSlot comet)

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "governor", steps := [] }, _ =>
      some (fieldLoc ⟨0⟩ 0 20 (by decide) .address)
  | { base := "rewardConfig", steps := [.mindex comet, .field "token"] }, _ =>
      some (fieldLoc (slotAdd (rewardConfigSlot comet) 0) 0 20 (by decide) .address)
  | { base := "rewardConfig", steps := [.mindex comet, .field "rescaleFactor"] }, _ =>
      some (fieldLoc (slotAdd (rewardConfigSlot comet) 0) 20 8 (by decide) (.int uint64Int))
  | { base := "rewardConfig", steps := [.mindex comet, .field "shouldUpscale"] }, _ =>
      some (fieldLoc (slotAdd (rewardConfigSlot comet) 0) 28 1 (by decide) .bool)
  | { base := "rewardConfig", steps := [.mindex comet, .field "multiplier"] }, _ =>
      some (fieldLoc (slotAdd (rewardConfigSlot comet) 1) 0 32 (by decide) (.int uint256Int))
  | { base := "rewardsClaimed", steps := [.mindex comet, .mindex account] }, _ =>
      some (fieldLoc (rewardsClaimedSlot comet account) 0 32 (by decide) (.int uint256Int))
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def calldataSizeLimit : Int := (2 : Int) ^ 255 + 4

def calldataGuardRef : StorageRef := { base := "__calldata" }

def calldataSizeGuard : List Stmt :=
  [ .letDecl "__calldata" (some bytesTy) (.env .msgData),
    .require
      (.binary .lt (.arrayLength .localVar calldataGuardRef) (.intLit calldataSizeLimit)) ]

def externalEntryGuard : List Stmt :=
  nonpayable ++ calldataSizeGuard

def checkedExternalCallStmts (receiver : Expr) (name : Ident) (eth : Expr)
    (args : List Expr) (retVar : Ident) (perm : Bool := true) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
    .externalCall receiver name eth args retVar (perm := perm) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "governor_", ty := addr }]
    body := nonpayable ++ [ .assign .storage governorRef (.var "governor_") ] }

/-! ## Internal helpers -/

def safe64Function : FunctionDecl :=
  { name := "safe64"
    params := [{ name := "n", ty := uint256 }]
    returnType := [uint64]
    body :=
      [ .require (.binary .le (.var "n") (.intLit maxUint64)),
        .return [u64 (.var "n")] ] }

def pow10Function : FunctionDecl :=
  { name := "pow10"
    params := [{ name := "n", ty := (.elem (.int (.uint ⟨8, by decide⟩))) }]
    returnType := [uint256]
    body :=
      [ .require (.binary .le (.var "n") (.intLit 77)),
        .return [u256 (.binary .exp (.intLit 10) (.var "n"))] ] }

def getRewardAccruedFunction : FunctionDecl :=
  { name := "getRewardAccrued"
    params :=
      [ { name := "comet", ty := addr }, { name := "account", ty := addr },
        { name := "rescaleFactor", ty := uint64 }, { name := "shouldUpscale", ty := boolTy },
        { name := "multiplier", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
          [.var "account"] "accrued" false,
        .ite (.var "shouldUpscale")
          [ .assign .localVar { base := "accrued" }
              (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
          [ .assign .localVar { base := "accrued" }
              (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
        .letDecl "scaled" (some uint256)
          (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
        .return [.binary .div (.var "scaled") (.intLit factorScale)] ] }

def doTransferOutFunction : FunctionDecl :=
  { name := "doTransferOut"
    params :=
      [ { name := "token", ty := addr }, { name := "to", ty := addr },
        { name := "amount", ty := uint256 } ]
    returnType := []
    body :=
      [ .externalCall (.var "token") "transfer" (.intLit 0)
          [.var "to", .var "amount"] "success",
        .require (.var "success") ] }

def setRewardConfigWithMultiplierFunction : FunctionDecl :=
  { name := "setRewardConfigWithMultiplierBody"
    params :=
      [ { name := "comet", ty := addr }, { name := "token", ty := addr },
        { name := "multiplier", ty := uint256 } ]
    returnType := []
    body :=
      [ .require (.binary .eq sender (.storage governorRef)),
        .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
        .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
        .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
        .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
        .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
        .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
          [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
            .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
              (.binary .div (.var "accrualScale") (.var "tokenScale")),
            .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
            .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
          [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
            .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
              (.binary .div (.var "tokenScale") (.var "accrualScale")),
            .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
            .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ] }

def claimInternalFunction : FunctionDecl :=
  { name := "claimInternal"
    params :=
      [ { name := "comet", ty := addr }, { name := "src", ty := addr },
        { name := "to", ty := addr }, { name := "shouldAccrue", ty := boolTy } ]
    returnType := []
    body :=
      [ .letDecl "token" (some addr) (.storage (rewardConfigF (.var "comet") "token")),
        .letDecl "rescaleFactor" (some uint64)
          (.storage (rewardConfigF (.var "comet") "rescaleFactor")),
        .letDecl "shouldUpscale" (some boolTy)
          (.storage (rewardConfigF (.var "comet") "shouldUpscale")),
        .letDecl "multiplier" (some uint256)
          (.storage (rewardConfigF (.var "comet") "multiplier")),
        .require (.binary .ne (.var "token") zeroAddr),
        .ite (.var "shouldAccrue")
          (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
            [.var "src"] "_accrued")
          [],
        .letDecl "claimed" (some uint256)
          (.storage (rewardsClaimedRef (.var "comet") (.var "src"))),
        .internalCall "getRewardAccrued"
          [ .var "comet", .var "src", .var "rescaleFactor",
            .var "shouldUpscale", .var "multiplier" ] "accrued",
        .ite (.binary .gt (.var "accrued") (.var "claimed"))
          [ .letDecl "owed" (some uint256) (.binary .sub (.var "accrued") (.var "claimed")),
            .assign .storage (rewardsClaimedRef (.var "comet") (.var "src")) (.var "accrued"),
            .internalCall "doTransferOut" [.var "token", .var "to", .var "owed"] "_sent" ]
          [] ] }

/-! ## Public ABI surface -/

def claimTransition : TransitionDecl :=
  { name := "claim"
    params := [{ name := "comet", ty := addr }, { name := "src", ty := addr }, { name := "shouldAccrue", ty := boolTy }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .internalCall "claimInternal"
          [.var "comet", .var "src", .var "src", .var "shouldAccrue"] "_claim" ] }

def claimToTransition : TransitionDecl :=
  { name := "claimTo"
    params := [{ name := "comet", ty := addr }, { name := "src", ty := addr }, { name := "to", ty := addr }, { name := "shouldAccrue", ty := boolTy }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .externalCall (.var "comet") "hasPermission" (.intLit 0)
          [.var "src", sender] "permitted" false,
        .require (.var "permitted"),
        .internalCall "claimInternal"
          [.var "comet", .var "src", .var "to", .var "shouldAccrue"] "_claim" ] }

def getRewardOwedTransition : TransitionDecl :=
  { name := "getRewardOwed"
    params := [{ name := "comet", ty := addr }, { name := "account", ty := addr }]
    returnType := [(.tuple [addr, uint256])]
    body :=
      externalEntryGuard ++
      [ .letDecl "token" (some addr) (.storage (rewardConfigF (.var "comet") "token")),
        .letDecl "rescaleFactor" (some uint64)
          (.storage (rewardConfigF (.var "comet") "rescaleFactor")),
        .letDecl "shouldUpscale" (some boolTy)
          (.storage (rewardConfigF (.var "comet") "shouldUpscale")),
        .letDecl "multiplier" (some uint256)
          (.storage (rewardConfigF (.var "comet") "multiplier")),
        .require (.binary .ne (.var "token") zeroAddr),
      ] ++
      checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
        [.var "account"] "_accrued" ++
      [
        .letDecl "claimed" (some uint256)
          (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
        .internalCall "getRewardAccrued"
          [ .var "comet", .var "account", .var "rescaleFactor",
            .var "shouldUpscale", .var "multiplier" ] "accrued",
        .letDecl "owed" (some uint256)
          (.ite (.binary .gt (.var "accrued") (.var "claimed"))
            (.binary .sub (.var "accrued") (.var "claimed"))
            (.intLit 0)),
        .return [(.tupleLit [.var "token", .var "owed"])] ] }

def governorTransition : TransitionDecl :=
  { name := "governor"
    params := []
    returnType := [addr]
    body := externalEntryGuard ++ [ .return [.storage governorRef] ] }

def rewardConfigTransition : TransitionDecl :=
  { name := "rewardConfig"
    params := [{ name := "arg0", ty := addr }]
    returnType := [addr, uint64, boolTy, uint256]
    body := externalEntryGuard ++ [ .return [.storage (rewardConfigF (.var "arg0") "token"), .storage (rewardConfigF (.var "arg0") "rescaleFactor"), .storage (rewardConfigF (.var "arg0") "shouldUpscale"), .storage (rewardConfigF (.var "arg0") "multiplier")] ] }

def rewardsClaimedTransition : TransitionDecl :=
  { name := "rewardsClaimed"
    params := [{ name := "arg0", ty := addr }, { name := "arg1", ty := addr }]
    returnType := [uint256]
    body := externalEntryGuard ++ [ .return [.storage (rewardsClaimedRef (.var "arg0") (.var "arg1"))] ] }

def setRewardConfigTransition : TransitionDecl :=
  { name := "setRewardConfig"
    params := [{ name := "comet", ty := addr }, { name := "token", ty := addr }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set" ] }

def setRewardConfigWithMultiplierTransition : TransitionDecl :=
  { name := "setRewardConfigWithMultiplier"
    params := [{ name := "comet", ty := addr }, { name := "token", ty := addr }, { name := "multiplier", ty := uint256 }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set" ] }

def setRewardsClaimedTransition : TransitionDecl :=
  { name := "setRewardsClaimed"
    params := [{ name := "comet", ty := addr }, { name := "users", ty := (.dynamicArray addr) }, { name := "claimedAmounts", ty := (.dynamicArray uint256) }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .require (.binary .eq sender (.storage governorRef)),
        .require
          (.binary .eq
            (.arrayLength .localVar { base := "users" })
            (.arrayLength .localVar { base := "claimedAmounts" })),
        .letDecl "i" (some uint256) (.intLit 0),
        .while (.binary .lt (.var "i") (.arrayLength .localVar { base := "users" }))
          [ .assign .storage
              (rewardsClaimedRef (.var "comet") (.index (.var "users") (.var "i")))
              (.index (.var "claimedAmounts") (.var "i")),
            .assign .localVar { base := "i" }
              (.binary .add (.var "i") (.intLit 1)) ] ] }

def functions : List FunctionDecl :=
  [ safe64Function,
    pow10Function,
    getRewardAccruedFunction,
    doTransferOutFunction,
    setRewardConfigWithMultiplierFunction,
    claimInternalFunction ]

def transferGovernorTransition : TransitionDecl :=
  { name := "transferGovernor"
    params := [{ name := "newGovernor", ty := addr }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .require (.binary .eq sender (.storage governorRef)),
        .assign .storage governorRef (.var "newGovernor") ] }

def withdrawTokenTransition : TransitionDecl :=
  { name := "withdrawToken"
    params := [{ name := "token", ty := addr }, { name := "to", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body :=
      externalEntryGuard ++
      [ .require (.binary .eq sender (.storage governorRef)),
        .internalCall "doTransferOut" [.var "token", .var "to", .var "amount"] "_sent" ] }

def transitions : List TransitionDecl :=
  [ claimTransition,
    claimToTransition,
    getRewardOwedTransition,
    governorTransition,
    rewardConfigTransition,
    rewardsClaimedTransition,
    setRewardConfigTransition,
    setRewardConfigWithMultiplierTransition,
    setRewardsClaimedTransition,
    transferGovernorTransition,
    withdrawTokenTransition ]

def contract : ContractDecl :=
  { name := "CometRewards"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := compoundRewardsExternalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.CompoundIII.CometRewards
