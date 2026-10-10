import Benchmarks.Morpho.MetaMorphoV1_1.Spec
import Reasoning.SolmBody
import Reasoning.ABI

/-! The queue update's two loops and its explicit allocation steps. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def updateWithdrawQueuePost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def updateWithdrawQueueBuildCondition : Expr := .binary .lt (.var "i") (.var "newLength")

def updateWithdrawQueueBuildBody : List Stmt :=
  [.letDecl "prevIndex" (some abiUInt256) (.index (.var "indexes") (.var "i")),
   .letDecl "id" (some abiBytes32)
     (.storage ⟨"withdrawQueue", [.aindex (.var "prevIndex")]⟩),
   .require (.unary .not (.index (.var "seen") (.var "prevIndex"))),
   .assign .localVar ⟨"seen", [.aindex (.var "prevIndex")]⟩ (.boolLit true),
   .assign .localVar ⟨"newWithdrawQueue", [.aindex (.var "i")]⟩ (.var "id")]

def updateWithdrawQueueBuildLoop : Stmt :=
  .for [.letDecl "i" (some abiUInt256) (.intLit 0)]
    updateWithdrawQueueBuildCondition updateWithdrawQueuePost updateWithdrawQueueBuildBody

def updateWithdrawQueueRemoveCondition : Expr := .binary .lt (.var "i") (.var "currLength")

def updateWithdrawQueueUnseenCondition : Expr :=
  .unary .not (.index (.var "seen") (.var "i"))

def updateWithdrawQueueRemovalGuards : List Stmt :=
  [.require (.binary .ne
     (.storage ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩) (.intLit 0)),
   .require (.binary .ge (.env .timestamp)
     (.storage ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩))]

def updateWithdrawQueueRemoval : List Stmt :=
  [.letDecl "id" (some abiBytes32) (.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩),
   .require (.binary .eq (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩)
     (.intLit 0)),
   .require (.binary .eq (.storage ⟨"pendingCap", [.mindex (.var "id"), .field "validAt"]⟩)
     (.intLit 0))] ++
  cursorCall allocatedSupplySharesFunction.name
    [.immutable "MORPHO", .var "id", .env .this] "__c2" ++
  [.ite (.binary .ne (.var "__c2") (.intLit 0)) updateWithdrawQueueRemovalGuards [],
   .delete ⟨"config", [.mindex (.var "id")]⟩]

def updateWithdrawQueueRemoveBody : List Stmt :=
  [.ite updateWithdrawQueueUnseenCondition updateWithdrawQueueRemoval []]

def updateWithdrawQueueRemoveLoop : Stmt :=
  .for [.letDecl "i" (some abiUInt256) (.intLit 0)]
    updateWithdrawQueueRemoveCondition updateWithdrawQueuePost updateWithdrawQueueRemoveBody

def updateWithdrawQueueTail : List Stmt :=
  [.assign .storage ⟨"withdrawQueue", []⟩ (.var "newWithdrawQueue"),
   .internalCall "_msgSender" [] "__c3",
   .emit "SetWithdrawQueue" [.var "__c3", .var "newWithdrawQueue"]]

def updateWithdrawQueueAllocation : List Stmt :=
  [.require (.binary .le (.var "currLength") (.intLit (Int.ofNat solcMaxU64))),
   .letDecl cursorName none (.intLit 128), reserveWordArray "currLength",
   .letDecl "seen" (some (.dynamicArray (.elem .bool)))
     (.newArray (.elem .bool) (.var "currLength")),
   .require (.binary .le (.var "newLength") (.intLit (Int.ofNat solcMaxU64))),
   reserveWordArray "newLength",
   .letDecl "newWithdrawQueue" (some (.dynamicArray abiBytes32))
     (.newArray (.elem (.bytes abiBytes32Width)) (.var "newLength"))]

def updateWithdrawQueueBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
   .letDecl "__calldata" (some .bytes) (.env .msgData),
   .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
     (.intLit (Int.ofNat (2 ^ 255 + 4)))),
   .internalCall "_checkAllocatorRole" [] "__role",
   .letDecl "newLength" (some abiUInt256) (.arrayLength .localVar ⟨"indexes", []⟩),
   .letDecl "currLength" (some abiUInt256) (.arrayLength .storage ⟨"withdrawQueue", []⟩)] ++
  updateWithdrawQueueAllocation ++ [updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++
  updateWithdrawQueueTail

set_option maxRecDepth 2000 in
theorem updateWithdrawQueueBody_eq : updateWithdrawQueueTransition.body =
    updateWithdrawQueueBody := by
  decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1
