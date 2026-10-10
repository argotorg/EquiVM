import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableSource

/-! The allocated withdrawal simulation loop and its reader/arithmetic phases. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def withdrawLoopReaders : List Stmt :=
  cursorCall allocatedMarketParamsFunction.name [.var "id"] "marketParams" ++
  cursorCall allocatedSupplySharesFunction.name
    [.immutable "MORPHO", .var "id", .env .this] "supplyShares" ++
  cursorCall allocatedMarketBalancesFunction.name [.immutable "MORPHO", .var "marketParams"] "__c2"

def withdrawLoopArithmetic : List Stmt :=
  [.letDecl "totalSupplyAssets" (some abiUInt256) (.tupleGet (.var "__c2") 0),
   .letDecl "totalSupplyShares" (some abiUInt256) (.tupleGet (.var "__c2") 1),
   .letDecl "totalBorrowAssets" (some abiUInt256) (.tupleGet (.var "__c2") 2),
   .internalCall "SharesMathLib_toAssetsDown"
     [.var "supplyShares", .var "totalSupplyAssets", .var "totalSupplyShares"] "__c3"] ++
  cursorCall allocatedWithdrawableFunction.name
    [.var "marketParams", .var "totalSupplyAssets", .var "totalBorrowAssets", .var "__c3"] "__c4" ++
  [.internalCall "UtilsLib_zeroFloorSub" [.var "assets", .var "__c4"] "__c5",
   .assign .localVar ⟨"assets", []⟩ (.var "__c5"),
   .ite (.binary .eq (.var "assets") (.intLit 0)) [.break] []]

def withdrawLoopIteration : List Stmt :=
  [.letDecl "id" (some abiBytes32) (.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩)] ++
  withdrawLoopReaders ++ withdrawLoopArithmetic

theorem allocatedSimulateWithdrawFunction_body :
    allocatedSimulateWithdrawFunction.body =
      [.for [.letDecl "i" (some abiUInt256) (.intLit 0)] accruedAssetsCondition
         accruedAssetsPost withdrawLoopIteration,
       .return [.var "assets", .var cursorName]] := by decide +kernel

def withdrawLoopParamsFrame (frame : Frame) (params : ByteArray) (ptr : UInt256) : Frame :=
  cursorResultFrame frame "marketParams" (marketParamsValue params) ptr

def withdrawLoopSharesFrame (frame : Frame) (params : ByteArray) (ptr shares next : UInt256) :
    Frame :=
  cursorResultFrame (withdrawLoopParamsFrame frame params ptr) "supplyShares"
    (uint256Value shares) next

def withdrawLoopBalancesFrame (frame : Frame) (params : ByteArray)
    (ptr shares next cursor : UInt256) (balances : Value) : Frame :=
  cursorResultFrame (withdrawLoopSharesFrame frame params ptr shares next) "__c2" balances cursor

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
