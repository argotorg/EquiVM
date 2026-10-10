import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsUp
import Benchmarks.Morpho.MetaMorphoV1_1.MarketArithmetic

/-! Source conversion, remaining capacity, and accumulation in a max-deposit iteration. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxDepositArithmetic : List Stmt :=
  [.letDecl "totalSupplyAssets" (some abiUInt256) (.tupleGet (.var "__c2") 0),
   .letDecl "totalSupplyShares" (some abiUInt256) (.tupleGet (.var "__c2") 1),
   .internalCall "SharesMathLib_toAssetsUp"
     [.var "supplyShares", .var "totalSupplyAssets", .var "totalSupplyShares"] "supplyAssets",
   .internalCall "UtilsLib_zeroFloorSub" [.var "supplyCap", .var "supplyAssets"] "__c4",
   .assign .localVar { base := "totalSuppliable", steps := [] }
     (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "totalSuppliable") (.var "__c4")))]

def maxDepositTotalsFrame (frame : Frame) (sa ss : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "totalSupplyAssets" (uint256Value sa)).insert
      "totalSupplyShares" (uint256Value ss) }

def maxDepositAssetsFrame (frame : Frame) (shares sa ss : UInt256) : Frame :=
  { maxDepositTotalsFrame frame sa ss with
    locals := (maxDepositTotalsFrame frame sa ss).locals.insert "supplyAssets"
      (uint256Value (assetsUpWord shares sa ss)) }

def maxDepositGap (shares sa ss cap : UInt256) : UInt256 :=
  UInt256.ofNat (cap.toNat - (assetsUpWord shares sa ss).toNat)

def maxDepositGapFrame (frame : Frame) (shares sa ss cap : UInt256) : Frame :=
  { maxDepositAssetsFrame frame shares sa ss with
    locals := (maxDepositAssetsFrame frame shares sa ss).locals.insert "__c4"
      (uint256Value (maxDepositGap shares sa ss cap)) }

def maxDepositArithmeticFrame (frame : Frame) (shares sa ss cap total : UInt256) : Frame :=
  { maxDepositGapFrame frame shares sa ss cap with
    locals := (maxDepositGapFrame frame shares sa ss cap).locals.insert "totalSuppliable"
      (uint256Value (total + maxDepositGap shares sa ss cap)) }

theorem maxDepositGap_toNat (shares sa ss cap : UInt256) :
    (maxDepositGap shares sa ss cap).toNat = cap.toNat - (assetsUpWord shares sa ss).toNat :=
  UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) cap.val.isLt)

theorem maxDepositTotalsPrefix {frame : Frame} {evm : State} {sa ss ba bs : UInt256}
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs])) :
    ABlock config evm frame maxDepositArithmetic (maxDepositTotalsFrame frame sa ss)
      (maxDepositArithmetic.drop 2) := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    simp only [evalExpr?, store_get_ne _ _ (by decide : ("totalSupplyAssets" == "__c2") = false),
      hbalances, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  · simp only [evalExpr?, hbalances, EvalResult.ofOption, bind, EvalResult.bind]
    rfl

theorem maxDepositTotalsFrame_preserves (frame : Frame) (sa ss : UInt256) (name : Ident)
    (ha : ("totalSupplyAssets" == name) = false) (hs : ("totalSupplyShares" == name) = false) :
    (maxDepositTotalsFrame frame sa ss).locals.get? name = frame.locals.get? name := by
  rw [maxDepositTotalsFrame, store_get_ne _ _ hs, store_get_ne _ _ ha]

theorem maxDepositConversionSource {frame : Frame} {evm : State} {shares sa ss : UInt256}
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hfit : assetsUpFits shares sa ss) :
    ExecStmt config (maxDepositTotalsFrame frame sa ss) evm maxDepositArithmetic[2]!
      (.ok (maxDepositAssetsFrame frame shares sa ss) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares
  subst c
  apply assetsUpCall _ _ _ shares sa ss _ _ _ _ hfit
  · simp only [evalExpr?, maxDepositTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "supplyShares") = false),
      store_get_ne _ _ (by decide : ("totalSupplyAssets" == "supplyShares") = false),
      hshares, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "totalSupplyAssets") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositTotalsFrame, store_get_self, EvalResult.ofOption]

theorem maxDepositConversionReverts {frame : Frame} {evm : State} {shares sa ss : UInt256}
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hbad : ¬ assetsUpFits shares sa ss) :
    ExecStmt config (maxDepositTotalsFrame frame sa ss) evm maxDepositArithmetic[2]!
      .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares
  subst c
  apply assetsUpCallReverts _ _ _ shares sa ss _ _ _ _ hbad
  · simp only [evalExpr?, maxDepositTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "supplyShares") = false),
      store_get_ne _ _ (by decide : ("totalSupplyAssets" == "supplyShares") = false),
      hshares, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositTotalsFrame,
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "totalSupplyAssets") = false),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositTotalsFrame, store_get_self, EvalResult.ofOption]

theorem maxDepositGapSource {frame : Frame} {evm : State} {shares sa ss cap : UInt256}
    (hcontract : frame.contract = contract)
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap)) :
    ExecStmt config (maxDepositAssetsFrame frame shares sa ss) evm maxDepositArithmetic[3]!
      (.ok (maxDepositGapFrame frame shares sa ss cap) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hcap
  subst c
  have he : uint256Value (maxDepositGap shares sa ss cap) =
      .int (Int.ofNat (cap.toNat - (assetsUpWord shares sa ss).toNat)) := by
    rw [uint256Value, maxDepositGap_toNat]
  simp only [maxDepositGapFrame, he]
  apply zeroFloorSubCall
  · simp only [evalExpr?, maxDepositAssetsFrame, maxDepositTotalsFrame,
      store_get_ne _ _ (by decide : ("supplyAssets" == "supplyCap") = false),
      store_get_ne _ _ (by decide : ("totalSupplyShares" == "supplyCap") = false),
      store_get_ne _ _ (by decide : ("totalSupplyAssets" == "supplyCap") = false),
      hcap, EvalResult.ofOption, uint256Value]
  · simp only [evalExpr?, maxDepositAssetsFrame, store_get_self, EvalResult.ofOption,
      uint256Value]

theorem maxDepositGapFrame_total {frame : Frame} {shares sa ss cap total : UInt256}
    (ht : frame.locals.get? "totalSuppliable" = some (uint256Value total)) :
    (maxDepositGapFrame frame shares sa ss cap).locals.get? "totalSuppliable" =
      some (uint256Value total) := by
  rw [maxDepositGapFrame, store_get_ne _ _ (by decide), maxDepositAssetsFrame,
    store_get_ne _ _ (by decide), maxDepositTotalsFrame_preserves _ _ _ _ (by decide) (by decide)]
  exact ht

theorem maxDepositSumSource {frame : Frame} {evm : State} {shares sa ss cap total : UInt256}
    (ht : frame.locals.get? "totalSuppliable" = some (uint256Value total))
    (hfit : total.toNat + (maxDepositGap shares sa ss cap).toNat < UInt256.size) :
    ExecStmt config (maxDepositGapFrame frame shares sa ss cap) evm maxDepositArithmetic[4]!
      (.ok (maxDepositArithmeticFrame frame shares sa ss cap total) evm) := by
  have htotal := maxDepositGapFrame_total (shares := shares) (sa := sa) (ss := ss) (cap := cap) ht
  apply ExecStmt.assign (checkedAddSourceOk ?_ ?_ hfit)
  · simp only [assignStorageRef?, htotal, updateLocalPath?, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExpr?, htotal, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositGapFrame, store_get_self, EvalResult.ofOption]

theorem maxDepositSumReverts {frame : Frame} {evm : State} {shares sa ss cap total : UInt256}
    (ht : frame.locals.get? "totalSuppliable" = some (uint256Value total))
    (hbad : UInt256.size ≤ total.toNat + (maxDepositGap shares sa ss cap).toNat) :
    ExecStmt config (maxDepositGapFrame frame shares sa ss cap) evm maxDepositArithmetic[4]!
      .reverted := by
  apply ExecStmt.assignExprRevert (checkedAddSourceOverflow ?_ ?_ hbad)
  · simp only [evalExpr?, maxDepositGapFrame_total ht, EvalResult.ofOption]
  · simp only [evalExpr?, maxDepositGapFrame, store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
