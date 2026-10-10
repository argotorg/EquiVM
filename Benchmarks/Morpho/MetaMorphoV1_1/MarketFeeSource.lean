import Benchmarks.Morpho.MetaMorphoV1_1.MarketAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.SharesDownSource

/-! The fee branch after interest has been added to the market's asset balances. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketFeeCondition : Expr :=
  .binary .ne (.field (.var "market") "fee") (.intLit 0)

def marketFeeOriginalBody : List Stmt :=
  [.internalCall "MathLib_wMulDown"
      [.var "interest", .field (.var "market") "fee"] "feeAmount",
   .internalCall "SharesMathLib_toSharesDown"
      [.var "feeAmount", .inRange (.uint ⟨256, by decide⟩)
        (.binary .sub (.field (.var "market") "totalSupplyAssets") (.var "feeAmount")),
       .field (.var "market") "totalSupplyShares"] "feeShares",
   .internalCall "UtilsLib_toUint128" [.var "feeShares"] "__c9",
   marketFieldAdd "totalSupplyShares" "__c9"]

def marketFeeBody : List Stmt :=
  [.internalCall "MathLib_wMulDown"
      [.var "interest", .field (.var "market") "fee"] "feeAmount",
   .internalCall "SharesMathLib_toSharesDown"
      [.var "feeAmount", .inRange (.uint ⟨256, by decide⟩)
        (.binary .sub (.field (.var "market") "totalSupplyAssets") (.var "feeAmount")),
       .field (.var "market") "totalSupplyShares"] "feeShares"] ++
  cursorCall allocatedToUint128Function.name [.var "feeShares"] "__c9" ++
  [marketFieldAdd "totalSupplyShares" "__c9"]

set_option maxRecDepth 2000 in
theorem marketFeeStatements :
    marketAccrualBody.drop 12 = [.ite marketFeeCondition marketFeeBody []] := by
  have hs : marketAccrualSourceBody =
      [borrowRateStatement,
       .internalCall "MathLib_wTaylorCompounded" [.var "borrowRate", .var "elapsed"] "__c3",
       .internalCall "MathLib_wMulDown"
         [.field (.var "market") "totalBorrowAssets", .var "__c3"] "interest",
       .internalCall "UtilsLib_toUint128" [.var "interest"] "__c5",
       marketFieldAdd "totalBorrowAssets" "__c5",
       .internalCall "UtilsLib_toUint128" [.var "interest"] "__c6",
       marketFieldAdd "totalSupplyAssets" "__c6",
       .ite marketFeeCondition marketFeeOriginalBody []] := rfl
  rw [marketAccrualBody, hs]
  simp [allocationBody, allocationStatement, marketBalancesAllocationCalls, borrowRateStatement,
    marketFeeOriginalBody, marketFeeBody, marketFieldAdd, cursorCall]

theorem marketFeeConditionSource {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba : UInt256}
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba)) :
    evalExpr? config frame evm marketFeeCondition =
      .ok (.bool (decide (calldataWord market 160 ≠ ⟨0⟩))) := by
  exact wordNeSource
    (evalExpr_structField
      (show evalExpr? config frame evm (.var "market") =
        .ok (marketUpdatedValue market sa ss ba) by
          simp only [evalExpr?, hm, EvalResult.ofOption]) rfl)
    (by simp only [evalExpr?, pure]; rfl)

theorem marketFeeSkipSource {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba : UInt256}
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hz : calldataWord market 160 = ⟨0⟩) :
    ExecBlock config frame evm (marketAccrualBody.drop 12) (.ok frame evm) := by
  rw [marketFeeStatements]
  exact ExecBlock.consNormal (ExecStmt.iteFalse
    (by rw [marketFeeConditionSource hm]; simp only [hz, ne_eq, not_true_eq_false, decide_false])
    ExecBlock.nil) ExecBlock.nil

-- LIBRARY CANDIDATE: multiplication of two canonical uint128 words fits uint256.
theorem uint128ProductFits {a b : UInt256} (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) :
    a.toNat * b.toNat < UInt256.size := by
  calc a.toNat * b.toNat ≤ (2 ^ 128) * b.toNat := Nat.mul_le_mul_right _ (Nat.le_of_lt ha)
       _ < (2 ^ 128) * (2 ^ 128) := Nat.mul_lt_mul_of_pos_left hb (by decide)
       _ = UInt256.size := by decide +kernel

def marketFeeShares (interest fee supplyAssets supplyShares : UInt256) : UInt256 :=
  sharesDownWord (wadMulWord interest fee)
    (UInt256.sub supplyAssets (wadMulWord interest fee)) supplyShares

def marketFeeFits (ptr interest fee supplyAssets supplyShares : UInt256) : Prop :=
  (wadMulWord interest fee).toNat ≤ supplyAssets.toNat ∧
    sharesDownFits (wadMulWord interest fee) supplyShares ∧
    castAddFits ptr (marketFeeShares interest fee supplyAssets supplyShares) supplyShares

instance (ptr interest fee supplyAssets supplyShares : UInt256) :
    Decidable (marketFeeFits ptr interest fee supplyAssets supplyShares) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def marketFeeAmountFrame (frame : Frame) (interest fee : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "feeAmount" (uint256Value (wadMulWord interest fee)) }

def marketFeeSharesFrame (frame : Frame) (interest fee supplyAssets supplyShares : UInt256) :
    Frame :=
  { marketFeeAmountFrame frame interest fee with
    locals := (marketFeeAmountFrame frame interest fee).locals.insert "feeShares"
      (uint256Value (marketFeeShares interest fee supplyAssets supplyShares)) }

theorem marketUpdatedFieldSource {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba : UInt256} {name : Ident} {value : Value}
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hf : lookupField? (marketUpdatedValue market sa ss ba) name = some value) :
    evalExpr? config frame evm (.field (.var "market") name) = .ok value :=
  evalExpr_structField
    (show evalExpr? config frame evm (.var "market") =
      .ok (marketUpdatedValue market sa ss ba) by
        simp only [evalExpr?, hm, EvalResult.ofOption]) hf

theorem marketFeeAmountFrame_market {frame : Frame} {market : ByteArray}
    {sa ss ba : UInt256} (interest fee : UInt256)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba)) :
    (marketFeeAmountFrame frame interest fee).locals.get? "market" =
      some (marketUpdatedValue market sa ss ba) := by
  rw [marketFeeAmountFrame, store_get_ne _ _ (by decide)]
  exact hm

theorem marketFeeAmountSource {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba interest : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hib : interest.toNat < 2 ^ 128) (hfb : (calldataWord market 160).toNat < 2 ^ 128) :
    ABlock config evm frame marketFeeBody
      (marketFeeAmountFrame frame interest (calldataWord market 160)) (marketFeeBody.drop 1) := by
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  constructor
  intro result htail
  exact ExecBlock.consNormal (wadMulCall evm locals imms interest (calldataWord market 160)
    "feeAmount" _ _ (uint128ProductFits hib hfb)
    (by simp only [evalExpr?, hi, EvalResult.ofOption]) (marketUpdatedFieldSource hm rfl)) htail

theorem marketFeeArithmeticSourcePrefix {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba interest : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hib : interest.toNat < 2 ^ 128) (hfb : (calldataWord market 160).toNat < 2 ^ 128)
    (hsa : sa.toNat < 2 ^ 128) (hss : ss.toNat < 2 ^ 128)
    (hle : (wadMulWord interest (calldataWord market 160)).toNat ≤ sa.toNat)
    (hprod : sharesDownFits (wadMulWord interest (calldataWord market 160)) ss) :
    ABlock config evm frame marketFeeBody
      (marketFeeSharesFrame frame interest (calldataWord market 160) sa ss)
      (marketFeeBody.drop 2) := by
  constructor
  intro result htail
  apply (marketFeeAmountSource hcontract hm hi hib hfb).run
  have htotal := marketFeeAmountFrame_market interest (calldataWord market 160) hm
  have hamount : evalExpr? config (marketFeeAmountFrame frame interest (calldataWord market 160))
      evm (.var "feeAmount") =
        .ok (uint256Value (wadMulWord interest (calldataWord market 160))) := by
    simp only [evalExpr?, marketFeeAmountFrame, store_get_self, EvalResult.ofOption]
  have hsub := evalExpr_uint256_sub (marketUpdatedFieldSource htotal
    (show lookupField? (marketUpdatedValue market sa ss ba) "totalSupplyAssets" =
      some (uint256Value sa) from rfl)) hamount hle
  have hbound : (UInt256.sub sa (wadMulWord interest (calldataWord market 160))).toNat <
      2 ^ 128 := by rw [usub_toNat hle]; omega
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  exact ExecBlock.consNormal (sharesDownCall evm _ imms
    (wadMulWord interest (calldataWord market 160))
    (UInt256.sub sa (wadMulWord interest (calldataWord market 160))) ss
    "feeShares" _ _ _ hbound hss hprod hamount hsub
    (marketUpdatedFieldSource htotal rfl)) htail

theorem marketFeeArithmeticSourceReverts {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba interest : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hib : interest.toNat < 2 ^ 128) (hfb : (calldataWord market 160).toNat < 2 ^ 128)
    (hsa : sa.toNat < 2 ^ 128) (hss : ss.toNat < 2 ^ 128)
    (hbad : ¬ ((wadMulWord interest (calldataWord market 160)).toNat ≤ sa.toNat ∧
      sharesDownFits (wadMulWord interest (calldataWord market 160)) ss)) :
    ExecBlock config frame evm marketFeeBody .reverted := by
  apply (marketFeeAmountSource hcontract hm hi hib hfb).run
  have htotal := marketFeeAmountFrame_market interest (calldataWord market 160) hm
  have hamount : evalExpr? config (marketFeeAmountFrame frame interest (calldataWord market 160))
      evm (.var "feeAmount") =
        .ok (uint256Value (wadMulWord interest (calldataWord market 160))) := by
    simp only [evalExpr?, marketFeeAmountFrame, store_get_self, EvalResult.ofOption]
  have hsupply := marketUpdatedFieldSource (evm := evm) htotal
    (show lookupField? (marketUpdatedValue market sa ss ba) "totalSupplyAssets" =
      some (uint256Value sa) from rfl)
  by_cases hle : (wadMulWord interest (calldataWord market 160)).toNat ≤ sa.toNat
  · have hsub := evalExpr_uint256_sub hsupply hamount hle
    have hbound : (UInt256.sub sa (wadMulWord interest (calldataWord market 160))).toNat <
        2 ^ 128 := by rw [usub_toNat hle]; omega
    rcases frame with ⟨c, locals, imms⟩
    cases hcontract
    exact ExecBlock.consRevert (sharesDownCallReverts evm _ imms
      (wadMulWord interest (calldataWord market 160))
      (UInt256.sub sa (wadMulWord interest (calldataWord market 160))) ss
      "feeShares" _ _ _ hbound hss (fun h ↦ hbad ⟨hle, h⟩) hamount hsub
      (marketUpdatedFieldSource htotal rfl))
  · have hsub := checkedSubSourceUnderflow hsupply hamount (Nat.lt_of_not_ge hle)
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
    simp only [evalExprs?, hamount, hsub, bind, EvalResult.bind]

theorem marketFeeSharesFrame_market {frame : Frame} {market : ByteArray}
    {sa ss ba interest : UInt256}
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba)) :
    (marketFeeSharesFrame frame interest (calldataWord market 160) sa ss).locals.get? "market" =
      some (marketUpdatedValue market sa ss ba) := by
  rw [marketFeeSharesFrame, store_get_ne _ _ (by decide)]
  exact marketFeeAmountFrame_market _ _ hm

theorem marketFeeSharesFrame_cursor {frame : Frame} {interest fee sa ss ptr : UInt256}
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) :
    (marketFeeSharesFrame frame interest fee sa ss).locals.get? cursorName =
      some (uint256Value ptr) := by
  rw [marketFeeSharesFrame, store_get_ne _ _ (by decide), marketFeeAmountFrame,
    store_get_ne _ _ (by decide)]
  exact hp

def marketFeeResultFrame (frame : Frame) (market : ByteArray) (ptr interest sa ss ba : UInt256) :
    Frame :=
  marketUpdateFrame
    (cursorCastFrame (marketFeeSharesFrame frame interest (calldataWord market 160) sa ss)
      "__c9" (marketFeeShares interest (calldataWord market 160) sa ss) ptr)
    (marketUpdatedValue market sa
      (ss + marketFeeShares interest (calldataWord market 160) sa ss) ba)

theorem marketFeeBodySource {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba interest ptr : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hib : interest.toNat < 2 ^ 128) (hfb : (calldataWord market 160).toNat < 2 ^ 128)
    (hsa : sa.toNat < 2 ^ 128) (hss : ss.toNat < 2 ^ 128)
    (hfit : marketFeeFits ptr interest (calldataWord market 160) sa ss) :
    ExecBlock config frame evm marketFeeBody
      (.ok (marketFeeResultFrame frame market ptr interest sa ss ba) evm) := by
  apply (marketFeeArithmeticSourcePrefix hcontract hm hi hib hfb hsa hss hfit.1 hfit.2.1).run
  apply (castFieldSourcePrefix "totalSupplyShares" "__c9" []
    (show (marketFeeSharesFrame frame interest (calldataWord market 160) sa ss).contract =
      contract from hcontract) (by decide) (by decide) (by decide)
    (marketFeeSharesFrame_market hm) rfl rfl
    (by simp only [evalExpr?, marketFeeSharesFrame, store_get_self, EvalResult.ofOption])
    (marketFeeSharesFrame_cursor hp) hfit.2.2).run
  exact ExecBlock.nil

theorem marketFeeBodySourceReverts {frame : Frame} {evm : State} {market : ByteArray}
    {sa ss ba interest ptr : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketUpdatedValue market sa ss ba))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hib : interest.toNat < 2 ^ 128) (hfb : (calldataWord market 160).toNat < 2 ^ 128)
    (hsa : sa.toNat < 2 ^ 128) (hss : ss.toNat < 2 ^ 128)
    (hbad : ¬ marketFeeFits ptr interest (calldataWord market 160) sa ss) :
    ExecBlock config frame evm marketFeeBody .reverted := by
  by_cases harith : (wadMulWord interest (calldataWord market 160)).toNat ≤ sa.toNat ∧
      sharesDownFits (wadMulWord interest (calldataWord market 160)) ss
  · apply (marketFeeArithmeticSourcePrefix
      hcontract hm hi hib hfb hsa hss harith.1 harith.2).run
    exact castFieldSourceReverts "totalSupplyShares" "__c9" []
      (show (marketFeeSharesFrame frame interest (calldataWord market 160) sa ss).contract =
        contract from hcontract) (by decide) (by decide) (by decide)
      (marketFeeSharesFrame_market hm) rfl
      (by simp only [evalExpr?, marketFeeSharesFrame, store_get_self, EvalResult.ofOption])
      (marketFeeSharesFrame_cursor hp) (fun hcast ↦ hbad ⟨harith.1, harith.2, hcast⟩)
  · exact marketFeeArithmeticSourceReverts hcontract hm hi hib hfb hsa hss harith

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
