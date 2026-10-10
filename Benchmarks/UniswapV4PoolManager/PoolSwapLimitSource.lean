import Benchmarks.UniswapV4PoolManager.PoolSwapInputsSource
import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.NatComparisonSource
import Benchmarks.UniswapV4PoolManager.ConditionalPairSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLimitValid (packed limit : UInt256) (zeroForOne : Bool) : Prop :=
  if zeroForOne then limit.toNat < (slot0SqrtPriceWord packed).toNat ∧ 4295128739 < limit.toNat
  else (slot0SqrtPriceWord packed).toNat < limit.toNat ∧ limit.toNat < 1461446703485210103287273052203988822378723970342
instance (packed limit : UInt256) (zeroForOne : Bool) : Decidable (poolSwapLimitValid packed limit zeroForOne) := by
  unfold poolSwapLimitValid
  infer_instance

def poolSwapLimitName (zeroForOne : Bool) : Ident := if zeroForOne then "__c10" else "__c11"
def poolSwapLimitFrame (f : Frame) (packed : UInt256) (zeroForOne : Bool) : Frame :=
  wordLocal f (poolSwapLimitName zeroForOne) (slot0SqrtPriceWord packed)
def poolSwapLimitBranch (zeroForOne : Bool) : List Stmt :=
  [.internalCall "Slot0Library_sqrtPriceX96" [.var "slot0Start"] (poolSwapLimitName zeroForOne),
   .ite (.binary (if zeroForOne then .ge else .le) (.field (.var "params") "sqrtPriceLimitX96")
      (.var (poolSwapLimitName zeroForOne))) [.require (.boolLit false)] [],
   .ite (.binary (if zeroForOne then .le else .ge) (.field (.var "params") "sqrtPriceLimitX96")
      (.intLit (if zeroForOne then 4295128739 else 1461446703485210103287273052203988822378723970342)))
      [.require (.boolLit false)] []]

theorem poolSwapFunction_limit : poolSwapFunction.body[25]! =
    .ite (.var "zeroForOne") (poolSwapLimitBranch true) (poolSwapLimitBranch false) := rfl

theorem poolSwapLimitFrame_get (f : Frame) (packed : UInt256) (zeroForOne : Bool) (key : Ident)
    (h10 : ("__c10" == key) = false) (h11 : ("__c11" == key) = false) :
    (poolSwapLimitFrame f packed zeroForOne).locals.get? key = f.locals.get? key := by
  cases zeroForOne
  · exact store_get_ne _ _ h11
  · exact store_get_ne _ _ h10

theorem poolSwapLimitBranchSource {f : Frame} {evm : State} {packed : UInt256} {p : PoolSwapParamsWords}
    (zeroForOne : Bool) (hf : f.contract = contract)
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hs : f.locals.get? "slot0Start" = some (wordBytes32Value packed)) :
    ExecBlock config f evm (poolSwapLimitBranch zeroForOne)
      (if poolSwapLimitValid packed p.priceLimit zeroForOne then .ok (poolSwapLimitFrame f packed zeroForOne) evm else .reverted) := by
  let f1 := poolSwapLimitFrame f packed zeroForOne
  have hcall := slot0SqrtCall hf (evalLocalValue (evm := evm) hs) (poolSwapLimitName zeroForOne)
  have hp1 : f1.locals.get? "params" = some (poolSwapParamsValue p) :=
    (poolSwapLimitFrame_get f packed zeroForOne "params" (by decide) (by decide)).trans hp
  have he := evalStructField (cfg := config) (evm := evm) (field := "sqrtPriceLimitX96") (evalLocalValue hp1) rfl
  have hv : evalExpr? config f1 evm (.var (poolSwapLimitName zeroForOne)) =
      .ok (.int (Int.ofNat (slot0SqrtPriceWord packed).toNat)) := evalLocalValue (store_get_self _ _ _)
  cases zeroForOne
  · have h0 := evalNatLe he hv
    have h1 := evalNatGe he
      (show evalExpr? config f1 evm (.intLit 1461446703485210103287273052203988822378723970342) =
        .ok (.int (Int.ofNat 1461446703485210103287273052203988822378723970342)) by simp only [evalExpr?, pure]; rfl)
    have ht := execBlock_rejectUnlessPair
      (p := (slot0SqrtPriceWord packed).toNat < p.priceLimit.toNat)
      (q := p.priceLimit.toNat < 1461446703485210103287273052203988822378723970342)
      (by simpa only [Nat.not_lt] using h0) (by simpa only [Nat.not_lt] using h1)
    exact ExecBlock.consNormal hcall ht
  · have h0 := evalNatGe he hv
    have h1 := evalNatLe he
      (show evalExpr? config f1 evm (.intLit 4295128739) = .ok (.int (Int.ofNat 4295128739)) by simp only [evalExpr?, pure]; rfl)
    have ht := execBlock_rejectUnlessPair
      (p := p.priceLimit.toNat < (slot0SqrtPriceWord packed).toNat) (q := 4295128739 < p.priceLimit.toNat)
      (by simpa only [Nat.not_lt] using h0) (by simpa only [Nat.not_lt] using h1)
    exact ExecBlock.consNormal hcall ht

theorem poolSwapLimitSource {f : Frame} {evm : State} {packed : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hs : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)) :
    ExecStmt config f evm poolSwapFunction.body[25]!
      (if poolSwapLimitValid packed p.priceLimit p.zeroForOne then .ok (poolSwapLimitFrame f packed p.zeroForOne) evm else .reverted) := by
  rw [poolSwapFunction_limit]
  have hb := poolSwapLimitBranchSource (evm := evm) p.zeroForOne hf hp hs
  have hg := evalLocalValue (cfg := config) (evm := evm) hz
  cases he : p.zeroForOne
  · rw [he] at hg hb
    exact ExecStmt.iteFalse hg hb
  · rw [he] at hg hb
    exact ExecStmt.iteTrue hg hb

end Benchmarks.UniswapV4PoolManager
