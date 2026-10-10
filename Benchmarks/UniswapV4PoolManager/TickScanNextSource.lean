import Benchmarks.UniswapV4PoolManager.TickScanNextWords
import Benchmarks.UniswapV4PoolManager.WordNarrowArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickScanNextExpr (distance : Expr) (lte : Bool) : Expr :=
  .cast (.binary .mul
    (.cast (.binary (if lte then .sub else .add) (.var "compressed") distance)
      (.elem (.int (.sint ⟨24, by decide⟩))))
    (.var "tickSpacing")) (.elem (.int (.sint ⟨24, by decide⟩)))

theorem tickScanNext_eval {f : Frame} {evm : EVM.State} {compressed spacing distance : UInt256}
    {e : Expr} (lte : Bool)
    (hc : f.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))))
    (hs : f.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)))
    (hd : distance.toNat < 256)
    (he : evalExpr? config f evm e = .ok (.int (Int.ofNat distance.toNat))) :
    evalExpr? config f evm (tickScanNextExpr e lte) =
      .ok (.int (EVM.signed (tickScanNextWord compressed spacing distance lte))) := by
  have hclean : UInt256.signextend (UInt256.ofNat 2) distance = distance :=
    (signextend24_eq_iff distance).mpr (Or.inl (by omega))
  have hsmall : EVM.signed (UInt256.signextend (UInt256.ofNat 2) distance) = Int.ofNat distance.toNat := by
    rw [hclean, signed_eq_normalize]
    exact normalizeInt_sint256_word_of_lt _ (by change distance.toNat < 2^255; omega)
  have he' : evalExpr? config f evm e =
      .ok (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) distance))) := by rw [hsmall]; exact he
  cases lte with
  | false => exact evalSigned24Mul (evalSigned24Add (evalLocalValue hc) he') (evalLocalValue hs)
  | true =>
    have hsub := evalSigned24Sub (evalLocalValue (cfg := config) (evm := evm) hc) he'
    rw [signextend24_sub_left] at hsub
    exact evalSigned24Mul hsub (evalLocalValue hs)

end Benchmarks.UniswapV4PoolManager
