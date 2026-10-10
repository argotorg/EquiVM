import Benchmarks.UniswapV4PoolManager.WordSignextend128
import Benchmarks.UniswapV4PoolManager.SignedWordBounds
import Benchmarks.UniswapV4PoolManager.SignedNormalizeRange
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def balanceDeltaAmount0 (word : UInt256) : Int := EVM.signed (UInt256.sar (UInt256.ofNat 128) word)
def balanceDeltaAmount1 (word : UInt256) : Int := EVM.signed (UInt256.signextend (UInt256.ofNat 15) word)

theorem balanceDeltaAmount0_fits (word : UInt256) : signedFits ⟨128, by decide⟩ (balanceDeltaAmount0 word) := by
  have hw := signedWord_fits word
  change -(2^255 : Int) ≤ EVM.signed word ∧ EVM.signed word < 2^255 at hw
  unfold balanceDeltaAmount0
  rw [wordSarSigned word (by decide)]
  change -(2^127 : Int) ≤ EVM.signed word / (2^128 : Int) ∧ EVM.signed word / (2^128 : Int) < 2^127
  constructor <;> omega

theorem balanceDeltaAmount1_fits (word : UInt256) : signedFits ⟨128, by decide⟩ (balanceDeltaAmount1 word) := by
  rw [balanceDeltaAmount1, ← normalizeSigned128Word]
  exact normalizeSigned_fits _ _

theorem balanceDeltaAmount0_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr} {word : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (EVM.signed word))) :
    evalExpr? cfg f evm (.cast (.binary (.shr (.sint ⟨256, by decide⟩)) e (.intLit 128))
      (.elem (.int (.sint ⟨128, by decide⟩)))) = .ok (.int (balanceDeltaAmount0 word)) := by
  have hshift := evalSignedWordSar (n := 128) (by decide) he
    (show evalExpr? cfg f evm (.intLit 128) = .ok (.int (Int.ofNat 128)) by simp only [evalExpr?, pure]; rfl)
  have hc := evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) hshift
  change evalExpr? cfg f evm _ = .ok (.int (normalizeInt (.sint ⟨128, by decide⟩) (balanceDeltaAmount0 word))) at hc
  simpa only [normalizeSigned_of_fits (balanceDeltaAmount0_fits word)] using hc

theorem balanceDeltaAmount1_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr} {word : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (EVM.signed word))) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.sint ⟨128, by decide⟩)))) =
      .ok (.int (balanceDeltaAmount1 word)) := by
  simpa only [normalizeSigned128Word] using evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) he

end Benchmarks.UniswapV4PoolManager
