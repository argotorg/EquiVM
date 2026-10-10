import Benchmarks.UniswapV4PoolManager.TickLogStagesSource
import Benchmarks.UniswapV4PoolManager.MostSignificantBit
import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.TickSqrtSource
import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickPriceFunction : FunctionDecl := contract.functions[56]!
theorem tickPrice_lookup : lookupCallable? contract "TickMath_getTickAtSqrtPrice" =
    some tickPriceFunction.toCallable := rfl

-- LIBRARY CANDIDATE: the source outcome of a partial signed-word computation.
def signedWordResult (f : Frame) (evm : EVM.State) (result : Option UInt256) : ExecResult :=
  match result with
  | none => .reverted
  | some tick => .returned f evm (some [.int (EVM.signed tick)])

-- LIBRARY CANDIDATE: lift a partial signed-word block result to a function result.
theorem execFuncBodySignedWordResult {cfg : Config} {f : Frame} {evm : EVM.State}
    {stmts : List Stmt} {result : Option UInt256}
    (h : ∃ f', ExecBlock cfg f evm stmts (signedWordResult f' evm result)) :
    ∃ f', ExecFuncBody cfg f evm stmts (signedWordResult f' evm result) := by
  obtain ⟨f', hb⟩ := h
  cases result with
  | none => exact ⟨f', .execBlockRevert hb⟩
  | some w => exact ⟨f', .execBlockRet hb⟩

def tickPriceOutside (sqrtPrice : UInt256) : Prop :=
  1461446703485210103287273052203988822374428841602 <
    ((Int.ofNat sqrtPrice.toNat - 4295128739) % (2^160 : Int))
instance (sqrtPrice : UInt256) : Decidable (tickPriceOutside sqrtPrice) :=
  inferInstanceAs (Decidable (_ < _))

def tickPriceNormalize (price msb : UInt256) : UInt256 :=
  if 128 ≤ msb.toNat then UInt256.shiftRight price (UInt256.sub msb (UInt256.ofNat 127))
  else UInt256.shiftLeft price (UInt256.sub (UInt256.ofNat 127) msb)

def tickPriceLogStart (msb : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.sub msb (UInt256.ofNat 128)) (UInt256.ofNat 64)

def tickPriceLog (sqrtPrice : UInt256) : UInt256 :=
  let price := UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32)
  let msb := mostSignificantBit price
  (tickLogStages (tickPriceNormalize price msb) (tickPriceLogStart msb) tickLogStageData).2

def tickPriceScaled (log2 : UInt256) : UInt256 := UInt256.mul log2 (UInt256.ofNat 255738958999603826347141)
def tickPriceLowRaw (log2 : UInt256) : UInt256 :=
  UInt256.sar (UInt256.ofNat 128) (UInt256.sub (tickPriceScaled log2) (UInt256.ofNat 3402992956809132418596140100660247210))
def tickPriceHighRaw (log2 : UInt256) : UInt256 :=
  UInt256.sar (UInt256.ofNat 128) (tickPriceScaled log2 + UInt256.ofNat 291339464771989622907027621153398088495)
def tickPriceLow (log2 : UInt256) : UInt256 := UInt256.signextend (UInt256.ofNat 2) (tickPriceLowRaw log2)
def tickPriceHigh (log2 : UInt256) : UInt256 := UInt256.signextend (UInt256.ofNat 2) (tickPriceHighRaw log2)

def tickPriceChoose (sqrtPrice low high : UInt256) : Option UInt256 :=
  if low = high then some low
  else if (EVM.signed high).natAbs ≤ 887272 then
    some (if (tickSqrtPrice (EVM.signed high)).toNat ≤ sqrtPrice.toNat then high else low)
  else none

def tickPriceFinish (sqrtPrice log2 : UInt256) : Option UInt256 :=
  tickPriceChoose sqrtPrice (tickPriceLow log2) (tickPriceHigh log2)

theorem tickPriceFinish_eq (sqrtPrice log2 : UInt256) :
    tickPriceFinish sqrtPrice log2 = tickPriceChoose sqrtPrice (tickPriceLow log2) (tickPriceHigh log2) := rfl

def tickPriceResult (sqrtPrice : UInt256) : Option UInt256 :=
  if tickPriceOutside sqrtPrice then none
  else if UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) = ⟨0⟩ then none
  else tickPriceFinish sqrtPrice (tickPriceLog sqrtPrice)

theorem tickLogStageData_valid : ∀ stage ∈ tickLogStageData, stage.valid := by
  have h : tickLogStageData.all (fun stage => decide stage.valid) = true := by decide +kernel
  intro stage hs
  exact of_decide_eq_true ((List.all_eq_true.mp h) stage hs)

theorem tickLogStageData_avoids_sqrt : ∀ stage ∈ tickLogStageData, "sqrtPriceX96" ≠ stage.name := by
  have h : tickLogStageData.all (fun stage => decide ("sqrtPriceX96" ≠ stage.name)) = true := by decide +kernel
  intro stage hs
  exact of_decide_eq_true ((List.all_eq_true.mp h) stage hs)

theorem tickLogFlag_compiled (r : UInt256) :
    tickLogFlag r = UInt256.shiftRight (UInt256.mul r r) (UInt256.ofNat 255) :=
  wordShiftRightCompose _ (by decide : 127+128 < 256)

-- LIBRARY CANDIDATE: signed interpretation is injective on EVM words.
theorem signedWord_injective : Function.Injective EVM.signed := by
  intro x y h
  have he := congrArg EVM.wordOfInt h
  simpa only [wordOfInt_signed] using he

-- LIBRARY CANDIDATE: int24 casts in arbitrary expression contexts.
theorem evalSignedWord24 {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (EVM.signed w))) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) w))) := by
  simpa only [normalizeSigned24Word] using evalExpr_cast_int (intType := .sint ⟨24, by decide⟩) he

end Benchmarks.UniswapV4PoolManager
