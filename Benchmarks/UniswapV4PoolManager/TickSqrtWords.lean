import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickSqrtFactors : List (UInt256 × UInt256) :=
  [(UInt256.ofNat 2, UInt256.ofNat 340248342086729790484326174814286782778),
   (UInt256.ofNat 4, UInt256.ofNat 340214320654664324051920982716015181260),
   (UInt256.ofNat 8, UInt256.ofNat 340146287995602323631171512101879684304),
   (UInt256.ofNat 16, UInt256.ofNat 340010263488231146823593991679159461444),
   (UInt256.ofNat 32, UInt256.ofNat 339738377640345403697157401104375502016),
   (UInt256.ofNat 64, UInt256.ofNat 339195258003219555707034227454543997025),
   (UInt256.ofNat 128, UInt256.ofNat 338111622100601834656805679988414885971),
   (UInt256.ofNat 256, UInt256.ofNat 335954724994790223023589805789778977700),
   (UInt256.ofNat 512, UInt256.ofNat 331682121138379247127172139078559817300),
   (UInt256.ofNat 1024, UInt256.ofNat 323299236684853023288211250268160618739),
   (UInt256.ofNat 2048, UInt256.ofNat 307163716377032989948697243942600083929),
   (UInt256.ofNat 4096, UInt256.ofNat 277268403626896220162999269216087595045),
   (UInt256.ofNat 8192, UInt256.ofNat 225923453940442621947126027127485391333),
   (UInt256.ofNat 16384, UInt256.ofNat 149997214084966997727330242082538205943),
   (UInt256.ofNat 32768, UInt256.ofNat 66119101136024775622716233608466517926),
   (UInt256.ofNat 65536, UInt256.ofNat 12847376061809297530290974190478138313),
   (UInt256.ofNat 131072, UInt256.ofNat 485053260817066172746253684029974020),
   (UInt256.ofNat 262144, UInt256.ofNat 691415978906521570653435304214168),
   (UInt256.ofNat 524288, UInt256.ofNat 1404880482679654955896180642)]

def tickSqrtInitial (absTick : UInt256) : UInt256 :=
  if UInt256.land absTick (UInt256.ofNat 1) ≠ ⟨0⟩ then
    UInt256.ofNat 340265354078544963557816517032075149313 else UInt256.ofNat (2^128)

def tickSqrtStage (absTick price mask factor : UInt256) : UInt256 :=
  if UInt256.land absTick mask ≠ ⟨0⟩ then
    UInt256.shiftRight (UInt256.mul price factor) (UInt256.ofNat 128) else price

def tickSqrtStages (absTick price : UInt256) : List (UInt256 × UInt256) → UInt256
  | [] => price
  | (mask, factor) :: rest => tickSqrtStages absTick (tickSqrtStage absTick price mask factor) rest

def tickSqrtRatio (absTick : UInt256) : UInt256 :=
  tickSqrtStages absTick (tickSqrtInitial absTick) tickSqrtFactors

def tickSqrtRound (price : UInt256) : UInt256 :=
  UInt256.shiftRight (price + UInt256.ofNat 4294967295) (UInt256.ofNat 32)

def tickSqrtPrice (tick : Int) : UInt256 :=
  let price := tickSqrtRatio (UInt256.ofNat tick.natAbs)
  tickSqrtRound (if 0 < tick then UInt256.div (UInt256.ofNat (2^256-1)) price else price)

end Benchmarks.UniswapV4PoolManager
