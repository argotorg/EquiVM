import Benchmarks.UniswapV4PoolManager.PoolSwapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.priceStart (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad step mem = s.priceStart := h.stepFields.load_zero (by change 0 < 8; decide)

theorem PoolSwapMemoryView.tickNext (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 32) mem = s.tickNext := h.stepFields.load 1 (by change 1 < 8; decide)

theorem PoolSwapMemoryView.initialized (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 64) mem = UInt256.fromBool s.initialized := h.stepFields.load 2 (by change 2 < 8; decide)

theorem PoolSwapMemoryView.priceNext (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 96) mem = s.priceNext := h.stepFields.load 3 (by change 3 < 8; decide)

theorem PoolSwapMemoryView.amountIn (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 128) mem = s.amountIn := h.stepFields.load 4 (by change 4 < 8; decide)

theorem PoolSwapMemoryView.amountOut (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 160) mem = s.amountOut := h.stepFields.load 5 (by change 5 < 8; decide)

theorem PoolSwapMemoryView.feeAmount (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 192) mem = s.feeAmount := h.stepFields.load 6 (by change 6 < 8; decide)

theorem PoolSwapMemoryView.growth (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (step+UInt256.ofNat 224) mem = s.feeGrowthGlobal := h.stepFields.load 7 (by change 7 < 8; decide)

theorem PoolSwapMemoryView.price (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad state mem = r.price := h.resultFields.load_zero (by change 0 < 3; decide)

theorem PoolSwapMemoryView.tick (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (state+UInt256.ofNat 32) mem = r.tick := h.resultFields.load 1 (by change 1 < 3; decide)

theorem PoolSwapMemoryView.liquidity (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (state+UInt256.ofNat 64) mem = r.liquidity := h.resultFields.load 2 (by change 2 < 3; decide)

theorem PoolSwapMemoryView.specified (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad params mem = p.amountSpecified := h.paramsFields.load_zero (by change 0 < 5; decide)

theorem PoolSwapMemoryView.spacing (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (params+UInt256.ofNat 32) mem = p.tickSpacing := h.paramsFields.load 1 (by change 1 < 5; decide)

theorem PoolSwapMemoryView.limit (h : PoolSwapMemoryView mem step state params s r p) :
    memLoad (params+UInt256.ofNat 96) mem = p.priceLimit := h.paramsFields.load 3 (by change 3 < 5; decide)

end Benchmarks.UniswapV4PoolManager
