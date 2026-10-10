import Benchmarks.UniswapV4PoolManager.TickLogCompiled

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickLogStages_unroll (log2 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 : UInt256)
    (h1 : tickLogNext r0 true = r1)
    (h2 : tickLogNext r1 true = r2)
    (h3 : tickLogNext r2 true = r3)
    (h4 : tickLogNext r3 true = r4)
    (h5 : tickLogNext r4 true = r5)
    (h6 : tickLogNext r5 true = r6)
    (h7 : tickLogNext r6 true = r7)
    (h8 : tickLogNext r7 true = r8)
    (h9 : tickLogNext r8 true = r9)
    (h10 : tickLogNext r9 true = r10)
    (h11 : tickLogNext r10 true = r11)
    (h12 : tickLogNext r11 true = r12)
    (h13 : tickLogNext r12 true = r13)
    : (tickLogStages r0 log2 tickLogStageData).2 =
      (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor log2 (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50))) := by
  simp only [tickLogStageData, tickLogStages, tickLogWord, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

end Benchmarks.UniswapV4PoolManager
