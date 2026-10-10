import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

-- The generated event block requires write permission at LOG3.
theorem swapWrapperEventStatic {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 1766) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
 :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1766⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1767⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1768⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1769⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1790⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1791⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1792⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1793⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup15 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1794⟩ : UInt256), UInt8.ofNat 142, .DUP15, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1795⟩ : UInt256), UInt8.ofNat 111, .Push .PUSH16, some ((UInt256.ofNat 340282366920938463463374607431768211455), 16), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1812⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1814⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1815⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1816⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1817⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1818⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1819⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMload r17 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1820⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 2) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1821⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.signextend (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1823⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1824⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1825⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMload r22 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1827⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1828⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup9 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1829⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 128) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1830⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.sar (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1832⟩ : UInt256), UInt8.ofNat 29, .SAR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 15) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1833⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.signextend (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1835⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup8 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1836⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := RD.genMstore r30 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1837⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup9 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1838⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 15) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1839⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.signextend (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1841⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1842⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.dup9 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1844⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1845⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := RD.genMstore r37 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1846⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1847⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.dup8 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1849⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1850⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := RD.genMstore r41 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1851⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 96) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1852⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup7 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1854⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1855⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := RD.genMstore r45 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1856⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 128) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1857⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1859⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1860⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := RD.genMstore r49 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1861⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := r50.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1862⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 160) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1863⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r53 := r52.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1865⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r54 := r53.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1866⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r55 := RD.genMstore r54 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1867⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r56 := r55.pushConst (UInt256.ofNat 29361124924822809794027248555348140138322545302739449826051187811167583539503) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1868⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 29361124924822809794027248555348140138322545302739449826051187811167583539503), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 192) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1901⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r58 := r57.caller (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1903⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r59 := r58.swap4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨1904⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.log3Static r59 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords,
      (⟨1905⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)

end Benchmarks.UniswapV4PoolManager
