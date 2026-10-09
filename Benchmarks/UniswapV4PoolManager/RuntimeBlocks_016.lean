import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.UniswapV4PoolManager.Bytecode
import Benchmarks.UniswapV4PoolManager.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace poolManagerBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.UniswapV4PoolManager.immutableLayout.sites = [(13606, 32, "original")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.UniswapV4PoolManager.immutableLayout.inBounds Benchmarks.UniswapV4PoolManager.poolManagerBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.UniswapV4PoolManager.poolManagerBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords).size = Benchmarks.UniswapV4PoolManager.poolManagerBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Automatically generated RD summary for bytecode block at pc 5015. -/
theorem poolManager_block_5015 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5015) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5015⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 104192673553174101138321129715474438949748936153505511482015284647762482692096) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5016⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 104192673553174101138321129715474438949748936153505511482015284647762482692096), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5049⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5050⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5051⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5053⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5054⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5056⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r8 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5057⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5058. -/
theorem poolManager_block_5058 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5058) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5058⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 68) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5059⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5061⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5062⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5063⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5065⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5066⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 49946283186677520417587053977908610890222359700026698888885427894795085283328) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5067⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 49946283186677520417587053977908610890222359700026698888885427894795085283328), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5100⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5101⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5102⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5104⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5105⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5106⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5107⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5109⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5110⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5111⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r18 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5112⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5113. -/
theorem poolManager_block_5113 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5113) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5113⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 105800607261278912725083386890480066866062597099005441148730534182315477696512) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5114⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 105800607261278912725083386890480066866062597099005441148730534182315477696512), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5147⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5148⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5149⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5151⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5152⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5154⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r8 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5155⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5156. -/
theorem poolManager_block_5156 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5156) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5156⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 82773506439673006985973338043435030183270660902763811874058968482724049846272) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5157⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 82773506439673006985973338043435030183270660902763811874058968482724049846272), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5190⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5191⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5192⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5194⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5195⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5197⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r8 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5198⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5199. -/
theorem poolManager_block_5199_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5199) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5199⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5200⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5201⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5204⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5199_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5199) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5199_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5199. -/
theorem poolManager_block_5199_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5199) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5199⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5200⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5201⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5204⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5205)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5199_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5199) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5199_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5205. -/
theorem poolManager_block_5205_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 320)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw rdata σ (k + 7) (C + ((27))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5205⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 320), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5208⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5241⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5242⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5243⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5244⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5247⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5205_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 320)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5205_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5205. -/
theorem poolManager_block_5205_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 320)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5248) R mem aw rdata σ (k + 7) (C + ((27))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5205⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 320), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5208⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5241⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5242⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5243⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5244⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5247⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5248)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5205_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932)) (UInt256.ofNat 320)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5205) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5248) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5205_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5248`. -/
def poolManager_block_5248_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 5256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5248. -/
theorem poolManager_block_5248 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11905) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5248) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11905) (poolManager_block_5248_stack (ee := ee) (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5256) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5248⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5251⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11905) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5252⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11905), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5255⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11905)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5248_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11905) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5248) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11905) (poolManager_block_5248_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5248 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5256. -/
theorem poolManager_block_5256_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772)) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5256) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5256⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5257⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5259⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5292⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5293⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5294⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5295⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5298⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5256_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772)) (UInt256.ofNat 128)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5256) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5256_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5256. -/
theorem poolManager_block_5256_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5256) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5299) R mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5256⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5257⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5259⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5292⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5293⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5294⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5295⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5298⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5299)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5256_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639772)) (UInt256.ofNat 128)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5256) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5299) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5256_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5299`. -/
def poolManager_block_5299_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 5311) :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5299. -/
theorem poolManager_block_5299 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11738) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5299) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11738) (poolManager_block_5299_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5299⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5301⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5302⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5311) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5303⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5311), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5306⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11738) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5307⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11738), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5310⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11738)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5299_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 11738) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5299) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 11738) (poolManager_block_5299_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5299 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5311_taken`. -/
def poolManager_block_5311_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5311. -/
theorem poolManager_block_5311_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5311) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5311_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5311⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 164) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5312⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 164), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5314⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5315⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5316⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5318⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5319⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5320⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5321⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5324⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5311_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5311) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5311_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5311_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5311_fallthrough`. -/
def poolManager_block_5311_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5311. -/
theorem poolManager_block_5311_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5311) R mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (poolManager_block_5311_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 10) (C + ((37))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5311⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 164) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5312⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 164), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5314⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5315⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5316⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5318⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5319⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5320⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5321⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5324⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5325)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5311_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5311) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (poolManager_block_5311_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5311_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5325_taken`. -/
def poolManager_block_5325_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `poolManager_block_5325_taken`. -/
def poolManager_block_5325_taken_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5325. -/
theorem poolManager_block_5325_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5325_taken_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5325_taken_memory (mem := mem) (x0 := x0) (x2 := x2)) (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((42) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5325⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5326⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 196) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5327⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 196), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5329⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5330⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5331⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5333⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5334⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5335⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5336⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5339⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5325_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5325_taken_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5325_taken_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5325_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5325_fallthrough`. -/
def poolManager_block_5325_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `poolManager_block_5325_fallthrough`. -/
def poolManager_block_5325_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5325. -/
theorem poolManager_block_5325_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (poolManager_block_5325_fallthrough_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5325_fallthrough_memory (mem := mem) (x0 := x0) (x2 := x2)) (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((42) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5325⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5326⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 196) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5327⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 196), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5329⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5330⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5331⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.signextend (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5333⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5334⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5335⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5336⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5339⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5340)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5325_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) (UInt256.signextend (UInt256.ofNat 2) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5325) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (poolManager_block_5325_fallthrough_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5325_fallthrough_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5325_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5340_taken`. -/
def poolManager_block_5340_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `poolManager_block_5340_taken`. -/
def poolManager_block_5340_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (x2 + (UInt256.ofNat 32)).toNat 32) (x2 + (UInt256.ofNat 64)).toNat 32) (x2 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5340. -/
theorem poolManager_block_5340_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5340_taken_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5340_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) (M (M (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((76) + (memExpansionCost aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5340⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5342⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5343⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5344⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 228) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5345⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 228), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5347⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5348⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5350⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5351⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5352⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 260) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5353⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 260), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5356⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5357⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5359⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5360⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5361⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 292) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5362⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 292), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5365⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5366⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5375⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5376⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5377⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5380⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 816)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5340_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.ofNat 18446744073709551615)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 816) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 816) (poolManager_block_5340_taken_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5340_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5340_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5340_fallthrough`. -/
def poolManager_block_5340_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `poolManager_block_5340_fallthrough`. -/
def poolManager_block_5340_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (x2 + (UInt256.ofNat 32)).toNat 32) (x2 + (UInt256.ofNat 64)).toNat 32) (x2 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5340. -/
theorem poolManager_block_5340_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5381) (poolManager_block_5340_fallthrough_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5340_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) (M (M (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((76) + (memExpansionCost aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5340⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5342⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5343⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5344⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 228) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5345⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 228), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5347⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5348⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5350⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5351⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5352⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 260) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5353⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 260), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5356⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5357⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5359⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5360⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5361⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 292) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5362⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 292), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.calldataload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5365⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5366⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5375⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.gt (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5376⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 816) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5377⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 816), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jumpiNT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5380⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5381)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5340_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.ofNat 18446744073709551615)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5340) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5381) (poolManager_block_5340_fallthrough_stack (ee := ee) (x1 := x1) (x2 := x2) (R := R)) (poolManager_block_5340_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5340_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5381`. -/
def poolManager_block_5381_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 5394) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5381. -/
theorem poolManager_block_5381 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 12109) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5381) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (poolManager_block_5381_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5394) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5381⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5394), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5384⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldatasize (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5385⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5386⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5387⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5389⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 12109) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5390⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12109), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5393⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12109)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5381_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 12109) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5381) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 12109) (poolManager_block_5381_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5381 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `poolManager_block_5394_taken`. -/
def poolManager_block_5394_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5394. -/
theorem poolManager_block_5394_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 1239) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5394) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 1239) (poolManager_block_5394_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 8) (C + ((26) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5394⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5395⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5396⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5397⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.tload (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5430⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5431⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1239) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5432⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1239), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨5435⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1239)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem poolManager_block_5394_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (UInt256.ofNat 87100234046427240614499661373387320107015461065347489303548037305558901893923) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) 0).contains (UInt256.ofNat 1239) = true)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 5394) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 1239) (poolManager_block_5394_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (poolManager_block_5394_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end poolManagerBlocks
