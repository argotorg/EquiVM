import Benchmarks.EAS.EAS.UIDControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- The provided complete block summaries require write permission; these prefixes stop
-- at the first forbidden SSTORE and use the library's static-halt rule.
theorem easRecordSingle_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+21 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 8511) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8511⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8512⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8513⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8514⟩ : UInt256), UInt8.ofNat 157, .SWAP14, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8515⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8516⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8517⟩ : UInt256), UInt8.ofNat 155, .SWAP12, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8518⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8519⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8520⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8521⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8522⟩ : UInt256), UInt8.ofNat 156, .SWAP13, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8523⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8524⟩ : UInt256), UInt8.ofNat 80, .POP, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8525⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8526⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8527⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8528⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8529⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8530⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8531⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8532⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMstore r22 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8534⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8535⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8537⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8539⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8540⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8542⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r29 := RD.genKeccak256 r28 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8544⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8545⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r31 := RD.genMload r30 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8546⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8547⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r32 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨8548⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)

theorem easRecordMany_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+19 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 10727) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10727⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10728⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10729⟩ : UInt256), UInt8.ofNat 80, .POP, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10730⟩ : UInt256), UInt8.ofNat 154, .SWAP11, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10731⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10732⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10733⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10734⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10735⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10736⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10737⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10738⟩ : UInt256), UInt8.ofNat 154, .SWAP11, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10739⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10740⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10741⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10742⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10743⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10744⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10745⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10746⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMstore r20 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10748⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10749⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10751⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10753⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10754⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10756⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genKeccak256 r26 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10758⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10759⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10760⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r30 := RD.genMload r29 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10761⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10762⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r31 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, wordsOf (immStore v), (⟨10763⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)

theorem easRecordWriteStatic {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src word bump t1 t2 t3 t4 : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+21 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site)
      (word::bump::uidSaved site src (t1::t2::t3::t4::R)) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 => exact easRecordSingle_static v hstack hperm rd
  | many s1 s2 s3 s4 s5 s6 => exact easRecordMany_static v (by omega) hperm rd

end Benchmarks.EAS.EAS
