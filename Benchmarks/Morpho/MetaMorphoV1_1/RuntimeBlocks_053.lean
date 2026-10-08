import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode
import Benchmarks.Morpho.MetaMorphoV1_1.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1Blocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.sites = [(8892, 32, "_asset"), (9554, 32, "_asset"), (14624, 32, "_asset"), (15675, 32, "_asset"), (9752, 32, "_underlyingDecimals"), (12952, 32, "_cachedDomainSeparator"), (13141, 32, "_cachedChainId"), (12898, 32, "_cachedThis"), (13031, 32, "_hashedName"), (13069, 32, "_hashedVersion"), (4899, 32, "_name"), (4940, 32, "_version"), (6184, 32, "MORPHO"), (6494, 32, "MORPHO"), (8484, 32, "MORPHO"), (9021, 32, "MORPHO"), (9486, 32, "MORPHO"), (12214, 32, "MORPHO"), (13651, 32, "MORPHO"), (13860, 32, "MORPHO"), (14958, 32, "MORPHO"), (15902, 32, "MORPHO"), (16145, 32, "MORPHO"), (17851, 32, "MORPHO"), (18804, 32, "MORPHO"), (19479, 32, "MORPHO"), (3680, 32, "DECIMALS_OFFSET"), (9716, 32, "DECIMALS_OFFSET"), (14387, 32, "DECIMALS_OFFSET"), (14457, 32, "DECIMALS_OFFSET"), (15259, 32, "DECIMALS_OFFSET"), (15326, 32, "DECIMALS_OFFSET")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.inBounds Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords).size = Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10683_fallthrough`. -/
def metaMorphoV1_1_block_10683_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 10683. -/
theorem metaMorphoV1_1_block_10683_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10688) (metaMorphoV1_1_block_10683_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10683⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 7782) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10684⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7782), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10687⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10688)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10683_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10688) (metaMorphoV1_1_block_10683_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10683_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10688. -/
theorem metaMorphoV1_1_block_10688 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10688) (x0 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)) ByteArray.empty := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10688⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10689⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10690⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 16) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10691⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 16), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10693⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10695⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10696⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10697⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10699⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10700⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10701⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10702⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 7305572981436849421498719419792676155618257611419054616042236861068758356256) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10703⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 7305572981436849421498719419792676155618257611419054616042236861068758356256), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10736⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10737⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genLog3 r15 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10738⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  exact r16.stop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10739⟩ : UInt256), UInt8.ofNat 0, .STOP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10740`. -/
def metaMorphoV1_1_block_10740_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 8) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10740. -/
theorem metaMorphoV1_1_block_10740 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10683) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10740) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (metaMorphoV1_1_block_10740_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10740⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10741⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 8) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10742⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 8), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10744⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10745⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10747⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10749⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10751⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10752⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10753⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10754⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10755⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10756⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 10683) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10757⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10683), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10760⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10683)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10740_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10683) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10740) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10683) (metaMorphoV1_1_block_10740_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10740 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10761`. -/
def metaMorphoV1_1_block_10761_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 10) (⟨0⟩ : UInt256)))))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10761. -/
theorem metaMorphoV1_1_block_10761 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10677) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10761) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (metaMorphoV1_1_block_10761_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10761⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10762⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 10) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10763⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 10), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10765⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10766⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10768⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10770⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10772⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10773⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10774⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10775⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10776⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10777⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 10677) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10778⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10677), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10781⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10677)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10761_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 10677) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10761) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10677) (metaMorphoV1_1_block_10761_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_10761 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10782. -/
theorem metaMorphoV1_1_block_10782_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10782) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10782⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10783⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10784⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10787⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10782_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10782) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10782_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10782. -/
theorem metaMorphoV1_1_block_10782_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10782) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10782⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10783⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10784⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10787⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10788)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10782_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10782) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10782_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10788. -/
theorem metaMorphoV1_1_block_10788_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10788⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10790⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10791⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10793⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10794⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10795⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10796⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10799⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10788_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10788_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10788. -/
theorem metaMorphoV1_1_block_10788_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10800) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10788⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10790⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10791⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10793⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10794⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10795⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10796⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10799⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10800)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10788_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10788) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10800) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10788_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10800`. -/
def metaMorphoV1_1_block_10800_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3483) :: (UInt256.ofNat 10815) :: (UInt256.ofNat 1578) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10800. -/
theorem metaMorphoV1_1_block_10800 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12205) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10800) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12205) (metaMorphoV1_1_block_10800_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10800⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1578) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10802⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1578), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10815) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10805⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10815), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3483) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10808⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 3483), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12205) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10811⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12205), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10814⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12205)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10800_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12205) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10800) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12205) (metaMorphoV1_1_block_10800_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10800 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10815`. -/
def metaMorphoV1_1_block_10815_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10815. -/
theorem metaMorphoV1_1_block_10815 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14377) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10815) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14377) (metaMorphoV1_1_block_10815_stack (ee := ee) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10815⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10816⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10818⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14377) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10819⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14377), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10822⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14377)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10815_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14377) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10815) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14377) (metaMorphoV1_1_block_10815_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10815 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10823. -/
theorem metaMorphoV1_1_block_10823_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10823) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10823⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10824⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10825⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10828⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10823_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10823) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10823_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10823. -/
theorem metaMorphoV1_1_block_10823_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10823) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10823⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10824⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10825⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10828⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10829)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10823_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10823) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10823_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10829. -/
theorem metaMorphoV1_1_block_10829_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10829⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10831⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10832⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10834⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10835⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10836⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10837⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10840⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10829_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10829_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10829. -/
theorem metaMorphoV1_1_block_10829_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10841) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10829⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10831⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10832⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10834⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10835⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10836⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10837⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10840⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10841)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10829_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 64)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10829) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10841) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10829_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10841`. -/
def metaMorphoV1_1_block_10841_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 10851) :: (UInt256.ofNat 4111) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10841. -/
theorem metaMorphoV1_1_block_10841 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11121) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10841) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11121) (metaMorphoV1_1_block_10841_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4111) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10841⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4111), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10851) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10844⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10851), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11121) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10847⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11121), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10850⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11121)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10841_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11121) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10841) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11121) (metaMorphoV1_1_block_10841_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10841 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_10851`. -/
def metaMorphoV1_1_block_10851_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10851. -/
theorem metaMorphoV1_1_block_10851 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 16650) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10851) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 16650) (metaMorphoV1_1_block_10851_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10851⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10852⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10854⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10855⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10856⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 16650) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10857⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16650), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10860⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16650)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10851_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 16650) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10851) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 16650) (metaMorphoV1_1_block_10851_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10851 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10861. -/
theorem metaMorphoV1_1_block_10861_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10861) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10861⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10862⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10863⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10866⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10861_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10861) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10861_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10861. -/
theorem metaMorphoV1_1_block_10861_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10861) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10861⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.callvalue (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10862⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10863⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10866⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10867)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10861_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10861) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10861_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10867. -/
theorem metaMorphoV1_1_block_10867_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10867⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10868⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10869⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10871⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10872⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10873⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10874⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10877⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 917)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10867_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 917) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 917) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10867_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10867. -/
theorem metaMorphoV1_1_block_10867_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10878) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10867⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10868⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10869⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10871⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10872⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10873⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 917) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10874⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨10877⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10878)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_10867_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10867) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 10878) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_10867_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1Blocks
