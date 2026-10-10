import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSlotRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSetup
import Benchmarks.Morpho.MetaMorphoV1_1.StaticCallSimulation

/-! Last-update call-buffer encoding and the shared source/bytecode STATICCALL. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem lastUpdateEncodeCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr array slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hin : array.toNat + 64 ≤ mem.size) (hbelow : array.toNat + 64 ≤ ptr.toNat)
    (hfit : ptr.toNat + 100 < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlen : memLoad array mem = ⟨1⟩) (hslot : memLoad (array + ⟨32⟩) mem = slot)
    (rd : RD (deployedRuntime v) I g s0 ⟨9039⟩ (array :: ⟨0⟩ :: ⟨9065⟩ :: R)
      mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨9111⟩
      (gasArg :: UInt256.ofNat v.MORPHO.toNat :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ :: ptr :: R)
      (extSloadsCallMem mem ptr.toNat slot) aw' rdata σ k' C' := by
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hm : metaMorphoV1_1_block_9039_memory (mem := mem) =
      writeWord mem ptr.toNat extSloadsSelectorWord := by
    unfold metaMorphoV1_1_block_9039_memory
    rw [hf]
    rfl
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_9039_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_9039_stack, hf, hm] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := extSloadsEncodeReturn v
    (by simp only [List.length_cons]; omega) hin hbelow hfit hlen hslot
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have r3 := metaMorphoV1_1_block_9065 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  have hclean : UInt256.land (EVM.Word.ofNat (↑v.MORPHO : Nat)) solcAddrMask =
      UInt256.ofNat v.MORPHO.toNat := addressWord_val_clean v.MORPHO
  simp only [metaMorphoV1_1_block_9065_stack, word_add_sub_left, hmask,
    wordsOf_immStore_MORPHO, u256_land_comm solcAddrMask, hclean] at r3
  exact ⟨_, aw2, _, _, r3⟩

theorem lastUpdateStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr slot gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨9111⟩
      (gasArg :: UInt256.ofNat v.MORPHO.toNat :: ptr :: ⟨100⟩ :: ptr :: ⟨0⟩ :: ptr :: R)
      (extSloadsCallMem mem ptr.toNat slot) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm v.MORPHO "extSloads" 0 [.array [wordBytes32Value slot]]
        (ok, evm', out) false ∧ SourceState s0 I evm'.accountMap evm' ∧
      out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨9112⟩ ((if ok then ⟨1⟩ else ⟨0⟩) :: ptr :: R)
        (extSloadsCallMem mem ptr.toNat slot) aw' out evm'.accountMap k' C' := by
  obtain ⟨evm', ok, out, aw', k', C', hcall, hs', hout, r1⟩ :=
    typedStaticcallSimulation (cfg := config) (address := v.MORPHO) (name := "extSloads")
      (args := [.array [wordBytes32Value slot]])
      (by simpa only [List.length_cons] using hstack)
      (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨9111⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
          immutableLayout_inBounds, immutableTemplate_size64)) hs
      (by rw [accountAddress_ofUInt256_eq_ofNat_toNat]; exact (addressOfWordOfNat _).symm)
      (by
        change _ = some ((extSloadsCallMem mem ptr.toNat slot).readWithPadding ptr.toNat 100)
        rw [extSloadsEncode, extSloadsCallMem_read]) rd
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    apply u256_inj
    change min 0 (UInt256.ofNat out.size).toNat = 0
    exact Nat.zero_min _
  simp only [hmin, show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_write_len_zero] at r1
  exact ⟨evm', ok, out, aw', k', C', hcall, hs', hout, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
