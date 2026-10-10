import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_061

/-! The shared five-word market-parameter encoder, including preservation of its source. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def MarketParamsLoads (mem : ByteArray) (src : UInt256) (p : MarketParamsData) : Prop :=
  memLoad src mem = UInt256.ofNat p.loanToken.toNat ∧
  memLoad (src + UInt256.ofNat 32) mem = UInt256.ofNat p.collateralToken.toNat ∧
  memLoad (src + UInt256.ofNat 64) mem = UInt256.ofNat p.oracle.toNat ∧
  memLoad (src + UInt256.ofNat 96) mem = UInt256.ofNat p.irm.toNat ∧
  memLoad (src + UInt256.ofNat 128) mem = p.lltv

theorem marketParamsEncodeMemory {mem : ByteArray} {src dst : UInt256}
    (p : MarketParamsData) (hmem : src.toNat + 160 ≤ mem.size)
    (hsep : src.toNat + 160 ≤ dst.toNat) (hdst : dst.toNat + 160 < UInt256.size)
    (hloads : MarketParamsLoads mem src p) :
    metaMorphoV1_1_block_12112_memory (mem := mem) (x0 := src) (x1 := dst) =
      wordSequenceMemory mem dst.toNat p.words := by
  have hs : src.toNat + 160 < UInt256.size := by omega
  have hadd (n : Nat) (hn : n ≤ 128) : (dst + UInt256.ofNat n).toNat = dst.toNat + n :=
    uadd_word_ofNat_toNat dst n (by omega)
  have hmask (a : AccountAddress) :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) (UInt256.ofNat a.toNat) = UInt256.ofNat a.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical a)
  let m1 := writeWord mem dst.toNat (UInt256.ofNat p.loanToken.toNat)
  have hm1 : src.toNat + 160 ≤ m1.size := by dsimp [m1]; rw [writeWord_sparse_size]; omega
  have hr1 := wordWindowRead_write (dst.toNat) (UInt256.ofNat p.loanToken.toNat)
    hmem hsep hs (fun off (_ : off + 32 ≤ 160) ↦ rfl)
  let m2 := writeWord m1 (dst.toNat + 32) (UInt256.ofNat p.collateralToken.toNat)
  have hm2 : src.toNat + 160 ≤ m2.size := by dsimp [m2]; rw [writeWord_sparse_size]; omega
  have hr2 := wordWindowRead_write (dst.toNat + 32) (UInt256.ofNat p.collateralToken.toNat)
    hm1 (by omega) hs hr1
  let m3 := writeWord m2 (dst.toNat + 64) (UInt256.ofNat p.oracle.toNat)
  have hm3 : src.toNat + 160 ≤ m3.size := by dsimp [m3]; rw [writeWord_sparse_size]; omega
  have hr3 := wordWindowRead_write (dst.toNat + 64) (UInt256.ofNat p.oracle.toNat)
    hm2 (by omega) hs hr2
  let m4 := writeWord m3 (dst.toNat + 96) (UInt256.ofNat p.irm.toNat)
  have hr4 := wordWindowRead_write (dst.toNat + 96) (UInt256.ofNat p.irm.toNat)
    hm3 (by omega) hs hr3
  dsimp only [m1, m2, m3] at hr2 hr3 hr4
  have hwrite (m : ByteArray) (off : Nat) (w : UInt256) :
      w.toByteArray.write 0 m off 32 = writeWord m off w := rfl
  simp only [metaMorphoV1_1_block_12112_memory, hwrite,
    hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide), hadd 128 (by decide),
    hloads.1, hmask, hr1 32 (by decide), hloads.2.1, hr2 64 (by decide), hloads.2.2.1,
    hr3 96 (by decide), hloads.2.2.2.1, u256_add_comm (UInt256.ofNat 128) src,
    hr4 128 (by decide), hloads.2.2.2.2]
  simp only [MarketParamsData.words, wordSequenceMemory, Nat.add_assoc, Nat.reduceAdd]

set_option maxRecDepth 2000 in
theorem marketParamsEncodeRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 7 ≤ 1024)
    (hmem : src.toNat + 160 ≤ mem.size) (hsep : src.toNat + 160 ≤ dst.toNat)
    (hdst : dst.toNat + 160 < UInt256.size) (hloads : MarketParamsLoads mem src p)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12112⟩ (src :: dst :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (wordSequenceMemory mem dst.toNat p.words) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_12112_packed
    (immWords := wordsOf (immStore v)) hstack hret rd
  exact ⟨aw', k', C', by simpa only [metaMorphoV1_1_block_12112_stack,
    marketParamsEncodeMemory p hmem hsep hdst hloads] using h⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
