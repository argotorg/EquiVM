import Benchmarks.CurveVault.MutationSites
import Benchmarks.CurveVault.ConversionArguments
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_013
import Benchmarks.CurveVault.RuntimeBlocks_016
import Benchmarks.CurveVault.RuntimeBlocks_018

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

namespace VaultFlow
def conversionToShares : VaultFlow → Bool
  | .deposit | .withdraw => true | .mint | .redeem => false
def conversionFloor : VaultFlow → Bool
  | .deposit | .redeem => true | .mint | .withdraw => false
def conversionEntry : VaultFlow → Nat
  | .deposit => 2498 | .mint => 3320 | .withdraw => 4381 | .redeem => 5232
def conversionNext : VaultFlow → Nat
  | .deposit => 2530 | .mint => 3359 | .withdraw => 4412 | .redeem => 5272
def conversionTotalOffset (flow : VaultFlow) : Nat := if flow.conversionToShares then 640 else 672
end VaultFlow

def vaultMutationConversionBase (flow : VaultFlow) (mem : ByteArray) (total : UInt256) : ByteArray :=
  if flow.conversionToShares then mem else total.toByteArray.write 0 mem 640 32

theorem vaultMutationConversionBase_frame (flow : VaultFlow) (mem : ByteArray) (total : UInt256) :
    WordMemoryRange mem (vaultMutationConversionBase flow mem total) 0 640 := by
  cases flow with
  | deposit | withdraw => exact WordMemoryRange.refl _ _ _
  | mint | redeem =>
    exact wordMemoryRange_write _ _ 640 0 640
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by omega))) (Or.inl (by omega))

theorem vaultMutationConversionSetup (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256}
    (hsize : flow.conversionTotalOffset + 32 ≤ mem.size)
    (hmt : memLoad (UInt256.ofNat flow.conversionTotalOffset) mem = total)
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.conversionEntry) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0
      (if flow.conversionToShares then UInt256.ofNat 7108 else UInt256.ofNat 7332)
      (UInt256.ofNat 704 :: UInt256.ofNat flow.conversionNext :: R)
      (vaultConversionArgsMemory (vaultMutationConversionBase flow mem total) (calldataWord I.calldata 4)
        (if flow.conversionFloor then ⟨1⟩ else ⟨0⟩) total) aw' rdata σ k' C' := by
  let baseMem := vaultMutationConversionBase flow mem total
  let flag : UInt256 := if flow.conversionFloor then ⟨1⟩ else ⟨0⟩
  let partialMem := flag.toByteArray.write 0 ((calldataWord I.calldata 4).toByteArray.write 0 baseMem 320 32) 352 32
  have hgap (m : ByteArray) (off : Nat) (hoff : off ≤ 640) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hbaseSize : 672 ≤ baseMem.size := by
    cases flow with
    | deposit | withdraw => exact hsize
    | mint | redeem => exact toByteArray_write_size_ge_off_add32 _ _ 640 (hgap _ _ (by omega))
  have hbaseTotal : memLoad (UInt256.ofNat 640) baseMem = total := by
    cases flow with
    | deposit | withdraw => exact hmt
    | mint | redeem => exact memLoad_write_back _ _ 640 (by decide +kernel) (hgap _ _ (by omega))
  have hframe : WordMemoryRange baseMem partialMem 416 UInt256.size :=
    (wordMemoryRange_write baseMem (calldataWord I.calldata 4) 320 416 UInt256.size
      (hgap _ _ (by omega)) (Or.inr (by omega))).trans
      (wordMemoryRange_write _ flag 352 416 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega)))
  have htotal : memLoad (UInt256.ofNat 640) partialMem = total :=
    (hframe.load 640 (by omega) (by decide +kernel) hbaseSize (by decide +kernel)).trans hbaseTotal
  let rawBase := if flow.conversionToShares then mem else (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32
  let rawPartial := flag.toByteArray.write 0 ((calldataWord I.calldata 4).toByteArray.write 0 rawBase 320 32) 352 32
  have hraw : ∃ aw' k' C', RD fork vaultBytecode I g s0
      (if flow.conversionToShares then UInt256.ofNat 7108 else UInt256.ofNat 7332)
      (UInt256.ofNat 704 :: UInt256.ofNat flow.conversionNext :: R)
      (vaultConversionArgsMemory rawBase (calldataWord I.calldata 4) flag (memLoad (UInt256.ofNat 640) rawPartial))
      aw' rdata σ k' C' := by
    cases flow
    · exact vaultBlocks.vault_block_2498_packed hstack (by native_decide) h
    · exact vaultBlocks.vault_block_3320_packed hstack (by native_decide) h
    · exact vaultBlocks.vault_block_4381_packed hstack (by native_decide) h
    · exact vaultBlocks.vault_block_5232_packed hstack (by native_decide) h
  have hbaseEq : rawBase = baseMem := by
    cases flow with
    | deposit | withdraw => rfl
    | mint | redeem =>
      change memLoad (UInt256.ofNat 672) mem = total at hmt
      change (memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32 = total.toByteArray.write 0 mem 640 32
      rw [hmt]
  obtain ⟨aw', k', C', rd⟩ := hraw
  dsimp only [rawPartial] at rd
  rw [hbaseEq, htotal] at rd
  exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
