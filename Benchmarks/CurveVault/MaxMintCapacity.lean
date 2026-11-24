import Benchmarks.CurveVault.Limits
import Benchmarks.CurveVault.ConversionPrefix
import Benchmarks.CurveVault.RuntimeBlocks_012

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMaxMintCapacity {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {limit assets : UInt256} {R : List UInt256}
    (hsize : 704 ≤ mem.size)
    (hl : memLoad (UInt256.ofNat 608) mem = limit)
    (ha : memLoad (UInt256.ofNat 672) mem = assets)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 2947) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 2993)
      (UInt256.sub (wordMax limit assets) assets :: assets :: wordMax limit assets :: UInt256.ofNat 32 :: R)
      (assets.toByteArray.write 0 mem 640 32) aw' rdata σ k' C' := by
  let written := assets.toByteArray.write 0 mem 640 32
  let mx (m : ByteArray) := UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) m)
    (memLoad (UInt256.ofNat 640) m)) (UInt256.xor (memLoad (UInt256.ofNat 640) m)
      (memLoad (UInt256.ofNat 608) m))) (memLoad (UInt256.ofNat 640) m)
  have hgap : 640 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 640 (by norm_num))
  have hl' : memLoad (UInt256.ofNat 608) written = limit := by
    rw [memLoad_below_write _ _ 640 608 (by omega) (by omega) hgap (by decide +kernel), hl]
  have ha' : memLoad (UInt256.ofNat 640) written = assets := memLoad_write_back _ _ 640 (by decide +kernel) hgap
  have hmx : mx written = wordMax limit assets := by dsimp only [mx]; rw [hl', ha', branchlessMax]
  have rd := vaultBlocks.vault_block_2947_fallthrough hstack (by
    rw [ha]
    change UInt256.gt (UInt256.sub (mx written) (memLoad (UInt256.ofNat 640) written)) (mx written) = _
    rw [hmx, ha']
    exact sub_wordMax_noUnderflow limit assets) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 2993)
    (UInt256.sub (mx ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32))
      (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32)) ::
      memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32) ::
      mx ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32) :: UInt256.ofNat 32 :: R)
    ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem 640 32) _ rdata σ _ _ at rd
  rw [ha] at rd
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 2993)
    (UInt256.sub (mx written) (memLoad (UInt256.ofNat 640) written) ::
      memLoad (UInt256.ofNat 640) written :: mx written :: UInt256.ofNat 32 :: R) written _ rdata σ _ _ at rd
  rw [hmx, ha'] at rd
  exact ⟨_, _, _, rd⟩
end Benchmarks.CurveVault
