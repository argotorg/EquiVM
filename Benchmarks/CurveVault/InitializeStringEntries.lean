import Benchmarks.CurveVault.InitializeStringLoop

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vyperStringWords_small (length : Nat) (hpos : 0 < length) (hcap : length ≤ 64) :
    vyperStringWords (UInt256.ofNat length) = if length ≤ 32 then ⟨2⟩ else ⟨3⟩ := by
  have hlen : (UInt256.ofNat length).toNat = length :=
    ulit_toNat' length (by change length < 2 ^ 256; omega)
  apply u256_inj
  rw [vyperStringWords_normal _ (by omega), hlen]
  split
  · change (length + 63) / 32 = 2
    omega
  · change (length + 63) / 32 = 3
    omega

theorem vaultInitializeNameLoopEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C length : Nat}
    {x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hpos : 0 < length) (hcap : length ≤ 64)
    (hheader : memLoad (UInt256.ofNat 352) mem = UInt256.ofNat length)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 598) (UInt256.ofNat 352 :: x1 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 628)
      (⟨0⟩ :: (if length ≤ 32 then ⟨2⟩ else ⟨3⟩) :: (UInt256.ofNat length + UInt256.ofNat 32) ::
        UInt256.ofNat 352 :: R) mem aw' rdata σ k' C' := by
  have hc := vyperStringWords_small length hpos hcap
  have hg : UInt256.gt (vyperStringWords (UInt256.ofNat length)) (UInt256.ofNat 3) = UInt256.ofNat 0 := by
    rw [hc]; split <;> rfl
  obtain ⟨aw1, k1, C1, rd1⟩ := vaultBlocks.vault_block_598_fallthrough_packed (by omega)
    (by rw [hheader]; exact hg) h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 621)
    (vyperStringWords (memLoad (UInt256.ofNat 352) mem) :: ⟨0⟩ ::
      (memLoad (UInt256.ofNat 352) mem + UInt256.ofNat 32) :: UInt256.ofNat 352 :: R) mem aw1 rdata σ k1 C1 at rd1
  rw [hheader, hc] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := vaultBlocks.vault_block_621_fallthrough_packed
    (by simpa only [List.length_cons] using (show R.length + 3 + 3 ≤ 1024 by omega))
    (by split <;> rfl) rd1
  exact vaultBlocks.vault_block_627_packed (by simpa only [List.length_cons] using
    (show R.length + 2 + 2 ≤ 1024 by omega)) rd2

theorem vaultInitializeSymbolLoopEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C length : Nat}
    {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hpos : 0 < length) (hcap : length ≤ 64)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 768)
      ((UInt256.ofNat 31 + (UInt256.ofNat length + UInt256.ofNat 32)) :: ⟨0⟩ ::
        (UInt256.ofNat length + UInt256.ofNat 32) :: UInt256.ofNat 352 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 786)
      (⟨0⟩ :: (if length ≤ 32 then ⟨2⟩ else ⟨3⟩) :: (UInt256.ofNat length + UInt256.ofNat 32) ::
        UInt256.ofNat 352 :: R) mem aw' rdata σ k' C' := by
  have hc := vyperStringWords_small length hpos hcap
  have hg : UInt256.gt (vyperStringWords (UInt256.ofNat length)) (UInt256.ofNat 3) = UInt256.ofNat 0 := by
    rw [hc]; split <;> rfl
  obtain ⟨aw1, k1, C1, rd1⟩ := vaultBlocks.vault_block_768_fallthrough_packed
    (by simpa only [List.length_cons] using (show R.length + 3 + 3 ≤ 1024 by omega)) hg h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 779)
    (vyperStringWords (UInt256.ofNat length) :: ⟨0⟩ ::
      (UInt256.ofNat length + UInt256.ofNat 32) :: UInt256.ofNat 352 :: R) mem aw1 rdata σ k1 C1 at rd1
  rw [hc] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := vaultBlocks.vault_block_779_fallthrough_packed
    (by simpa only [List.length_cons] using (show R.length + 3 + 3 ≤ 1024 by omega))
    (by split <;> rfl) rd1
  exact vaultBlocks.vault_block_785_packed (by simpa only [List.length_cons] using
    (show R.length + 2 + 2 ≤ 1024 by omega)) rd2

end Benchmarks.CurveVault
