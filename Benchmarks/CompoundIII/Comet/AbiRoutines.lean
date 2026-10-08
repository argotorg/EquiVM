import Benchmarks.CompoundIII.Comet.GetterCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES Reasoning.Solc.solcCalldataStaticLenCheckOk to the NOT/ADD spelling.
theorem calldataLength_ok {size need : Nat} (hn : need < 2 ^ 255)
    (hlo : need + 4 ≤ size) (hhi : size < 2 ^ 255 + 4) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat need) = ⟨0⟩ := by
  rw [lnot3_add_returnSize (by omega) hsize]
  exact slt_ofNat_lit_zero hn (by omega) (by omega)

theorem calldataLength_short {size need : Nat} (hn : need < 2 ^ 255) (hsz : 4 ≤ size)
    (hlo : size < need + 4) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat need) ≠ ⟨0⟩ := by
  rw [lnot3_add_returnSize hsz hsize, slt_ofNat_lit_one_low hn (by omega)]
  decide

theorem calldataLength_huge {size need : Nat} (hn : need < 2 ^ 255)
    (hhi : 2 ^ 255 + 4 ≤ size) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat need) ≠ ⟨0⟩ := by
  rw [lnot3_add_returnSize (by omega) hsize]
  have hs := slt_lit_one_high (a := UInt256.ofNat (size - 4)) hn (by
    rw [ulit_toNat' _ (by omega)]
    omega)
  rw [hs]
  decide

theorem cometValidateAddress_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hcanon : w.toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨1393⟩ (w :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C' := by
  have hcond : UInt256.sub (UInt256.land w
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))) w = UInt256.ofNat 0 := by
    change UInt256.sub (UInt256.land w solcAddrMask) w = ⟨0⟩
    rw [solcAddrMask_clean hcanon, u256_sub_self]
  have rd1 := cometWithExtendedAssetList_block_1393_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hcond h
  have rd2 := cometWithExtendedAssetList_block_1409
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
  exact ⟨_, _, rd2⟩

set_option maxRecDepth 10000 in
theorem cometValidateAddress_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hcanon : ¬ w.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 ⟨1393⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hne : UInt256.land w solcAddrMask ≠ w := by
    intro heq
    have hc := solcAddrMask_result_canonical w
    rw [heq] at hc
    exact hcanon hc
  have hcond : UInt256.sub (UInt256.land w
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))) w ≠ UInt256.ofNat 0 := by
    change UInt256.sub (UInt256.land w solcAddrMask) w ≠ ⟨0⟩
    exact u256_sub_ne_zero_of_ne hne
  have rd1 := cometWithExtendedAssetList_block_1393_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometRevert1410 (by change R.length + 2 ≤ 1024; omega) rd1

end Benchmarks.CompoundIII.Comet
