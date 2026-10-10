import Benchmarks.UniswapV3.Pool.OracleGrowSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_051
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_052
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem uint16Word_clean {w : UInt256} (hw : w.toNat < 2 ^ 16) :
    UInt256.land (UInt256.ofNat 65535) w = w := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat w _ (by decide) hw

theorem oracleGrowStepX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw current next junk ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (i : Nat)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16139⟩
      (UInt256.ofNat i :: junk :: next :: current :: UInt256.ofNat 8 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hnext : next.toNat < 2 ^ 16) (hi : i < next.toNat) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16139⟩
      (UInt256.ofNat (i + 1) :: junk :: next :: current :: UInt256.ofNat 8 :: ret :: R)
      mem aw rdata (storeObservationTimestampOne evm (UInt256.ofNat i)).accountMap k' C' := by
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' i (by change i < 2 ^ 256; omega)
  have hci : UInt256.land (UInt256.ofNat 65535) (UInt256.ofNat i) = UInt256.ofNat i :=
    uint16Word_clean (by rw [hin]; omega)
  have hcn := uint16Word_clean hnext
  have rdCond := uniswapV3Pool_block_16139_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hci, hcn, ult_one (by rw [hin]; exact hi)]; decide) rd
  have rdBound := uniswapV3Pool_block_16156_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [hci, ult_one (by rw [hin]; change i < 65535; change next.toNat < 65536 at hnext; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCond
  simp only [uniswapV3Pool_block_16156_taken_stack, hci] at rdBound
  obtain ⟨_, _, rdStore⟩ := uniswapV3Pool_block_16174 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdBound
  have hplus : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := u256_one_add_ofNat i
  have hs' := SourceState.storeObservationTimestampOne hs (UInt256.ofNat i)
  have hmap := hs'.accounts
  change sstoreAccountMap ee.codeOwner σ (UInt256.ofNat i + UInt256.ofNat 8)
      (UInt256.lor ⟨1⟩ (UInt256.land (UInt256.lnot (UInt256.ofNat 4294967295))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat i + UInt256.ofNat 8) (⟨0⟩ : UInt256))))) =
      (storeObservationTimestampOne evm (UInt256.ofNat i)).accountMap at hmap
  simp only [uniswapV3Pool_block_16174_stack, hplus,
    show UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1) = (⟨1⟩ : UInt256) from by decide,
    hmap] at rdStore
  exact ⟨_, _, rdStore⟩

theorem oracleGrowLoopX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw current next junk ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (i count : Nat)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16139⟩
      (UInt256.ofNat i :: junk :: next :: current :: UInt256.ofNat 8 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hnext : next.toNat < 2 ^ 16) (hsum : i + count = next.toNat) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16207⟩
      (next :: junk :: next :: current :: UInt256.ofNat 8 :: ret :: R)
      mem aw rdata (oracleGrowState evm i count).accountMap k' C' := by
  induction count generalizing evm σ k C i with
  | zero =>
      have hi : i = next.toNat := by omega
      subst i
      rw [u256_ofNat_toNat] at rd
      have hr := uniswapV3Pool_block_16139_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uint16Word_clean hnext, ult_zero (Nat.le_refl _)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      rw [hs.accounts] at hr
      exact ⟨_, _, hr⟩
  | succ count ih =>
      obtain ⟨_, _, rdNext⟩ := oracleGrowStepX (v := v) i rd hs hperm hnext (by omega) hov
      have hsNext : SourceState s0 ee (storeObservationTimestampOne evm (UInt256.ofNat i)).accountMap
          (storeObservationTimestampOne evm (UInt256.ofNat i)) :=
        ⟨(storageStore_σ₀ _ _ _ _).trans hs.world,
          (storeObservationTimestampOne_executionEnv _ _).trans hs.env, rfl⟩
      exact ih (i + 1) rdNext hsNext (by omega)

theorem oracleGrowX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw current next ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16053⟩
      (next :: current :: UInt256.ofNat 8 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hcurrent : current.toNat < 2 ^ 16) (hnext : next.toNat < 2 ^ 16)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ current = ⟨0⟩) ∨
    (0 < current.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (oracleGrowResult current next :: R) mem aw rdata
      (oracleGrowState evm current.toNat (next.toNat - current.toNat)).accountMap k' C') := by
  have hcc := uint16Word_clean hcurrent
  have hcn := uint16Word_clean hnext
  by_cases hz : current = ⟨0⟩
  · have hr := uniswapV3Pool_block_16053_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hcc, hz]; decide) rd
    simp only [uniswapV3Pool_block_16053_fallthrough_stack] at hr
    exact Or.inl ⟨uniswapV3Pool_block_16067 (immWords := wordsOf (immStore v)) (by evm_ov) hr, hz⟩
  · have hpos : 0 < current.toNat := by
      by_contra hn
      exact hz (uint256_toNat_eq_zero (by omega))
    have rdCheck := uniswapV3Pool_block_16053_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hcc, ugt_one (show (UInt256.ofNat 0).toNat < current.toNat from hpos)]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16053_taken_stack] at rdCheck
    refine Or.inr ⟨hpos, ?_⟩
    by_cases hgrow : current.toNat < next.toNat
    · have rdInit := uniswapV3Pool_block_16115_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcn, hcc, ugt_one hgrow]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCheck
      have rdLoop := uniswapV3Pool_block_16137 (immWords := wordsOf (immStore v)) (by evm_ov) rdInit
      simp only [uniswapV3Pool_block_16137_stack] at rdLoop
      rw [← u256_ofNat_toNat current] at rdLoop
      obtain ⟨_, _, rdExit⟩ := oracleGrowLoopX (v := v) current.toNat (next.toNat - current.toNat)
        rdLoop hs hperm hnext (by omega) hov
      have rdDone := uniswapV3Pool_block_16207 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdExit
      rw [oracleGrowResult, if_pos hgrow]
      exact ⟨_, _, rdDone⟩
    · have rdSkip := uniswapV3Pool_block_16115_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcn, hcc]; exact ugt_zero (by omega)) rdCheck
      have rdRet := uniswapV3Pool_block_16131 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdSkip
      simp only [uniswapV3Pool_block_16131_stack] at rdRet
      have rdDone := uniswapV3Pool_block_13186 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdRet
      rw [oracleGrowResult, if_neg hgrow, show next.toNat - current.toNat = 0 by omega, oracleGrowState]
      rw [hs.accounts] at rdDone
      exact ⟨_, _, rdDone⟩

end Benchmarks.UniswapV3.Pool
