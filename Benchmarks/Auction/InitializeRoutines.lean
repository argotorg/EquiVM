import Benchmarks.Auction.InitializeEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionInitializePausableUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4993⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
  have rd4994 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd4995₀⟩ := rd4994.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4995⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4996⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4995₀⟩
  have rd5004₀ := evm_run rd4995 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5016 := evm_run rd5004₀ with [
    push2 ⟨5016⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5044 := evm_run rd5016 with [
    push2 ⟨5044⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5045 := evm_run rd5044 with [push0]
  obtain ⟨_, _, rd5046₀⟩ := rd5045.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5046⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5047⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5046₀⟩
  have rd5058₀ := evm_run rd5046 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5058 := rd5058₀
  rw [hiz] at rd5058
  have rd5076 := evm_run rd5058 with [
    push2 ⟨5076⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd5080₀ := evm_run rd5076 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd5081₀⟩ := rd5080₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5081⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5081⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ⟨0⟩ :: ret :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5081₀⟩
  have rd5086₀ := evm_run rd5081 with [push1 ⟨255⟩, not, and, swap1]
  have hclear : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      auctionPausedSetFalseWord (auctionSlotWord ⟨51⟩ σ I) := by
    rw [u256_land_comm]
    rfl
  have rd5086 := rd5086₀
  rw [hclear] at rd5086
  obtain ⟨_, _, rd5087₀⟩ := rd5086.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5087⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5087⟩ (⟨0⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionUnpausePostMap] using rd5087₀⟩
  have rd2850 := evm_run rd5087 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeNoop_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨4892⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have rd4894 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd4895₀⟩ := rd4894.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4895⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4895⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4895₀⟩
  have rd4904₀ := evm_run rd4895 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd4915 := evm_run rd4904₀ with [
    push2 ⟨4915⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4943 := evm_run rd4915 with [
    push2 ⟨4943⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4945 := evm_run rd4943 with [push0]
  obtain ⟨_, _, rd4946₀⟩ := rd4945.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4946⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4946⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4946₀⟩
  have rd4957₀ := evm_run rd4946 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd4957 := rd4957₀
  rw [hiz] at rd4957
  have rd3877 := evm_run rd4957 with [
    push2 ⟨3877⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd2850 := evm_run rd3877 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializePausable_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3778⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, auctionUnpausePostMap σ I) k C := by
  have rd3779 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3780₀⟩ := rd3779.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3780⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3781⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3780₀⟩
  have rd3789₀ := evm_run rd3780 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd3801 := evm_run rd3789₀ with [
    push2 ⟨3801⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3829 := evm_run rd3801 with [
    push2 ⟨3829⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3831 := evm_run rd3829 with [push0]
  obtain ⟨_, _, rd3832₀⟩ := rd3831.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3832⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3832⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3832₀⟩
  have rd3843₀ := evm_run rd3832 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd3843 := rd3843₀
  rw [hiz] at rd3843
  have rd3861 := evm_run rd3843 with [
    push2 ⟨3861⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd4892 := evm_run rd3861 with [push2 ⟨3869⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3869⟩ := auctionInitializeNoop_nested (σ := σ) (g := g)
    (ret := ⟨3869⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd4892
  have rd4993 := evm_run rd3869 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨4993⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializePausableUnchained_nested (σ := σ) (g := g)
    (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega) hperm hnz (by jump_dest) rd4993
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeReentrancyGuardUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5105⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
  have rd5106 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd5107₀⟩ := rd5106.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5107⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5108⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5107₀⟩
  have rd5116₀ := evm_run rd5107 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5128 := evm_run rd5116₀ with [
    push2 ⟨5128⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5156 := evm_run rd5128 with [
    push2 ⟨5156⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5157 := evm_run rd5156 with [push0]
  obtain ⟨_, _, rd5158₀⟩ := rd5157.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5158⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5159⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5158₀⟩
  have rd5169₀ := evm_run rd5158 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5169 := rd5169₀
  rw [hiz] at rd5169
  have rd5188 := evm_run rd5169 with [
    push2 ⟨5188⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd5192 := evm_run rd5188 with [push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd5193₀⟩ := rd5192.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5193⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5194⟩ (⟨0⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap] using rd5193₀⟩
  have rd2850 := evm_run rd5193 with [
    dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeReentrancyGuard_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3896⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k C := by
  have rd3897 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3898₀⟩ := rd3897.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3898⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3899⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3898₀⟩
  have rd3907₀ := evm_run rd3898 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd3919 := evm_run rd3907₀ with [
    push2 ⟨3919⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3947 := evm_run rd3919 with [
    push2 ⟨3947⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd3949 := evm_run rd3947 with [push0]
  obtain ⟨_, _, rd3950₀⟩ := rd3949.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3950⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3950⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3950₀⟩
  have rd3961₀ := evm_run rd3950 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd3961 := rd3961₀
  rw [hiz] at rd3961
  have rd3979 := evm_run rd3961 with [
    push2 ⟨3979⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd5105 := evm_run rd3979 with [push2 ⟨3877⟩, push2 ⟨5105⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializeReentrancyGuardUnchained_nested (σ := σ)
    (g := g) (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega) hperm hnz (by jump_dest) rd5105
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionSetOwnerRoutine {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {newOwner ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3574⟩
      (newOwner :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I newOwner) k C := by
  have rd3578₀ := evm_run h with [jumpdest, push1 ⟨151⟩, dup1]
  obtain ⟨_, _, rd3579₀⟩ := rd3578₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3579⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3579⟩
      (auctionSlotWord ⟨151⟩ σ I :: ⟨151⟩ :: newOwner :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3579₀⟩
  have hsolcMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hpostComm :
      UInt256.lor (UInt256.land solcAddrMask newOwner)
          (UInt256.land (auctionSlotWord ⟨151⟩ σ I) (UInt256.lnot solcAddrMask)) =
        auctionSetOwnerWord (auctionSlotWord ⟨151⟩ σ I) newOwner := by
    rw [u256_land_comm solcAddrMask newOwner]
    unfold auctionSetOwnerWord setAddressOffset0Word
    rw [u256_lor_comm]
  have rd3605₀ := evm_run rd3579 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, dup4, and, dup2, lor,
    swap1, swap4]
  have rd3605 := rd3605₀
  rw [hsolcMask] at rd3605
  rw [hpostComm] at rd3605
  obtain ⟨_, _, rd3606₀⟩ := rd3605.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3606⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3606⟩
      (solcAddrMask :: auctionSlotWord ⟨151⟩ σ I :: UInt256.land solcAddrMask newOwner ::
        newOwner :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I newOwner) k C := by
    exact ⟨_, _, by simpa [auctionSetOwnerPostMap] using rd3606₀⟩
  have rd3615 := evm_run rd3606 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by native_decide) (by evm_ov),
    swap2, and, swap2, swap1, dup3, swap1]
  have rd3648 := rd3615.pushConst auctionOwnershipTransferredTopic
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd3652 := evm_run rd3648 with [swap1, push0, swap1]
  have rd3653 := RD.log3 0 (UInt256.ofNat 3) rd3652 (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3653 with [pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeOwnableUnchained_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 990)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5212⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I (auctionSourceWord I)) k C := by
  have rd5213 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd5214₀⟩ := rd5213.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5214⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5215⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5214₀⟩
  have rd5223₀ := evm_run rd5214 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd5235 := evm_run rd5223₀ with [
    push2 ⟨5235⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5263 := evm_run rd5235 with [
    push2 ⟨5263⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd5264 := evm_run rd5263 with [push0]
  obtain ⟨_, _, rd5265₀⟩ := rd5264.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5265⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨5266⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd5265₀⟩
  have rd5277₀ := evm_run rd5265 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd5277 := rd5277₀
  rw [hiz] at rd5277
  have rd5295 := evm_run rd5277 with [
    push2 ⟨5295⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd3574 := evm_run rd5295 with [
    push2 ⟨3877⟩, caller, push2 ⟨3574⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionSetOwnerRoutine (σ := σ) (g := g)
    (newOwner := auctionSourceWord I) (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega)
    hperm (by jump_dest) (by simpa [auctionSourceWord] using rd3574)
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeOwnable_nested {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (hperm : I.perm = true)
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3987⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionSetOwnerPostMap σ I (auctionSourceWord I)) k C := by
  have rd3988 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, rd3989₀⟩ := rd3988.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3989⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3990⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3989₀⟩
  have rd3998₀ := evm_run rd3989 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hcomm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hcomm] using hnz
  have rd4010 := evm_run rd3998₀ with [
    push2 ⟨4010⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4038 := evm_run rd4010 with [
    push2 ⟨4038⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd4039 := evm_run rd4038 with [push0]
  obtain ⟨_, _, rd4040₀⟩ := rd4039.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4040⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨4041⟩
      (auctionSlotWord ⟨0⟩ σ I :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd4040₀⟩
  have rd4052₀ := evm_run rd4040 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd4052 := rd4052₀
  rw [hiz] at rd4052
  have rd4070 := evm_run rd4052 with [
    push2 ⟨4070⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd4892 := evm_run rd4070 with [push2 ⟨4078⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4078⟩ := auctionInitializeNoop_nested (σ := σ) (g := g)
    (ret := ⟨4078⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd4892
  have rd5212 := evm_run rd4078 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨5212⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3877⟩ := auctionInitializeOwnableUnchained_nested (σ := σ) (g := g)
    (ret := ⟨3877⟩) (R := ⟨0⟩ :: ret :: R) (by simp only [List.length_cons]; omega) hperm hnz (by jump_dest) rd5212
  have rd2850 := evm_run rd3877 with [
    jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2850 with [pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionPauseRoutine_success {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 1000)
    (hperm : I.perm = true)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, auctionPausePostMap σ I) k C := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) ≠ ⟨0⟩ := by
    rw [hmask, hzero]
    decide
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd3734₀ := evm_run rd3725 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730₀⟩ := rd3734₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3730⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3730⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3730₀⟩
  have rd3737₀ := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd3737₁ := rd3737₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I)
  rw [hland] at rd3737₁
  have rd3737₂ := RD.lor rd3737₁ (by native_decide) (by evm_ov)
  have hlor :
      UInt256.lor ⟨1⟩
          (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I) := by
    unfold auctionPausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd3737₂
  have rd3738 := evm_run rd3737₂ with [swap1]
  obtain ⟨_, _, rd3739₀⟩ := rd3738.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3739⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3739⟩ (ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionPausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionPausePostMap] using rd3739₀⟩
  have rd3772 := rd3739.pushConst
    (⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  have rd2988₀ := evm_run rd2971 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  have rd2991 := evm_run rd2988 with [
    raw mstore 6 (auctionEventMem I) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd2998₀ := evm_run rd2991 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (auctionEventMem_mload64 I) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  have rd2999 := RD.log1 0 (UInt256.ofNat 5) rd2998 (by native_decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2999 with [jump hret]⟩



end Auction
