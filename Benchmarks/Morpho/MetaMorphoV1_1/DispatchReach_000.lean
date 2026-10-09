import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_001
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_002

/-! ## Runtime dispatcher paths -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- Dispatcher path to `totalAssets()` (arm entry pc 11049). -/
theorem metaMorphoV1_1ReachTotalAssetsBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 0)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11049)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨31576340⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x01 0xe1 0xd1 0x14 ⟨31576340⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_taken_stack, deployedRuntime] using rd2⟩

/-- Dispatcher path to `name()` (arm entry pc 10884). -/
theorem metaMorphoV1_1ReachNameBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 1)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10884)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨117300739⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨117300739⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd3⟩

/-- Dispatcher path to `convertToAssets(uint256)` (arm entry pc 7734). -/
theorem metaMorphoV1_1ReachConvertToAssetsBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 2)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 7734)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨128110906⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x07 0xa2 0xd1 0x3a ⟨128110906⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd3
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd4⟩

/-- Dispatcher path to `approve(address,uint256)` (arm entry pc 10846). -/
theorem metaMorphoV1_1ReachApproveBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 3)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10846)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨157198259⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨157198259⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd4
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd5⟩

/-- Dispatcher path to `previewWithdraw(uint256)` (arm entry pc 10805). -/
theorem metaMorphoV1_1ReachPreviewWithdrawBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 4)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10805)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨170435703⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x0a 0x28 0xa4 0x77 ⟨170435703⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd6⟩

/-- Dispatcher path to `revokePendingCap(bytes32)` (arm entry pc 10660). -/
theorem metaMorphoV1_1ReachRevokePendingCapBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 5)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10660)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨271547244⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x10 0x2f 0x7b 0x6c ⟨271547244⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd6
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd7⟩

/-- Dispatcher path to `totalSupply()` (arm entry pc 10631). -/
theorem metaMorphoV1_1ReachTotalSupplyBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 6)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10631)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨404098525⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨404098525⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd8⟩

/-- Dispatcher path to `revokePendingGuardian()` (arm entry pc 10526). -/
theorem metaMorphoV1_1ReachRevokePendingGuardianBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 7)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10526)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨516728700⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x1e 0xcc 0xa7 0x7c ⟨516728700⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd8
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd9⟩

/-- Dispatcher path to `lostAssets()` (arm entry pc 10497). -/
theorem metaMorphoV1_1ReachLostAssetsBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 8)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10497)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨566971156⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x21 0xcb 0x4b 0x14 ⟨566971156⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd9
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd10⟩

/-- Dispatcher path to `transferFrom(address,address,uint256)` (arm entry pc 10441). -/
theorem metaMorphoV1_1ReachTransferFromBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 9)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 10441)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨599290589⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨599290589⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd10
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd11⟩

/-- Dispatcher path to `setSupplyQueue(bytes32[])` (arm entry pc 9964). -/
theorem metaMorphoV1_1ReachSetSupplyQueueBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 10)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9964)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨718034681⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2a 0xcc 0x56 0xf9 ⟨718034681⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd11
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd12⟩

/-- Dispatcher path to `setSkimRecipient(address)` (arm entry pc 9855). -/
theorem metaMorphoV1_1ReachSetSkimRecipientBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 11)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9855)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨724605307⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2b 0x30 0x99 0x7b ⟨724605307⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd11
  have rd13 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_144_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨724605307⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd12
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd13⟩

/-- Dispatcher path to `decimals()` (arm entry pc 9744). -/
theorem metaMorphoV1_1ReachDecimalsBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 12)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9744)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨826074471⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨826074471⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd11
  have rd13 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_144_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨724605307⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd12
  have rd14 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_155_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨826074471⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd13
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd14⟩

/-- Dispatcher path to `withdrawQueueLength()` (arm entry pc 9715). -/
theorem metaMorphoV1_1ReachWithdrawQueueLengthBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 13)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9715)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨871964347⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x33 0xf9 0x1e 0xbb ⟨871964347⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd11
  have rd13 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_144_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨724605307⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd12
  have rd14 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_155_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨826074471⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd13
  have rd15 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_166_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨871964347⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd14
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd15⟩

/-- Dispatcher path to `DOMAIN_SEPARATOR()` (arm entry pc 9689). -/
theorem metaMorphoV1_1ReachDOMAIN_SEPARATORBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 14)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9689)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨910484757⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x36 0x44 0xe5 0x15 ⟨910484757⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd11
  have rd13 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_144_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨724605307⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd12
  have rd14 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_155_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨826074471⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd13
  have rd15 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_166_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨871964347⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd14
  have rd16 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_177_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨910484757⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd15
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd16⟩

/-- Dispatcher path to `skimRecipient()` (arm entry pc 9649). -/
theorem metaMorphoV1_1ReachSkimRecipientBody {σ σ₀ A I} {g : Sat256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 15)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 9649)
      [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨948630965⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x38 0x8a 0xf5 0xb5 ⟨948630965⟩ (by native_decide)
      (by simpa [metaMorphoV1_1SelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken (immWords := wordsOf (immStore v)) (by simp) (by first | exact lt_four_eq_zero_of_ge hsz hsize | exact lt_four_ne_zero_of_lt hshort | exact isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort) | (rw [lt_four_eq_zero_of_ge hsz hsize]; decide) | (rw [isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)]; decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨31576340⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd1
  have rd3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_34_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨117300739⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd2
  have rd4 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_45_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨128110906⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd3
  have rd5 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_56_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨157198259⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd4
  have rd6 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_67_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨170435703⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd5
  have rd7 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_78_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨271547244⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd6
  have rd8 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_89_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨404098525⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd7
  have rd9 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_100_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨516728700⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd8
  have rd10 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_111_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨566971156⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd9
  have rd11 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_122_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨599290589⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd10
  have rd12 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_133_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨718034681⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd11
  have rd13 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_144_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨724605307⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd12
  have rd14 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_155_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨826074471⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd13
  have rd15 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_166_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨871964347⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd14
  have rd16 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_177_fallthrough (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨910484757⟩ (solcSelectorWord I)) = ⟨0⟩ by rw [hword]; native_decide)) rd15
  have rd17 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_188_taken (immWords := wordsOf (immStore v)) (by simp [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack]) (by simpa [solcSelectorWord] using (show (UInt256.eq ⟨948630965⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by rw [hword]; native_decide)) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd16
  exact ⟨_, _, by simpa [metaMorphoV1_1Blocks.metaMorphoV1_1_block_0_taken_memory, metaMorphoV1_1Blocks.metaMorphoV1_1_block_17_fallthrough_stack, deployedRuntime] using rd17⟩

end Benchmarks.Morpho.MetaMorphoV1_1
