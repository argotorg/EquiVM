import Benchmarks.OpenZeppelinBench.TimelockController.ConstructorEvm
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
namespace OpenZeppelinBench.TimelockController

-- discover grant stack shapes. Entry @450: [account, role, retaddr, R...]
example {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {M : ByteArray} {aw : UInt256} {account role retaddr : UInt256} {R : List UInt256}
    (h : RD timelockControllerBenchCreationBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨450⟩
      (account :: role :: retaddr :: R) M aw ByteArray.empty (cA, σ) k C)
    (haw : 96 ≤ 32 * aw.toNat) (hMsize : 256 ≤ M.size) (hR : R.length ≤ 900)
    (hfp : M.readWithPadding 64 32 = (⟨256⟩ : UInt256).toByteArray) :
    True := by
  have e0 : (⟨0⟩ : UInt256).toNat = 0 := by native_decide
  have e32 : (⟨32⟩ : UInt256).toNat = 32 := by native_decide
  have e64 : (⟨64⟩ : UInt256).toNat = 64 := by native_decide
  -- @450 JUMPDEST ; @451 PUSH0 ; @452 DUP3 ; @453 DUP2 ; @454 MSTORE (mem[0]=role)
  have h1 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h2 := h1.mstore 0 (wordAt0Mem role M) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_mstore ha hs (by omega)) (by rfl)
    (tlcCtorEvmAwOut aw (⟨0⟩ : UInt256).toNat 32 (by omega)) (by evm_ov)
  -- @455 PUSH1 32 ; @457 DUP2 ; @458 DUP2 ; @459 MSTORE (mem[32]=0)
  have h3 := h2.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h4 := h3.mstore 0 (twoWordHashMem role ⟨0⟩ M) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_mstore ha hs (by omega)) (by rfl)
    (tlcCtorEvmAwOut aw (⟨32⟩ : UInt256).toNat 32 (by omega)) (by evm_ov)
  -- @460 PUSH1 64 ; @462 DUP1 ; @463 DUP4 ; @464 KECCAK256 -> roleDataSlot = solcMappingSlot 0 role
  have h5 := h4.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
  have h6 := h5.keccak256 0 (solcMappingSlot ⟨0⟩ role) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_keccak ha hs (by omega))
    (by rw [e0, e64]; exact tlcCtorEvmScratch_keccak role ⟨0⟩ (by omega))
    (tlcCtorEvmAwOut aw (⟨0⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat (by omega)) (by evm_ov)
  -- @465-474: mask account. maskAcc = land account solcAddrMask
  have h7 := h6.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
  -- @475 DUP5 ; @476 MSTORE (mem[0]=maskAcc)
  have h8 := h7.dup5 (by native_decide) (by evm_ov)
  have h9 := h8.mstore 0 (wordAt0Mem (UInt256.land account (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩))
      (twoWordHashMem role ⟨0⟩ M)) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_mstore ha hs (by omega)) (by rfl)
    (tlcCtorEvmAwOut aw (⟨0⟩ : UInt256).toNat 32 (by omega)) (by evm_ov)
  -- @477 SWAP1 ; @478 SWAP2 ; @479 MSTORE (mem[32]=roleDataSlot)
  have h10 := h9.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have h11 := h10.mstore 0 (twoWordHashMem (UInt256.land account (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩))
      (solcMappingSlot ⟨0⟩ role) (twoWordHashMem role ⟨0⟩ M)) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_mstore ha hs (by omega)) (by rfl)
    (tlcCtorEvmAwOut aw (⟨32⟩ : UInt256).toNat 32 (by omega)) (by evm_ov)
  -- @480 DUP2 ; @481 KECCAK256 -> finalSlot = solcMappingSlot roleDataSlot maskAcc
  have h12 := h11.dup2 (by native_decide) (by evm_ov)
  have h13 := h12.keccak256 0
      (solcMappingSlot (solcMappingSlot ⟨0⟩ role)
        (UInt256.land account (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩))) aw (by native_decide)
    (fun s ha hs => tlcCtorEvmCost0_keccak ha hs (by omega))
    (by rw [e0, e64]
        exact tlcCtorEvmScratch_keccak _ (solcMappingSlot ⟨0⟩ role)
          (by rw [tlcCtorEvmScratch_size role ⟨0⟩ (by omega)]; omega))
    (tlcCtorEvmAwOut aw (⟨0⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat (by omega)) (by evm_ov)
  -- @482 SLOAD ; @483 PUSH1 255 ; @485 AND ; @486 PUSH2 610 ; @489 JUMPI
  obtain ⟨_, _, h14⟩ := h13.sload (by native_decide) (by evm_ov)
  have h15 := h14.push1 ⟨255⟩ (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.push2 ⟨610⟩ (by native_decide) (by evm_ov)
  sorry

end OpenZeppelinBench.TimelockController
