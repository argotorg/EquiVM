import Benchmarks.Dss.Cat.BiteBodyReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — the `p`-parametric `kick` trace reach (pc 2383 → RETURN)

The frozen kick trace (`catBiteTraceSeg8aCalldata`/`Seg8b1`/`Seg8b2`, and the wrappers
`catBiteReach2383to2532`/`catBiteReach2532toRet`) all bake `@0x40 = 128`, which is UNSATISFIABLE in
the real chained `bite` flow: the milk-struct build advances the free pointer to `q + 96 = 320`.
This file re-does the whole kick tail at the abstract free pointer `p` (the real one), cloning the
frozen RD steps but mapping every memory OFFSET `128 → p`, `132 → p+4`, `164 → p+36`, `196 → p+68`,
`228 → p+100`, `260 → p+132`, `292 → p+164` (and the event offsets `128 → p`, `160 → p+32`, …),
while LENGTHS (argsLen 164, retLen 32, word 32, log 160, selector 4) stay fixed.  The calldata memory
is the foundation def `kickCalldataMemP p …` (from `BiteBodyReach`). -/

/-! ## `2383 → 2516` — the `kick` calldata build at the free pointer `p` -/

set_option maxHeartbeats 40000000 in
/-- `p`-relative clone of `catBiteTraceSeg8aCalldata`: builds the `milkFlip.kick(urn,vow,tab,dink,0)`
calldata at the abstract free pointer `p` (`@0x40 = p`), leaving the CALL frame on the stack (inOff
`p`, argsLen `164`, retOff `p`, retLen `32`, end pointer `p+164`) and the calldata memory
`kickCalldataMemP p (urn&mask) (vow&mask) tab dink mem`. -/
theorem catBiteKickCalldataP {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {tab dink dart q art ink iDust iSpot iRate urn ilk milkFlip p : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cAx, σx) k C)
    (hFlip : (if q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32))) = milkFlip)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = p)
    (hawq : q.toNat + 32 ≤ aw.toNat * 32)
    (hp96 : 96 ≤ p.toNat)
    (haw : p.toNat + 164 ≤ aw.toNat * 32)
    (hpmem : p.toNat + 164 ≤ mem.size)
    (hpsz : p.toNat + 164 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (UInt256.land biteAddrMaskWord milkFlip :: UInt256.land biteAddrMaskWord milkFlip ::
        ⟨0⟩ :: p :: ⟨164⟩ :: p :: ⟨32⟩ ::
        (p + ⟨164⟩) :: ⟨891151872⟩ :: UInt256.land biteAddrMaskWord milkFlip ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
      aw o (cAx, σx) k' C' := by
  -- offset `toNat` facts
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  -- offset arithmetic rewrites (`⟨4⟩+p = p+⟨4⟩`, `⟨32⟩+(p+⟨j⟩) = p+⟨j+32⟩`, `SUB (p+⟨164⟩) p = 164`)
  have a4 : (⟨4⟩ : UInt256) + p = p + ⟨4⟩ := u256_add_comm ⟨4⟩ p
  have a36 : (⟨32⟩ : UInt256) + (p + ⟨4⟩) = p + ⟨36⟩ := by
    rw [← u256_add_assoc, u256_add_comm ⟨32⟩ p, u256_add_assoc,
      show (⟨32⟩ : UInt256) + ⟨4⟩ = ⟨36⟩ from by native_decide]
  have a68 : (⟨32⟩ : UInt256) + (p + ⟨36⟩) = p + ⟨68⟩ := by
    rw [← u256_add_assoc, u256_add_comm ⟨32⟩ p, u256_add_assoc,
      show (⟨32⟩ : UInt256) + ⟨36⟩ = ⟨68⟩ from by native_decide]
  have a100 : (⟨32⟩ : UInt256) + (p + ⟨68⟩) = p + ⟨100⟩ := by
    rw [← u256_add_assoc, u256_add_comm ⟨32⟩ p, u256_add_assoc,
      show (⟨32⟩ : UInt256) + ⟨68⟩ = ⟨100⟩ from by native_decide]
  have a132 : (⟨32⟩ : UInt256) + (p + ⟨100⟩) = p + ⟨132⟩ := by
    rw [← u256_add_assoc, u256_add_comm ⟨32⟩ p, u256_add_assoc,
      show (⟨32⟩ : UInt256) + ⟨100⟩ = ⟨132⟩ from by native_decide]
  have a164 : (⟨32⟩ : UInt256) + (p + ⟨132⟩) = p + ⟨164⟩ := by
    rw [← u256_add_assoc, u256_add_comm ⟨32⟩ p, u256_add_assoc,
      show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ from by native_decide]
  have sub164 : UInt256.sub (p + ⟨164⟩) p = ⟨164⟩ := by
    apply u256_inj
    rw [usub_toNat (by rw [e164]; omega), e164, show (⟨164⟩ : UInt256).toNat = 164 from by decide]
    omega
  -- aw invariance witnesses at every kick-region offset
  have hMq : UInt256.ofNat (MachineState.M aw.toNat q.toNat 32) = aw := awInv32 aw hawq
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := awInv32 aw (by omega)
  have hMp : UInt256.ofNat (MachineState.M aw.toNat p.toNat 32) = aw := awInv32 aw (by omega)
  have hMp4 : UInt256.ofNat (MachineState.M aw.toNat (p + ⟨4⟩).toNat 32) = aw :=
    awInv32 aw (by rw [e4]; omega)
  have hMp36 : UInt256.ofNat (MachineState.M aw.toNat (p + ⟨36⟩).toNat 32) = aw :=
    awInv32 aw (by rw [e36]; omega)
  have hMp68 : UInt256.ofNat (MachineState.M aw.toNat (p + ⟨68⟩).toNat 32) = aw :=
    awInv32 aw (by rw [e68]; omega)
  have hMp100 : UInt256.ofNat (MachineState.M aw.toNat (p + ⟨100⟩).toNat 32) = aw :=
    awInv32 aw (by rw [e100]; omega)
  have hMp132 : UInt256.ofNat (MachineState.M aw.toNat (p + ⟨132⟩).toNat 32) = aw :=
    awInv32 aw (by rw [e132]; omega)
  -- `p ≠ 0` (from `96 ≤ p`) → the MLOAD@64 guard is false
  have hpne : p ≠ ⟨0⟩ := fun h => absurd (h ▸ hp96) (by decide)
  have hcond : ¬((⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) := by
    intro h; rw [if_pos h] at hFree; exact hpne hFree.symm
  have hsel : UInt256.land ⟨4294967295⟩ ⟨891151872⟩ = ⟨891151872⟩ := by native_decide
  -- 2383 DUP4 (q), PUSH1 0, ADD, MLOAD (flip@q)
  have rd2384 := rd.dup4 (by native_decide) (by evm_ov)
  have rd2386 := rd2384.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2387 := rd2386.add (by native_decide) (by evm_ov)
  rw [u256_zero_add q] at rd2387
  have rd2388 := RD.mload 0 milkFlip aw rd2387 (by native_decide) (mloadCost0 hMq) hFlip hMq (by evm_ov)
  -- 2388..2396 mask flip -> target
  have rd2390 := rd2388.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2392 := rd2390.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2394 := rd2392.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2395 := rd2394.shl (by native_decide) (by evm_ov)
  have rd2396 := rd2395.sub (by native_decide) (by evm_ov)
  have rd2397 := rd2396.and (by native_decide) (by evm_ov)
  -- 2397 PUSH4 sel, 2402 DUP13 (urn), 2403 PUSH1 4, 2405 PUSH1 0, 2407 SWAP1, 2408 SLOAD
  have rd2402 := rd2397.push4 ⟨891151872⟩ (by native_decide) (by evm_ov)
  have rd2403 := rd2402.dup13 (by native_decide) (by evm_ov)
  have rd2405 := rd2403.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2407 := rd2405.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2408 := rd2407.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2409⟩ := rd2408.sload (by native_decide) (by evm_ov)
  -- 2409 SWAP1, 2410 PUSH2 256, 2413 EXP, 2414 SWAP1, 2415 DIV
  have rd2410 := rd2409.swap1 (by native_decide) (by evm_ov)
  have rd2413 := rd2410.push2 ⟨256⟩ (by native_decide) (by evm_ov)
  have rd2414 := rd2413.exp (by native_decide) (by evm_ov)
  have rd2415 := rd2414.swap1 (by native_decide) (by evm_ov)
  have rd2416 := rd2415.div (by native_decide) (by evm_ov)
  -- 2416..2424 mask vow (first mask)
  have rd2418 := rd2416.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2420 := rd2418.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2422 := rd2420.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2423 := rd2422.shl (by native_decide) (by evm_ov)
  have rd2424 := rd2423.sub (by native_decide) (by evm_ov)
  have rd2425 := rd2424.and (by native_decide) (by evm_ov)
  -- 2425 DUP5 (tab), 2426 DUP7 (dink), 2427 PUSH1 0, 2429 PUSH1 64, 2431 MLOAD (freeptr=p)
  have rd2426 := rd2425.dup5 (by native_decide) (by evm_ov)
  have rd2427 := rd2426.dup7 (by native_decide) (by evm_ov)
  have rd2429 := rd2427.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2431 := rd2429.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2432 := RD.mload 0 p aw rd2431 (by native_decide) (mloadCost0 hM64) hFree hM64 (by evm_ov)
  -- 2432 DUP7 (sel), 2433 PUSH4 ffffffff, 2438 AND, 2439 PUSH1 224, 2441 SHL, 2442 DUP2, 2443 MSTORE (sel@p)
  have rd2433 := rd2432.dup7 (by native_decide) (by evm_ov)
  have rd2438 := rd2433.push4 ⟨4294967295⟩ (by native_decide) (by evm_ov)
  have rd2439 := rd2438.and (by native_decide) (by evm_ov)
  rw [hsel] at rd2439
  have rd2441 := rd2439.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd2442 := rd2441.shl (by native_decide) (by evm_ov)
  have rd2443 := rd2442.dup2 (by native_decide) (by evm_ov)
  have rd2444 := RD.mstore 0 (kickSelectorMemP p mem) aw rd2443 (by native_decide) (mstoreCost0 hMp)
    (by rfl) hMp (by evm_ov)
  -- 2444 PUSH1 4, 2446 ADD (->p+4), 2447 DUP1, 2448 DUP7 (urn), mask, 2458 DUP2, 2459 MSTORE (urn@p+4)
  have rd2446 := rd2444.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2447 := rd2446.add (by native_decide) (by evm_ov)
  rw [a4] at rd2447
  have rd2448 := rd2447.dup1 (by native_decide) (by evm_ov)
  have rd2449 := rd2448.dup7 (by native_decide) (by evm_ov)
  have rd2451 := rd2449.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2453 := rd2451.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2455 := rd2453.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2456 := rd2455.shl (by native_decide) (by evm_ov)
  have rd2457 := rd2456.sub (by native_decide) (by evm_ov)
  have rd2458 := rd2457.and (by native_decide) (by evm_ov)
  have rd2459 := rd2458.dup2 (by native_decide) (by evm_ov)
  have rd2460 := RD.mstore 0 ((UInt256.land biteAddrMaskWord urn).toByteArray.write 0
      (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32) aw rd2459 (by native_decide) (mstoreCost0 hMp4)
    (by rfl) hMp4 (by evm_ov)
  -- 2460 PUSH1 32, 2462 ADD (->p+36), 2463 DUP6 (vow1), mask again, 2473 DUP2, 2474 MSTORE (vow@p+36)
  have rd2462 := rd2460.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2463 := rd2462.add (by native_decide) (by evm_ov)
  rw [a36] at rd2463
  have rd2464 := rd2463.dup6 (by native_decide) (by evm_ov)
  have rd2466 := rd2464.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2468 := rd2466.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2470 := rd2468.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2471 := rd2470.shl (by native_decide) (by evm_ov)
  have rd2472 := rd2471.sub (by native_decide) (by evm_ov)
  have rd2473 := rd2472.and (by native_decide) (by evm_ov)
  have rd2474 := rd2473.dup2 (by native_decide) (by evm_ov)
  have rd2475 := RD.mstore 0 ((UInt256.land biteAddrMaskWord
        (UInt256.land biteAddrMaskWord (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))).toByteArray.write 0
      ((UInt256.land biteAddrMaskWord urn).toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32)
        (p + ⟨36⟩).toNat 32)
      aw rd2474 (by native_decide) (mstoreCost0 hMp36) (by rfl) hMp36 (by evm_ov)
  -- 2475 PUSH1 32, 2477 ADD (->p+68), 2478 DUP5 (tab), 2479 DUP2, 2480 MSTORE (tab@p+68)
  have rd2477 := rd2475.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2478 := rd2477.add (by native_decide) (by evm_ov)
  rw [a68] at rd2478
  have rd2479 := rd2478.dup5 (by native_decide) (by evm_ov)
  have rd2480 := rd2479.dup2 (by native_decide) (by evm_ov)
  have rd2481 := RD.mstore 0 _ aw rd2480 (by native_decide) (mstoreCost0 hMp68) (by rfl) hMp68 (by evm_ov)
  -- 2481 PUSH1 32, 2483 ADD (->p+100), 2484 DUP4 (dink), 2485 DUP2, 2486 MSTORE (dink@p+100)
  have rd2483 := rd2481.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2484 := rd2483.add (by native_decide) (by evm_ov)
  rw [a100] at rd2484
  have rd2485 := rd2484.dup4 (by native_decide) (by evm_ov)
  have rd2486 := rd2485.dup2 (by native_decide) (by evm_ov)
  have rd2487 := RD.mstore 0 _ aw rd2486 (by native_decide) (mstoreCost0 hMp100) (by rfl) hMp100 (by evm_ov)
  -- 2487 PUSH1 32, 2489 ADD (->p+132), 2490 DUP3 (0), 2491 DUP2, 2492 MSTORE (0@p+132)
  have rd2489 := rd2487.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2490 := rd2489.add (by native_decide) (by evm_ov)
  rw [a132] at rd2490
  have rd2491 := rd2490.dup3 (by native_decide) (by evm_ov)
  have rd2492 := rd2491.dup2 (by native_decide) (by evm_ov)
  have rd2493 := RD.mstore 0 (kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
      aw rd2492 (by native_decide) (mstoreCost0 hMp132) (by rfl) hMp132 (by evm_ov)
  -- 2493 PUSH1 32, 2495 ADD (->p+164), 2496 SWAP6, 2497..2502 POP x6
  have rd2495 := rd2493.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2496 := rd2495.add (by native_decide) (by evm_ov)
  rw [a164] at rd2496
  have rd2497 := rd2496.swap6 (by native_decide) (by evm_ov)
  have rd2498 := rd2497.pop (by native_decide) (by evm_ov)
  have rd2499 := rd2498.pop (by native_decide) (by evm_ov)
  have rd2500 := rd2499.pop (by native_decide) (by evm_ov)
  have rd2501 := rd2500.pop (by native_decide) (by evm_ov)
  have rd2502 := rd2501.pop (by native_decide) (by evm_ov)
  have rd2503 := rd2502.pop (by native_decide) (by evm_ov)
  -- 2503 PUSH1 32, 2505 PUSH1 64, 2507 MLOAD (freeptr=p), 2508 DUP1, 2509 DUP4, 2510 SUB (->164)
  have rd2505 := rd2503.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2507 := rd2505.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have hcalldataSize : (kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
      (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
        (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).size = mem.size :=
    kickCalldataMemP_size p _ _ tab dink hp96 hpmem hpsz
  have hval2 : (if (⟨64⟩ : UInt256).toNat ≥ (kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
          (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
            (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).readWithPadding 64 32)))
        = p := by
    rw [hcalldataSize, if_neg hcond,
      kickCalldataMemP_read64 p _ _ tab dink hp96 hpmem hpsz hread64,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  have rd2508 := RD.mload 0 p aw rd2507 (by native_decide) (mloadCost0 hM64) hval2 hM64 (by evm_ov)
  have rd2509 := rd2508.dup1 (by native_decide) (by evm_ov)
  have rd2510 := rd2509.dup4 (by native_decide) (by evm_ov)
  have rd2511 := rd2510.sub (by native_decide) (by evm_ov)
  rw [sub164] at rd2511
  -- 2511 DUP2, 2512 PUSH1 0, 2514 DUP8, 2515 DUP1 -> reach 2516
  have rd2512 := rd2511.dup2 (by native_decide) (by evm_ov)
  have rd2514 := rd2512.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2515 := rd2514.dup8 (by native_decide) (by evm_ov)
  have rd2516 := rd2515.dup1 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2516⟩

/-! ## `2516 → 2532` — EXTCODESIZE guard + `kick` CALL (retOff `p`, retLen `32`) + coupling -/

/-- **Coupling** (`p`-relative clone of `kickEncode_eq`): the bytecode-constructed `kick` calldata
slice at the free pointer `p` equals the spec-level ABI encoding of `kick(urn, vow, tab, dink, 0)`. -/
theorem kickEncodeP_eq (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size)
    (hurn : urn.toNat < EVM.addressModulus) (hvow : vow.toNat < EVM.addressModulus) :
    config.externalABI.encode? "kick"
        [.address (AccountAddress.ofNat urn.toNat), .address (AccountAddress.ofNat vow.toNat),
          .int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .int 0] =
      some ((kickCalldataMemP p urn vow tab dink mem).readWithPadding p.toNat 164) := by
  rw [kickCalldataMemP_read128_164 p urn vow tab dink hp96 hpmem hpsz]
  have hurnWord : EVM.word ↑(AccountAddress.ofNat urn.toNat) = urn := by
    have haddrVal : (AccountAddress.ofNat urn.toNat).val = urn.toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using hurn)
    change UInt256.ofNat (AccountAddress.ofNat urn.toNat).val = urn
    rw [haddrVal]; exact u256_ofNat_toNat _
  have hvowWord : EVM.word ↑(AccountAddress.ofNat vow.toNat) = vow := by
    have haddrVal : (AccountAddress.ofNat vow.toNat).val = vow.toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using hvow)
    change UInt256.ofNat (AccountAddress.ofNat vow.toNat).val = vow
    rw [haddrVal]; exact u256_ofNat_toNat _
  have htabWord : EVM.word tab.toNat = tab := by
    show UInt256.ofNat tab.toNat = tab; exact u256_ofNat_toNat tab
  have hdinkWord : EVM.word dink.toNat = dink := by
    show UInt256.ofNat dink.toNat = dink; exact u256_ofNat_toNat dink
  have hsizeEq : EVM.twoPow 256 = UInt256.size := by native_decide
  have hzeroLt : 0 < EVM.twoPow 256 := by native_decide
  have htabLt : tab.toNat < EVM.twoPow 256 := by rw [hsizeEq]; exact tab.val.isLt
  have hdinkLt : dink.toNat < EVM.twoPow 256 := by rw [hsizeEq]; exact dink.val.isLt
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    kickerKickSelector, selectorBytes, hurnWord, hvowWord, htabWord, hdinkWord,
    htabLt, hdinkLt, hzeroLt, word_toBytesBE_toByteArray_eq_toByteArray]
  have hw0 : EVM.word 0 = (⟨0⟩ : UInt256) := by decide
  simp [hw0, ByteArray.append_assoc]

/-- `2516 → 2532`: the EXTCODESIZE guard (`RD.uniswapExtcodesizeGuardOkGas`) + the `kick` `CALL`
(`perm := true`, value `0`, `depth < 1024`, inOff/retOff `p`, argsLen `164`, retLen `32`) + the
`Θ`→Solm coupling (`callCoincides`).  The kick `CALL` copies its 1-word return `o'` (the auction `id`)
into memory at `p`, so the post-call memory is `o'.write 0 mem' p (min 32 o'.size)`.  Generic in the
`targetWord`/`args`/`hencode` so the caller instantiates the spec-side values. -/
theorem catBiteKickGuardCallP {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {target p : UInt256} {args : List Value} {R : List UInt256}
    {mem' o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (target :: target :: ⟨0⟩ :: p :: ⟨164⟩ :: p :: ⟨32⟩ :: R)
      mem' aw o (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σx target ≠ ⟨0⟩)
    (hencode : config.externalABI.encode? "kick" args = some (mem'.readWithPadding p.toNat 164))
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (o'.write 0 mem' p.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        aw' o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 target) "kick" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2531⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2516⟩) (okPc := ⟨2528⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd2532raw, hosz⟩ :=
    RD.call rd2531 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hpc : ((⟨2528⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2532⟩ : UInt256) := by native_decide
  rw [hpc] at rd2532raw
  refine ⟨cA', σ', z, o', A', _, k', C', rd2532raw, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm) (targetWord := target)
    (mem := mem') (inOff := p) (inSize := ⟨164⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-! ## `2532 → 2631` — success guard + `id` extract + `dtab = dart*rate` checkedMul (`Seg8b1` at `p`) -/

set_option maxHeartbeats 40000000 in
/-- `p`-relative clone of `catBiteTraceSeg8b1`: the success guard (`RD.catBiteKickCallSucceeded`), the
free-ptr reload (`@64 = p`), the returned `id` read (`@p`), and the `dtab = dart*rate` checkedMul,
reaching pc 2631 with the event topic pushed. -/
theorem catBiteKickSeg8b1P {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status endptr target tab dink dart q art ink iDust iSpot iRate id ret urn ilk p : UInt256}
    {R3 : List UInt256} {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (status :: endptr :: ⟨891151872⟩ :: target ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk ::
        ⟨419⟩ :: ret :: R3) mem8 aw8 o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoszLt : o.size < UInt256.size)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = p)
    (hId8 : (if p.toNat ≥ mem8.size ∨ p ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding p.toNat 32))) = id)
    (hp96 : 96 ≤ p.toNat)
    (haw8 : p.toNat + 160 ≤ aw8.toNat * 32)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hov : R3.length + 40 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2631⟩
      (UInt256.mul dart iRate :: dart :: dink ::
        ⟨75576624561978822343662660390461596253028794313781746339941468162579799588392⟩ ::
        ilk :: UInt256.land urn biteAddrMaskWord ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: id :: urn :: ilk ::
        ⟨419⟩ :: ret :: R3) mem8 aw8 o acc k' C' := by
  have hM64 : UInt256.ofNat (MachineState.M aw8.toNat 64 32) = aw8 := awInv32 aw8 (by omega)
  have hMp : UInt256.ofNat (MachineState.M aw8.toNat p.toNat 32) = aw8 := awInv32 aw8 (by omega)
  obtain ⟨_, _, rd2550⟩ := RD.catBiteKickCallSucceeded rd hstatus (by simp only [List.length_cons]; omega)
  have rd2551 := rd2550.pop (by native_decide) (by evm_ov)
  have rd2552 := rd2551.pop (by native_decide) (by evm_ov)
  have rd2553 := rd2552.pop (by native_decide) (by evm_ov)
  have rd2555 := rd2553.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2556 := RD.mload 0 p aw8 rd2555 (by native_decide) (mloadCost0 hM64) hFree8 hM64 (by evm_ov)
  have rd2557 := rd2556.returndatasize (by native_decide) (by evm_ov)
  have rd2559 := rd2557.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2560 := rd2559.dup2 (by native_decide) (by evm_ov)
  have rd2561 := rd2560.lt (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (UInt256.ofNat o.size) ⟨32⟩ = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hoszLt]
    exact ho32
  rw [hlt] at rd2561
  have rd2562 := rd2561.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2562
  have rd2565 := rd2562.push2 ⟨2570⟩ (by native_decide) (by evm_ov)
  have rd2570 := rd2565.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2571 := rd2570.jumpdest (by native_decide) (by evm_ov)
  have rd2572 := rd2571.pop (by native_decide) (by evm_ov)
  have rd2573 := RD.mload 0 id aw8 rd2572 (by native_decide) (mloadCost0 hMp) hId8 hMp (by evm_ov)
  have rd2574 := rd2573.swap10 (by native_decide) (by evm_ov)
  have rd2575 := rd2574.pop (by native_decide) (by evm_ov)
  have rd2576 := rd2575.pop (by native_decide) (by evm_ov)
  have rd2578 := rd2576.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2580 := rd2578.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2582 := rd2580.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2583 := rd2582.shl (by native_decide) (by evm_ov)
  have rd2584 := rd2583.sub (by native_decide) (by evm_ov)
  have rd2585 := rd2584.dup11 (by native_decide) (by evm_ov)
  have rd2586 := rd2585.and (by native_decide) (by evm_ov)
  have rd2587 := RD.dup12 rd2586 (by native_decide) (by evm_ov)
  have rd2620 := rd2587.pushConst ⟨75576624561978822343662660390461596253028794313781746339941468162579799588392⟩ (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd2621 := rd2620.dup4 (by native_decide) (by evm_ov)
  have rd2622 := rd2621.dup6 (by native_decide) (by evm_ov)
  have rd2625 := rd2622.push2 ⟨2631⟩ (by native_decide) (by evm_ov)
  have rd2626 := rd2625.dup2 (by native_decide) (by evm_ov)
  have rd2627 := rd2626.dup15 (by native_decide) (by evm_ov)
  have rd2630 := rd2627.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720 := rd2630.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2631⟩ := RD.catBiteCheckedMul rd3720 hRateFit (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2631⟩

/-! ## `2631 → RETURN` — event `LOG3` + `@419` uint256 return encoder (`Seg8b2` at `p`)

The event data is built at `[p, p+160)` (`dink@p, dart@p+32, dtab@p+64, flip@p+96, id@p+128`), then
`LOG3 Bite()` logs it, and the `@419` encoder writes `id@p` and returns `[p, p+32)`.  These two
helpers are the `p`-relative analogues of `seg8_evMemSize`/`seg8_evMemRead64` (which bake `128`),
built on the offset-generic `seg8_wsize`/`seg8_wread64`. -/

/-- `p`-relative clone of `seg8_evMemSize`: the 5-word event build (`[p, p+160)`) preserves size. -/
theorem seg8_evMemSizeP (base : ByteArray) (p v1 v2 v3 v4 v5 : UInt256)
    (_hp96 : 96 ≤ p.toNat) (hbase : p.toNat + 160 ≤ base.size) (hpsz : p.toNat + 160 < UInt256.size) :
    ((UInt256.toByteArray v5).write 0 ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p + ⟨32⟩).toNat 32) (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32).size
      = base.size := by
  have f32 : (p + ⟨32⟩).toNat = p.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f64 : (p + ⟨64⟩).toNat = p.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f96 : (p + ⟨96⟩).toNat = p.toNat + 96 := by
    rw [uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f128 : (p + ⟨128⟩).toNat = p.toNat + 128 := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide, Nat.mod_eq_of_lt (by omega)]
  rw [f32, f64, f96, f128]
  have s1 := seg8_wsize base v1 p.toNat (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
      (p.toNat + 32) 32).size = base.size := by rw [seg8_wsize _ v2 (p.toNat + 32) (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0
      ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) 32).size
        = base.size := by rw [seg8_wsize _ v3 (p.toNat + 64) (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32)
        (p.toNat + 64) 32) (p.toNat + 96) 32).size = base.size := by
    rw [seg8_wsize _ v4 (p.toNat + 96) (by rw [s3]; omega)]; exact s3
  rw [seg8_wsize _ v5 (p.toNat + 128) (by rw [s4]; omega)]; exact s4

/-- `p`-relative clone of `seg8_evMemRead64`: the event build (`[p, p+160)`, `96 ≤ p`) leaves `@64`. -/
theorem seg8_evMemRead64P (base : ByteArray) (p v1 v2 v3 v4 v5 : UInt256)
    (hp96 : 96 ≤ p.toNat) (hbase : p.toNat + 160 ≤ base.size) (hpsz : p.toNat + 160 < UInt256.size) :
    ((UInt256.toByteArray v5).write 0 ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p + ⟨32⟩).toNat 32) (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32).readWithPadding 64 32
      = base.readWithPadding 64 32 := by
  have f32 : (p + ⟨32⟩).toNat = p.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f64 : (p + ⟨64⟩).toNat = p.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f96 : (p + ⟨96⟩).toNat = p.toNat + 96 := by
    rw [uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f128 : (p + ⟨128⟩).toNat = p.toNat + 128 := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide, Nat.mod_eq_of_lt (by omega)]
  rw [f32, f64, f96, f128]
  have s1 := seg8_wsize base v1 p.toNat (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
      (p.toNat + 32) 32).size = base.size := by rw [seg8_wsize _ v2 (p.toNat + 32) (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0
      ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) 32).size
        = base.size := by rw [seg8_wsize _ v3 (p.toNat + 64) (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32)
        (p.toNat + 64) 32) (p.toNat + 96) 32).size = base.size := by
    rw [seg8_wsize _ v4 (p.toNat + 96) (by rw [s3]; omega)]; exact s3
  rw [seg8_wread64 _ v5 (p.toNat + 128) (by omega) (by rw [s4]; omega),
    seg8_wread64 _ v4 (p.toNat + 96) (by omega) (by rw [s3]; omega),
    seg8_wread64 _ v3 (p.toNat + 64) (by omega) (by rw [s2]; omega),
    seg8_wread64 _ v2 (p.toNat + 32) (by omega) (by rw [s1]; omega),
    seg8_wread64 _ v1 p.toNat (by omega) (by omega)]

set_option maxHeartbeats 40000000 in
/-- `p`-relative clone of `catBiteTraceSeg8b2`: builds the `Bite()` event data at `[p, p+160)`,
`LOG3`s it, then the `@419` uint256 return encoder (`id@p`, `RETURN [p, p+32)`) → `RDret (toByteArray id)`. -/
theorem catBiteKickSeg8b2P {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {dart dink q art ink iDust iSpot iRate id ret urn ilk flip2 p : UInt256}
    {R3 : List UInt256} {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2631⟩
      (UInt256.mul dart iRate :: dart :: dink ::
        ⟨75576624561978822343662660390461596253028794313781746339941468162579799588392⟩ ::
        ilk :: UInt256.land urn biteAddrMaskWord ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: id :: urn :: ilk ::
        ⟨419⟩ :: ret :: R3) mem8 aw8 o acc k C)
    (hperm : I.perm = true)
    (hp96 : 96 ≤ p.toNat)
    (hmem8size : p.toNat + 160 ≤ mem8.size)
    (hpsz : p.toNat + 160 < UInt256.size)
    (haw8q : q.toNat + 32 ≤ aw8.toNat * 32)
    (haw8 : p.toNat + 160 ≤ aw8.toNat * 32)
    (hFlipEv : (if q.toNat ≥ mem8.size ∨ q ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding q.toNat 32))) = flip2)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = p)
    (hov : R3.length + 30 ≤ 1024) :
    RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id) := by
  have f32 : (p + ⟨32⟩).toNat = p.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f64 : (p + ⟨64⟩).toNat = p.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f96 : (p + ⟨96⟩).toNat = p.toNat + 96 := by
    rw [uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f128 : (p + ⟨128⟩).toNat = p.toNat + 128 := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide, Nat.mod_eq_of_lt (by omega)]
  have comm64 : (⟨64⟩ : UInt256) + p = p + ⟨64⟩ := u256_add_comm ⟨64⟩ p
  have hMq : UInt256.ofNat (MachineState.M aw8.toNat q.toNat 32) = aw8 := awInv32 aw8 haw8q
  have hM64 : UInt256.ofNat (MachineState.M aw8.toNat 64 32) = aw8 := awInv32 aw8 (by omega)
  have hMp : UInt256.ofNat (MachineState.M aw8.toNat p.toNat 32) = aw8 := awInv32 aw8 (by omega)
  have hMp32 : UInt256.ofNat (MachineState.M aw8.toNat (p + ⟨32⟩).toNat 32) = aw8 :=
    awInv32 aw8 (by rw [f32]; omega)
  have hMp64 : UInt256.ofNat (MachineState.M aw8.toNat (p + ⟨64⟩).toNat 32) = aw8 :=
    awInv32 aw8 (by rw [f64]; omega)
  have hMp96 : UInt256.ofNat (MachineState.M aw8.toNat (p + ⟨96⟩).toNat 32) = aw8 :=
    awInv32 aw8 (by rw [f96]; omega)
  have hMp128 : UInt256.ofNat (MachineState.M aw8.toNat (p + ⟨128⟩).toNat 32) = aw8 :=
    awInv32 aw8 (by rw [f128]; omega)
  have hMlog : UInt256.ofNat (MachineState.M aw8.toNat p.toNat 160) = aw8 := awInv160 aw8 (by omega)
  have hpne : p ≠ ⟨0⟩ := fun h => absurd (h ▸ hp96) (by decide)
  have hcond : ¬((⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩) := by
    intro h; rw [if_pos h] at hFree8; exact hpne hFree8.symm
  -- 2631 JUMPDEST, event data build: dink@p, dart@p+32, dtab@p+64, flip@p+96, id@p+128
  have rdJD := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2632 := rdJD.dup9 (by native_decide) (by evm_ov)
  have rd2633 := RD.mload 0 flip2 aw8 rd2632 (by native_decide) (mloadCost0 hMq) hFlipEv hMq (by evm_ov)
  have rd2634 := rd2633.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2636 := rd2634.dup1 (by native_decide) (by evm_ov)
  have rd2637 := RD.mload 0 p aw8 rd2636 (by native_decide) (mloadCost0 hM64) hFree8 hM64 (by evm_ov)
  have rd2638 := rd2637.swap5 (by native_decide) (by evm_ov)
  have rd2639 := rd2638.dup6 (by native_decide) (by evm_ov)
  have rd2640 := RD.mstore 0 _ aw8 rd2639 (by native_decide) (mstoreCost0 hMp) (by rfl) hMp (by evm_ov)
  have rd2641 := rd2640.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2643 := rd2641.dup6 (by native_decide) (by evm_ov)
  have rd2644 := rd2643.add (by native_decide) (by evm_ov)
  have rd2645 := rd2644.swap4 (by native_decide) (by evm_ov)
  have rd2646 := rd2645.swap1 (by native_decide) (by evm_ov)
  have rd2647 := rd2646.swap4 (by native_decide) (by evm_ov)
  have rd2648 := RD.mstore 0 _ aw8 rd2647 (by native_decide) (mstoreCost0 hMp32) (by rfl) hMp32 (by evm_ov)
  have rd2649 := rd2648.dup4 (by native_decide) (by evm_ov)
  have rd2650 := rd2649.dup4 (by native_decide) (by evm_ov)
  have rd2651 := rd2650.add (by native_decide) (by evm_ov)
  rw [comm64] at rd2651
  have rd2652 := rd2651.swap2 (by native_decide) (by evm_ov)
  have rd2653 := rd2652.swap1 (by native_decide) (by evm_ov)
  have rd2654 := rd2653.swap2 (by native_decide) (by evm_ov)
  have rd2655 := RD.mstore 0 _ aw8 rd2654 (by native_decide) (mstoreCost0 hMp64) (by rfl) hMp64 (by evm_ov)
  have rd2656 := rd2655.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2658 := rd2656.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2660 := rd2658.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2662 := rd2660.shl (by native_decide) (by evm_ov)
  have rd2663 := rd2662.sub (by native_decide) (by evm_ov)
  have rd2664 := rd2663.and (by native_decide) (by evm_ov)
  have rd2665 := rd2664.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd2667 := rd2665.dup4 (by native_decide) (by evm_ov)
  have rd2668 := rd2667.add (by native_decide) (by evm_ov)
  have rd2669 := RD.mstore 0 _ aw8 rd2668 (by native_decide) (mstoreCost0 hMp96) (by rfl) hMp96 (by evm_ov)
  have rd2670 := rd2669.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd2672 := rd2670.dup3 (by native_decide) (by evm_ov)
  have rd2673 := rd2672.add (by native_decide) (by evm_ov)
  have rd2674 := rd2673.dup15 (by native_decide) (by evm_ov)
  have rd2675 := rd2674.swap1 (by native_decide) (by evm_ov)
  have rd2676 := RD.mstore 0 _ aw8 rd2675 (by native_decide) (mstoreCost0 hMp128) (by rfl) hMp128 (by evm_ov)
  -- event-memory read-below/size + free-ptr reload (`@64 = p`), then LOG3
  have hevRead := seg8_evMemRead64P mem8 p dink dart (UInt256.mul dart iRate)
    (UInt256.land biteAddrMaskWord flip2) id hp96 hmem8size hpsz
  have hevSize := seg8_evMemSizeP mem8 p dink dart (UInt256.mul dart iRate)
    (UInt256.land biteAddrMaskWord flip2) id hp96 hmem8size hpsz
  have hFreeEv : (if (⟨64⟩ : UInt256).toNat ≥ ((UInt256.toByteArray id).write 0
        ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
          ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
            ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
            (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (((UInt256.toByteArray id).write 0
        ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
          ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
            ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
            (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32).readWithPadding 64 32))) = p := by
    have h8 := hFree8; rw [if_neg hcond] at h8
    rw [hevSize, if_neg hcond, hevRead]; exact h8
  have rd2677 := RD.mload 0 p aw8 rd2676 (by native_decide) (mloadCost0 hM64) hFreeEv hM64 (by evm_ov)
  have rd2678 := rd2677.swap1 (by native_decide) (by evm_ov)
  have rd2679 := rd2678.dup2 (by native_decide) (by evm_ov)
  have rd2680 := rd2679.swap1 (by native_decide) (by evm_ov)
  have rd2681 := rd2680.sub (by native_decide) (by evm_ov)
  rw [u256_sub_self p] at rd2681
  have rd2682 := rd2681.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2684 := rd2682.add (by native_decide) (by evm_ov)
  rw [show (⟨160⟩ : UInt256) + ⟨0⟩ = ⟨160⟩ from by native_decide] at rd2684
  have rd2685 := rd2684.swap1 (by native_decide) (by evm_ov)
  have rd2686 := RD.log3 0 aw8 rd2685 (by native_decide) hperm (log3Cost0 hMlog) hMlog (by evm_ov)
  have rd2687 := rd2686.pop (by native_decide) (by evm_ov)
  have rd2688 := rd2687.pop (by native_decide) (by evm_ov)
  have rd2689 := rd2688.pop (by native_decide) (by evm_ov)
  have rd2690 := rd2689.pop (by native_decide) (by evm_ov)
  have rd2691 := rd2690.pop (by native_decide) (by evm_ov)
  have rd2692 := rd2691.pop (by native_decide) (by evm_ov)
  have rd2693 := rd2692.pop (by native_decide) (by evm_ov)
  have rd2694 := rd2693.pop (by native_decide) (by evm_ov)
  have rd2695 := rd2694.swap3 (by native_decide) (by evm_ov)
  have rd2696 := rd2695.swap2 (by native_decide) (by evm_ov)
  have rd2697 := rd2696.pop (by native_decide) (by evm_ov)
  have rd2698 := rd2697.pop (by native_decide) (by evm_ov)
  have rd419 := rd2698.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- @419 uint256 return encoder: mstore id@p ; return [p, p+32)
  have rd420 := rd419.jumpdest (by native_decide) (by evm_ov)
  have rd422 := rd420.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd423 := rd422.dup1 (by native_decide) (by evm_ov)
  have rd424 := RD.mload 0 p aw8 rd423 (by native_decide) (mloadCost0 hM64) hFreeEv hM64 (by evm_ov)
  have rd425 := rd424.swap2 (by native_decide) (by evm_ov)
  have rd426 := rd425.dup3 (by native_decide) (by evm_ov)
  have rd427 := RD.mstore 0 _ aw8 rd426 (by native_decide) (mstoreCost0 hMp) (by rfl) hMp (by evm_ov)
  -- second free-ptr read (m2[64] = p, below the id@p write)
  have hm2read : ((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0
      ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
        ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
          ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
          (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32)) p.toNat 32).readWithPadding 64 32
      = mem8.readWithPadding 64 32 := by
    rw [seg8_wread64 _ id p.toNat (by omega) (by rw [hevSize]; omega), hevRead]
  have hFreeM2 : (if (⟨64⟩ : UInt256).toNat ≥ ((UInt256.toByteArray id).write 0
        (((UInt256.toByteArray id).write 0
          ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
            ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
              ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
              (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32)) p.toNat 32).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (((UInt256.toByteArray id).write 0
        (((UInt256.toByteArray id).write 0
          ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
            ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
              ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
              (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32)) p.toNat 32).readWithPadding 64 32))) = p := by
    have h8 := hFree8; rw [if_neg hcond] at h8
    rw [seg8_wsize _ id p.toNat (by rw [hevSize]; omega), hevSize, if_neg hcond, hm2read]; exact h8
  have rd428 := RD.mload 0 p aw8 rd427 (by native_decide) (mloadCost0 hM64) hFreeM2 hM64 (by evm_ov)
  have rd429 := rd428.swap1 (by native_decide) (by evm_ov)
  have rd430 := rd429.dup2 (by native_decide) (by evm_ov)
  have rd431 := rd430.swap1 (by native_decide) (by evm_ov)
  have rd432 := rd431.sub (by native_decide) (by evm_ov)
  rw [u256_sub_self p] at rd432
  have rd434 := rd432.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd435 := rd434.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨0⟩ = ⟨32⟩ from by native_decide] at rd435
  have rd436 := rd435.swap1 (by native_decide) (by evm_ov)
  -- RETURN mem[p..p+32) = toByteArray id
  have hret : ((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0
      ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
        ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
          ((UInt256.toByteArray dink).write 0 mem8 p.toNat 32) (p + ⟨32⟩).toNat 32)
          (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32)) p.toNat 32).readWithPadding p.toNat 32
      = UInt256.toByteArray id :=
    toByteArray_write32_read_back _ id p.toNat (by rw [hevSize]; omega)
  exact RD.ret 0 (UInt256.toByteArray id) rd436 (by native_decide)
    (fun s haw hstk => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, List.getElem!_cons_zero,
        List.getElem!_cons_succ]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hMp]; simp)
    (by rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]; exact hret)
    (by evm_ov)

/-- `2532 → RETURN` at the free pointer `p` (composes `Seg8b1P` + `Seg8b2P`): the `p`-relative
replacement for `catBiteReach2532toRet` on the success path. -/
theorem catBiteKickReturnP {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status endptr target tab dink dart q art ink iDust iSpot iRate id ret urn ilk milkFlip p : UInt256}
    {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (status :: endptr :: ⟨891151872⟩ :: target ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk ::
        ⟨419⟩ :: ret :: []) mem8 aw8 o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoszLt : o.size < UInt256.size)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = p)
    (hId8 : (if p.toNat ≥ mem8.size ∨ p ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding p.toNat 32))) = id)
    (hperm : I.perm = true)
    (hp96 : 96 ≤ p.toNat)
    (hmem8size : p.toNat + 160 ≤ mem8.size)
    (hpsz : p.toNat + 160 < UInt256.size)
    (haw8q : q.toNat + 32 ≤ aw8.toNat * 32)
    (haw8 : p.toNat + 160 ≤ aw8.toNat * 32)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hFlipEv : (if q.toNat ≥ mem8.size ∨ q ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding q.toNat 32))) = milkFlip) :
    RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id) := by
  obtain ⟨_, _, rd2631⟩ :=
    catBiteKickSeg8b1P rd hstatus ho32 hoszLt hFree8 hId8 hp96 haw8 hRateFit (by simp)
  exact catBiteKickSeg8b2P rd2631 hperm hp96 hmem8size hpsz haw8q haw8 hFlipEv hFree8 (by simp)

/-- The active-words after the kick `CALL` (`aw' = M (M aw p 164) p 32`) still cover `[0, p+164)`:
memory expansion is `max`-monotone, so the argument-region growth survives. -/
theorem kickAwBound (aw p : UInt256) (hpsz : p.toNat + 164 < UInt256.size) :
    p.toNat + 164 ≤
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32)).toNat * 32 := by
  have hinnerEq : MachineState.M aw.toNat p.toNat 164 = max aw.toNat ((p.toNat + 164 + 31) / 32) := rfl
  have houterEq : MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 =
      max (MachineState.M aw.toNat p.toNat 164) ((p.toNat + 32 + 31) / 32) := rfl
  have hinner_ge : (p.toNat + 164 + 31) / 32 ≤ MachineState.M aw.toNat p.toNat 164 := by
    rw [hinnerEq]; exact le_max_right _ _
  have houter_ge : MachineState.M aw.toNat p.toNat 164 ≤
      MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 := by
    rw [houterEq]; exact le_max_left _ _
  have hlt : MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 < UInt256.size := by
    rw [houterEq, hinnerEq]
    have h1 : aw.toNat < UInt256.size := aw.val.isLt
    have h2 : (p.toNat + 164 + 31) / 32 < UInt256.size := by omega
    have h3 : (p.toNat + 32 + 31) / 32 < UInt256.size := by omega
    omega
  have hval : (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32)).toNat
      = MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 := ulit_toNat' _ hlt
  rw [hval]
  have hceil : p.toNat + 164 ≤ (p.toNat + 164 + 31) / 32 * 32 := by omega
  calc p.toNat + 164 ≤ (p.toNat + 164 + 31) / 32 * 32 := hceil
    _ ≤ MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 * 32 := by
        have := le_trans hinner_ge houter_ge; exact Nat.mul_le_mul_right 32 this

/-! ## Part A — the `p`-relative return-copy memory `if`-forms (`kick` `CALL` return copy)

The kick `CALL` copies its 1-word return `o'` (the auction `id`) into memory at OFFSET `p`
(`o'.write 0 (kickCalldataMemP …) p (min 32 |o'|)`, needing `32 ≤ |o'|` so the length is `32`).
These are the `p`-relative clones of `catBiteKickPostCallMem_size`/`_mload64`/`_mload128`. -/

/-- The `min 32 |o|` return-copy length collapses to `32` once `32 ≤ |o|`. -/
private theorem kickP_hlen (o : ByteArray) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
  umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hout

/-- `mem8.size = mem.size` (`p`-relative clone of `catBiteKickPostCallMem_size`). -/
theorem catBiteKickPostCallMemP_size (p kurn kvow tab dink : UInt256) {mem : ByteArray} (o : ByteArray)
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size)
    (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size) :
    (o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size = mem.size := by
  rw [kickP_hlen o ho32 hout,
    write32_eq o (kickCalldataMemP p kurn kvow tab dink mem) p.toNat (by omega)
      (by rw [kickCalldataMemP_size p kurn kvow tab dink hp96 hpmem hpsz]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, kickCalldataMemP_size p kurn kvow tab dink hp96 hpmem hpsz]
  omega

/-- The free pointer `p` survives at `@64` (below the return copy since `96 ≤ p`) — discharges
`catBiteKickReturnP`'s `hFree8`. -/
theorem catBiteKickPostCallMemP_mload64 (p kurn kvow tab dink : UInt256) {mem : ByteArray}
    (o : ByteArray) {aw8 : UInt256} (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size)
    (hpsz : p.toNat + 164 < UInt256.size) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (haw : p.toNat + 160 ≤ aw8.toNat * 32) (hawsz : aw8.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding 64 32))) = p :=
  mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := p)
    (by rw [catBiteKickPostCallMemP_size p kurn kvow tab dink o hp96 hpmem hpsz ho32 hout]
        show (64 : ℕ) < mem.size; omega)
    (by intro hh
        have hle : (aw8 * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz, show (⟨64⟩ : UInt256).toNat = 64 from by decide] at hle
        omega)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, kickP_hlen o ho32 hout,
          write_read_below_gen_extend o (kickCalldataMemP p kurn kvow tab dink mem) p.toNat 32 64
            (by decide) (by omega)
            (by rw [kickCalldataMemP_size p kurn kvow tab dink hp96 hpmem hpsz]; omega) (by omega)]
        exact kickCalldataMemP_read64 p kurn kvow tab dink hp96 hpmem hpsz hread64)

/-- The returned `id` (`o.extract 0 32`) sits AT `@p` (the return copy) — discharges
`catBiteKickReturnP`'s `hId8`. -/
theorem catBiteKickPostCallMemP_mloadP (p kurn kvow tab dink : UInt256) {mem : ByteArray}
    (o : ByteArray) {aw8 : UInt256} (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size)
    (hpsz : p.toNat + 164 < UInt256.size) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (haw : p.toNat + 160 ≤ aw8.toNat * 32) (hawsz : aw8.toNat * 32 < UInt256.size) :
    (if p.toNat ≥ (o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size
        ∨ p ≥ aw8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding p.toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :=
  mloadWordValue_of_readWithPadding (off := p)
    (v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
    (by rw [catBiteKickPostCallMemP_size p kurn kvow tab dink o hp96 hpmem hpsz ho32 hout]; omega)
    (by intro hh
        have hle : (aw8 * ⟨32⟩).toNat ≤ p.toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz] at hle
        omega)
    (by rw [kickP_hlen o ho32 hout,
          writeReturnCopy_read32 o (kickCalldataMemP p kurn kvow tab dink mem) p.toNat 32 p.toNat
            (by omega) (by rw [kickCalldataMemP_size p kurn kvow tab dink hp96 hpmem hpsz]; omega)
            (by omega) (by omega)]
        have hw := readWithPadding_eq_toByteArray_ofNat o 0 (by omega)
        rw [readWithPadding_eq_extract o 0 (by omega)] at hw
        simpa using hw)

/-- The milk-struct `flip` word at `@q` survives (below the return copy since `q+32 ≤ p`) —
discharges `catBiteKickReturnP`'s `hFlipEv` (takes the raw `@q` read as hypothesis). -/
theorem catBiteKickPostCallMemP_mloadFlip (p kurn kvow tab dink q milkFlip : UInt256) {mem : ByteArray}
    (o : ByteArray) {aw8 : UInt256} (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size)
    (hpsz : p.toNat + 164 < UInt256.size) (ho32 : 32 ≤ o.size) (hout : o.size < UInt256.size)
    (hqp : q.toNat + 32 ≤ p.toNat) (hawq : q.toNat + 32 ≤ aw8.toNat * 32)
    (hawsz : aw8.toNat * 32 < UInt256.size)
    (hFlipRaw : mem.readWithPadding q.toNat 32 = UInt256.toByteArray milkFlip) :
    (if q.toNat ≥ (o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).size
        ∨ q ≥ aw8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((o.write 0 (kickCalldataMemP p kurn kvow tab dink mem) p.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat).readWithPadding q.toNat 32))) = milkFlip :=
  mloadWordValue_of_readWithPadding (off := q) (v := milkFlip)
    (by rw [catBiteKickPostCallMemP_size p kurn kvow tab dink o hp96 hpmem hpsz ho32 hout]; omega)
    (by intro hh
        have hle : (aw8 * ⟨32⟩).toNat ≤ q.toNat := hh
        rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt hawsz] at hle
        omega)
    (by rw [kickP_hlen o ho32 hout,
          write_read_below_gen_extend o (kickCalldataMemP p kurn kvow tab dink mem) p.toNat 32 q.toNat
            (by decide) (by omega)
            (by rw [kickCalldataMemP_size p kurn kvow tab dink hp96 hpmem hpsz]; omega) (by omega),
          kickCalldataMemP_readBelow p kurn kvow tab dink q.toNat (by omega) hp96 hpmem hpsz]
        exact hFlipRaw)

/-! ## Part B — `2383 → 2532` + success-path `RETURN`, all at the free pointer `p`

Composes `catBiteKickCalldataP` (2383→2516), the EXTCODESIZE guard + `kick` `CALL` (2516→2532,
inlined so the post-call active-words `M (M aw p 164) p 32` stays concrete — it collapses to `aw`
by `haw`), and, on the success branch, `catBiteKickReturnP` (2532→RETURN) discharged by the Part A
memory `if`-forms.  `hawsz` (`aw*32 < size`) is the "active words do not overflow" side-condition
needed to invert the input `@q` `flip` read and the return-copy `MLOAD` guards. -/
theorem catBiteReachKickC {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {tab dink dart q art ink iDust iSpot iRate urn milkFlip p : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: []) mem aw o (cAx, σx) k C)
    (hFlip : (if q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32))) = milkFlip)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = p)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hawq : q.toNat + 32 ≤ aw.toNat * 32) (hqp : q.toNat + 32 ≤ p.toNat)
    (hp96 : 96 ≤ p.toNat) (haw : p.toNat + 164 ≤ aw.toNat * 32)
    (hawsz : aw.toNat * 32 < UInt256.size)
    (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size)
    (hperm : I.perm = true) (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σx
      (UInt256.land biteAddrMaskWord milkFlip) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (p + ⟨164⟩) :: ⟨891151872⟩ ::
          UInt256.land biteAddrMaskWord milkFlip ::
          tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (o'.write 0 (kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
          (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
            (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
          p.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        aw' o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord milkFlip)) "kick" 0
        (seg8KickArgs σx I urn tab dink)
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm
    ∧ o'.size < UInt256.size
    ∧ (z = true → 32 ≤ o'.size →
        RDret catBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA', σ')
          (UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o'.extract 0 32))))) := by
  -- 2383 → 2516: build the kick calldata at the free pointer `p`
  obtain ⟨_, _, rd2516⟩ :=
    catBiteKickCalldataP rd hFlip hFree hawq hp96 haw hpmem hpsz hread64 (by simp)
  -- the ABI-encode coupling for the kick calldata
  have henc := kickEncodeP_eq p (UInt256.land biteAddrMaskWord urn)
    (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
      (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink
    hp96 hpmem hpsz (seg8_maskBound urn) (seg8_maskBound _)
  -- 2516 → 2532: inline EXTCODESIZE guard + kick CALL (concrete post-call active-words)
  obtain ⟨gasWord, _, _, rd2531⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2516⟩) (okPc := ⟨2528⟩) rd2516 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd2532raw, hosz⟩ :=
    RD.call rd2531 (by native_decide) hdepth (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hpc : ((⟨2528⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2532⟩ : UInt256) := by native_decide
  rw [hpc] at rd2532raw
  -- the post-call active-words `M (M aw p 164) p 32` collapse to `aw` (already covers `[0, p+164)`)
  have hawEq : UInt256.ofNat (MachineState.M (MachineState.M aw.toNat p.toNat (⟨164⟩ : UInt256).toNat)
      p.toNat (⟨32⟩ : UInt256).toNat) = aw := by
    rw [show (⟨164⟩ : UInt256).toNat = 164 from by decide, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    have hinner : MachineState.M aw.toNat p.toNat 164 = aw.toNat := by
      rw [show MachineState.M aw.toNat p.toNat 164 = max aw.toNat ((p.toNat + 164 + 31) / 32) from rfl,
        max_eq_left (by omega)]
    rw [hinner]; exact awInv32 aw (by omega)
  rw [hawEq] at rd2532raw
  -- the spec-side call coincidence (Θ ↔ Solm)
  have hcall : typedCallViaEVM config
      { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σx, createdAccounts := cAx }
      (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord milkFlip)) "kick" 0
      (seg8KickArgs σx I urn tab dink)
      (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm := by
    refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := UInt256.land biteAddrMaskWord milkFlip)
      (mem := kickCalldataMemP p (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
      (inOff := p) (inSize := ⟨164⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl henc ?_
    simpa [initState] using hΘ
  refine ⟨cA', σ', z, o', A', aw, k', C', rd2532raw, hcall, hosz, ?_⟩
  -- success path: 2532 → RETURN via `catBiteKickReturnP`
  intro hz ho32
  subst hz
  have hFlipRaw : mem.readWithPadding q.toNat 32 = UInt256.toByteArray milkFlip := by
    have hcondFlip : ¬(q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩) := by
      refine not_or.mpr ⟨by omega, ?_⟩
      intro hh
      have hle : (aw * ⟨32⟩).toNat ≤ q.toNat := hh
      rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt hawsz] at hle
      omega
    have hFlipVal : UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32)) = milkFlip := by
      rw [if_neg hcondFlip] at hFlip; exact hFlip
    rw [readWithPadding_eq_toByteArray_ofNat mem q.toNat (by omega),
      ← readWithPadding_eq_extract mem q.toNat (by omega), hFlipVal]
  exact catBiteKickReturnP rd2532raw (by decide) ho32 hosz
    (catBiteKickPostCallMemP_mload64 p (UInt256.land biteAddrMaskWord urn)
      (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
        (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink o'
      hp96 hpmem hpsz ho32 hosz hread64 (by omega) hawsz)
    (catBiteKickPostCallMemP_mloadP p (UInt256.land biteAddrMaskWord urn)
      (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
        (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink o'
      hp96 hpmem hpsz ho32 hosz (by omega) hawsz)
    hperm hp96
    (by rw [catBiteKickPostCallMemP_size p (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink o'
        hp96 hpmem hpsz ho32 hosz]; omega)
    (by omega) hawq (by omega) hRateFit
    (catBiteKickPostCallMemP_mloadFlip p (UInt256.land biteAddrMaskWord urn)
      (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
        (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink q milkFlip o'
      hp96 hpmem hpsz ho32 hosz hqp hawq hawsz hFlipRaw)

end Benchmarks.Dss.Cat
