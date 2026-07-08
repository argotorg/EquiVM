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

end Benchmarks.Dss.Cat
