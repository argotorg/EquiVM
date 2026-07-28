import Benchmarks.Dss.Cat.BiteEVM
import Benchmarks.Dss.Cat.BiteCallIlks
import Benchmarks.Dss.Cat.BiteCallUrns
import Benchmarks.Dss.Cat.BiteSource
import Reasoning.ExternalCall
import Benchmarks.Dss.Cat.BiteCallKick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite(bytes32,address)` — EVM-side trace helpers

`catReachBiteRoutine` : from the `bite` arm entry (pc `375`) through the 2-arg `(bytes32,address)`
decode preamble and the unsigned length check (`need = 64`) to the `bite` routine entry at pc `1163`,
with the decoded args on the stack:
`[land ((1<<160)-1) (calldataWord 36), calldataWord 4, ⟨419⟩, catSelWord I]`.

Disassembly of the preamble (runtime.hex):
```
375 JUMPDEST; 376 PUSH2 419; 379 PUSH1 4; 381 DUP1; 382 CALLDATASIZE; 383 SUB;
384 PUSH1 64; 386 DUP2; 387 LT; 388 ISZERO; 389 PUSH2 397; 392 JUMPI;   (len check)
393 PUSH1 0; DUP1; REVERT                                                (short revert)
397 JUMPDEST; 398 POP; 399 DUP1; 400 CALLDATALOAD;                       (ilk = cd@4)
401 SWAP1; 402 PUSH1 32; 404 ADD; 405 CALLDATALOAD;                      (urnRaw = cd@36)
406 PUSH1 1; 408 PUSH1 1; 410 PUSH1 160; 412 SHL; 413 SUB; 414 AND;      (urn = urnRaw & addrMask)
415 PUSH2 1163; 418 JUMP
```
The `375→397` half (JUMPDEST + len check, `JUMPI` taken) is packaged by
`RD.solcExternalStaticArgsLenOk`; the `397→1163` half is the explicit stack trace below.
-/

/-- The 160-bit address mask `(1 << 160) - 1` exactly as the bytecode builds it
(`PUSH1 1; PUSH1 160; SHL; SUB` over the preceding `PUSH1 1`). -/
abbrev biteAddrMaskWord : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩

theorem catReachBiteRoutine {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
        (UInt256.land biteAddrMaskWord (calldataWord I.calldata 36) ::
          calldataWord I.calldata 4 :: ⟨419⟩ :: [catSelWord I])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  -- entry at pc 375, stack [sel]
  have hentry := catReachBiteEntry (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv (by omega) hsize hsel
  -- 375 → 397 (JUMPDEST + unsigned length check `size - 4 ≥ 64`, JUMPI taken)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (head := ⟨4⟩) (need := ⟨64⟩) (by simpa using hsz68) hsize
  obtain ⟨_, _, rd397⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨375⟩) (ret := ⟨419⟩)
    (decoded := ⟨397⟩) (need := ⟨64⟩) hentry
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  -- 397 → 1163 explicit stack trace
  have rd398 := rd397.jumpdest (by native_decide) (by evm_ov)
  have rd399 := rd398.pop (by native_decide) (by evm_ov)
  have rd400 := rd399.dup1 (by native_decide) (by evm_ov)
  have rd401 := rd400.calldataload (by native_decide) (by evm_ov)
  have rd402 := rd401.swap1 (by native_decide) (by evm_ov)
  have rd404 := rd402.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd405 := rd404.add (by native_decide) (by evm_ov)
  have rd406 := rd405.calldataload (by native_decide) (by evm_ov)
  have rd408 := rd406.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd410 := rd408.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd412 := rd410.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd413 := rd412.shl (by native_decide) (by evm_ov)
  have rd414 := rd413.sub (by native_decide) (by evm_ov)
  have rd415 := rd414.and (by native_decide) (by evm_ov)
  have rd418 := rd415.push2 ⟨1163⟩ (by native_decide) (by evm_ov)
  have rd1163 := rd418.jump (by native_decide) (by jump_dest) (by evm_ov)
  have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
  have hadd36 : ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 := by native_decide
  exact ⟨_, _, by simpa only [biteAddrMaskWord, calldataWord, h4, hadd36] using rd1163⟩

/-!
## Shared arithmetic routine: solc `checked_mul_uint256` @ pc `3720`

`bite` calls this DSMath checked-multiply routine 6× (inkSpot, artRateUnsafe, dunkRoomWad, inkDart,
dartRate, tabBase). Entry (after `PUSH2 ret; PUSH b; PUSH a; PUSH2 3720; JUMP`) is stack
`[a, b, ret, R]`; on the no-overflow success path it JUMPs to `ret` with `[a*b, R]`.

Disassembly (3720–3761):
```
3720 JUMPDEST; 3721 PUSH1 0; 3723 DUP2; 3724 ISZERO; 3725 DUP1; 3726 PUSH2 3747; 3729 JUMPI  (a==0?)
3730 POP; 3731 POP; 3732 DUP1; 3733 DUP3; 3734 MUL;                                          (p = b*a)
3735 DUP3; 3736 DUP3; 3737 DUP3; 3738 DUP2; 3739 PUSH2 3744; 3742 JUMPI; 3743 INVALID;       (div guard a!=0)
3744 JUMPDEST; 3745 DIV; 3746 EQ;                                                            ((p/a)==b overflow check)
3747 JUMPDEST; 3748 PUSH2 3756; 3751 JUMPI; 3752 PUSH1 0; DUP1; REVERT;                       (revert on overflow)
3756 JUMPDEST; 3757 SWAP3; 3758 SWAP2; 3759 POP; 3760 POP; 3761 JUMP                          (return p to ret)
```
The routine computes `UInt256.mul b a` (MUL of `[b, a]`); the caller relates it to its source-order
product by commutativity of `UInt256.mul`. -/
set_option maxHeartbeats 1000000 in
theorem RD.catBiteCheckedMul {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3720⟩
      (a :: b :: ret :: R) mem aw rdata acc k C)
    (hmulfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.mul b a :: R) mem aw rdata acc k' C' := by
  by_cases ha : a = ⟨0⟩
  · -- a = 0: product short-circuits to 0
    subst ha
    have hmul0 : UInt256.mul b ⟨0⟩ = ⟨0⟩ := by
      apply u256_inj; rw [u256_mul_toNat]; simp
    have rd3721 := rd.jumpdest (by native_decide) (by evm_ov)
    have rd3723 := rd3721.push1 ⟨0⟩ (by native_decide) (by evm_ov)
    have rd3724 := rd3723.dup2 (by native_decide) (by evm_ov)
    have rd3725 := rd3724.iszero (by native_decide) (by evm_ov)
    have rd3726 := rd3725.dup1 (by native_decide) (by evm_ov)
    have rd3729 := rd3726.push2 ⟨3747⟩ (by native_decide) (by evm_ov)
    have rd3747 := rd3729.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)
    have rd3748 := rd3747.jumpdest (by native_decide) (by evm_ov)
    have rd3751 := rd3748.push2 ⟨3756⟩ (by native_decide) (by evm_ov)
    have rd3756 := rd3751.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)
    have rd3757 := rd3756.jumpdest (by native_decide) (by evm_ov)
    have rd3758 := rd3757.swap3 (by native_decide) (by evm_ov)
    have rd3759 := rd3758.swap2 (by native_decide) (by evm_ov)
    have rd3760 := rd3759.pop (by native_decide) (by evm_ov)
    have rd3761 := rd3760.pop (by native_decide) (by evm_ov)
    have rdRet := rd3761.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by rw [hmul0]; exact rdRet⟩
  · -- a ≠ 0: full mul + overflow check
    have hbafit : b.toNat * a.toNat < UInt256.size := by rw [Nat.mul_comm]; exact hmulfit
    have hapos : 0 < a.toNat := by
      rcases Nat.eq_zero_or_pos a.toNat with h | h
      · exact absurd (u256_inj (a := a) (b := ⟨0⟩) (by rw [h]; rfl)) ha
      · exact h
    have hdiv : UInt256.div (UInt256.mul b a) a = b := by
      apply u256_inj
      rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hbafit, Nat.mul_div_cancel _ hapos]
    have heq1 : UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨1⟩ := by
      rw [hdiv]; exact uInt256_eq_self b
    have hiszero0 : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne ha
    have rd3721 := rd.jumpdest (by native_decide) (by evm_ov)
    have rd3723 := rd3721.push1 ⟨0⟩ (by native_decide) (by evm_ov)
    have rd3724 := rd3723.dup2 (by native_decide) (by evm_ov)
    have rd3725 := rd3724.iszero (by native_decide) (by evm_ov)
    have rd3726 := rd3725.dup1 (by native_decide) (by evm_ov)
    have rd3729 := rd3726.push2 ⟨3747⟩ (by native_decide) (by evm_ov)
    have rd3730 := rd3729.jumpiNT (by native_decide) hiszero0 (by evm_ov)
    have rd3731 := rd3730.pop (by native_decide) (by evm_ov)
    have rd3732 := rd3731.pop (by native_decide) (by evm_ov)
    have rd3733 := rd3732.dup1 (by native_decide) (by evm_ov)
    have rd3734 := rd3733.dup3 (by native_decide) (by evm_ov)
    have rd3735 := rd3734.mul (by native_decide) (by evm_ov)
    have rd3736 := rd3735.dup3 (by native_decide) (by evm_ov)
    have rd3737 := rd3736.dup3 (by native_decide) (by evm_ov)
    have rd3738 := rd3737.dup3 (by native_decide) (by evm_ov)
    have rd3739 := rd3738.dup2 (by native_decide) (by evm_ov)
    have rd3742 := rd3739.push2 ⟨3744⟩ (by native_decide) (by evm_ov)
    have rd3744 := rd3742.jumpiT (by native_decide) ha (by jump_dest) (by evm_ov)
    have rd3745 := rd3744.jumpdest (by native_decide) (by evm_ov)
    have rd3746 := rd3745.div (by native_decide) (by evm_ov)
    have rd3747 := rd3746.eq (by native_decide) (by evm_ov)
    rw [heq1] at rd3747
    have rd3748 := rd3747.jumpdest (by native_decide) (by evm_ov)
    have rd3751 := rd3748.push2 ⟨3756⟩ (by native_decide) (by evm_ov)
    have rd3756 := rd3751.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)
    have rd3757 := rd3756.jumpdest (by native_decide) (by evm_ov)
    have rd3758 := rd3757.swap3 (by native_decide) (by evm_ov)
    have rd3759 := rd3758.swap2 (by native_decide) (by evm_ov)
    have rd3760 := rd3759.pop (by native_decide) (by evm_ov)
    have rd3761 := rd3760.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, rd3761.jump (by native_decide) hret (by evm_ov)⟩

/-!
## Shared internal routine: solc `min` @ pc `3778`

`bite` calls this 3× (dunkRoom, dart, dink). Entry `[a, b, ret, R]`; returns to `ret` the smaller:
`b` when `b ≤ a` (`gt b a = 0`), else `a`. Solc `min(x,y) = x>y ? y : x` (see `execMinFunctionReturn*`).

Disassembly (3778–3801, sharing the `3756` return trampoline on the `b>a` branch):
```
3778 JUMPDEST; 3779 PUSH1 0; 3781 DUP2; 3782 DUP4; 3783 GT; 3784 ISZERO; 3785 PUSH2 3795; 3788 JUMPI
  (b≤a) 3795 JUMPDEST; 3796 POP; 3797 SWAP1; 3798 SWAP2; 3799 SWAP1; 3800 POP; 3801 JUMP    → b
  (b>a) 3789 POP; 3790 DUP1; 3791 PUSH2 3756; 3794 JUMP; 3756 …return trampoline…            → a
```
-/
set_option maxHeartbeats 1000000 in
theorem RD.catBiteMin {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3778⟩
      (a :: b :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      ((if UInt256.gt b a = ⟨0⟩ then b else a) :: R) mem aw rdata acc k' C' := by
  have rd3779 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd3781 := rd3779.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3782 := rd3781.dup2 (by native_decide) (by evm_ov)
  have rd3783 := rd3782.dup4 (by native_decide) (by evm_ov)
  have rd3784 := rd3783.gt (by native_decide) (by evm_ov)
  have rd3785 := rd3784.iszero (by native_decide) (by evm_ov)
  have rd3788 := rd3785.push2 ⟨3795⟩ (by native_decide) (by evm_ov)
  by_cases hgt : UInt256.gt b a = ⟨0⟩
  · -- b ≤ a: return b
    have rd3795 := rd3788.jumpiT (by native_decide) (by rw [hgt]; decide) (by jump_dest) (by evm_ov)
    have rd3796 := rd3795.jumpdest (by native_decide) (by evm_ov)
    have rd3797 := rd3796.pop (by native_decide) (by evm_ov)
    have rd3798 := rd3797.swap1 (by native_decide) (by evm_ov)
    have rd3799 := rd3798.swap2 (by native_decide) (by evm_ov)
    have rd3800 := rd3799.swap1 (by native_decide) (by evm_ov)
    have rd3801 := rd3800.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by rw [if_pos hgt]; exact rd3801.jump (by native_decide) hret (by evm_ov)⟩
  · -- b > a: return a
    have rd3789 := rd3788.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hgt) (by evm_ov)
    have rd3790 := rd3789.pop (by native_decide) (by evm_ov)
    have rd3791 := rd3790.dup1 (by native_decide) (by evm_ov)
    have rd3794 := rd3791.push2 ⟨3756⟩ (by native_decide) (by evm_ov)
    have rd3756 := rd3794.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd3757 := rd3756.jumpdest (by native_decide) (by evm_ov)
    have rd3758 := rd3757.swap3 (by native_decide) (by evm_ov)
    have rd3759 := rd3758.swap2 (by native_decide) (by evm_ov)
    have rd3760 := rd3759.pop (by native_decide) (by evm_ov)
    have rd3761 := rd3760.pop (by native_decide) (by evm_ov)
    exact ⟨_, _, by rw [if_neg hgt]; exact rd3761.jump (by native_decide) hret (by evm_ov)⟩

/-!
## Shared checked-sub @ pc `3762` and checked-add @ pc `3802`

These match the generic `solcCheckedSub/AddSuccessWf` shapes (both returning via the shared `3756`
trampoline), so `bite`'s `checkedSub "room"` and `checkedAdd "litterNew"` reuse the library lemmas.
The wrappers below specialize the PCs and discharge the `Wf`/jump-dest side goals. -/
theorem RD.catBiteCheckedSub {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3762⟩
      (b :: a :: ret :: R) mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.sub a b :: R) mem aw rdata acc k' C' :=
  RD.solcCheckedSubSuccess (okPc := ⟨3756⟩) rd
    (by unfold solcCheckedSubSuccessWf; repeat' first | apply And.intro | native_decide)
    hle hret (by native_decide) hov

theorem RD.catBiteCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3802⟩
      (b :: a :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      ((a + b) :: R) mem aw rdata acc k' C' :=
  RD.solcCheckedAddSuccess (okPc := ⟨3756⟩) rd
    (by unfold solcCheckedAddSuccessWf; repeat' first | apply And.intro | native_decide)
    hfit hret (by native_decide) hov

/-!
## `vat.ilks(ilk)` STATICCALL @ pc `1248` (guard `1233`)

Completes the ilks call helper (`BiteCallIlks` only reaches the guard `1233`): steps the
`EXTCODESIZE` guard + `STATICCALL` and exposes the `typedCallViaEVM` coupling (`callCoincides`),
landing at pc `1249` with the success flag on top (the 5-word return decode that follows is
optimizer-interleaved with the urns calldata build, hand-traced in the main body).  Generic over the
deep stack tail `t`, the calldata memory `mem` and the argument list via `hencode`. -/
theorem RD.catBiteIlksStaticcall
    {cA gh bl σ σ₀ A I} {g : UInt256} {args : List Value}
    {target aw : UInt256} {mem o : ByteArray} {t : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1233⟩
      (target :: target :: catBiteIlksOutPtr :: catBiteIlksInSize :: catBiteIlksOutPtr ::
        catBiteIlksOutSize :: t)
      mem aw o (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode : config.externalABI.encode? "ilks" args =
        some (mem.readWithPadding catBiteIlksOutPtr.toNat catBiteIlksInSize.toNat))
    (hov : t.length + 8 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: t)
        (o'.write 0 mem catBiteIlksOutPtr.toNat
          (min catBiteIlksOutSize (UInt256.ofNat o'.size)).toNat)
        awout o' (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 target) "ilks" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') false
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1248⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1233⟩) (okPc := ⟨1245⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd1249, hosz⟩ :=
    RD.solcStaticcall rd1248 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o', A', _, k', C', rd1249, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := target)
    (mem := mem) (inOff := catBiteIlksOutPtr) (inSize := catBiteIlksInSize)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-!
## Main success trace, assembled as segments `catBiteTraceSegN`

Each segment is a self-contained RD reach lemma `pcIn stackIn → ∃ …, RD pcOut stackOut …`,
composed at the end into `catBiteSuccessTrace`.  Values computed by the bytecode are exposed as
existentials / matched to the `catBiteSourceSuccess` contract.
-/

/-- **Seg 1** (`1163 → 1249`): from the `bite` routine entry, build the `vat.ilks(ilk)` calldata,
clear the `EXTCODESIZE` guard, issue the `STATICCALL`, and expose the `typedCallViaEVM` coupling. -/
theorem catBiteTraceSeg1 {cA gh bl σ σ₀ A I} {g : UInt256}
    {urn : UInt256} {R : List UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1163⟩
      (urn :: biteIlkWord I :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (catBiteVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 17 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: catBiteIlksEndPtr :: catBiteIlksSelectorWord ::
          catBiteVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: biteIlkWord I :: R)
        (o'.write 0 (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
          catBiteIlksOutPtr.toNat (min catBiteIlksOutSize (UInt256.ofNat o'.size)).toNat)
        awout o' (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ I)) "ilks" 0 [biteIlkVal I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') false
    ∧ o'.size < UInt256.size := by
  obtain ⟨_, _, rd1233⟩ := RD.catBiteIlksToStaticcallGuard (hR := by omega) rd
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    simpa [biteIlkBytes, biteIlkWord, biteUrnsIlkBytes, biteUrnsIlkWord] using
      biteUrnsIlkBytes_eq_toBytesBE (I := I) hsz36
  have hencode : config.externalABI.encode? "ilks" [biteIlkVal I] =
      some ((catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).readWithPadding
        catBiteIlksOutPtr.toNat catBiteIlksInSize.toNat) := by
    simpa [biteIlkVal] using
      catBiteIlksEncode_eq (biteIlkWord I) (biteIlkBytes I) solcFreePtrMem_size hbytes
  obtain ⟨cA', σ', z, o', A', awout, k', C', rd1249, hcall, hosz⟩ :=
    RD.catBiteIlksStaticcall (target := catBiteVatTargetWord σ I) rd1233 hcodeSize hdepth hencode
      (by simp only [List.length_cons]; omega)
  exact ⟨cA', σ', z, o', A', awout, k', C', rd1249, hcall, hosz⟩

/-- **Seg 2a** (`1249 → 1289`): the ilks `STATICCALL` success guard + the `returndatasize ≥ 160`
length check.  Pops the call frame (`endPtr`/`selWord`/`target` = `d0`/`d1`/`d2`), reads the free
pointer (`= 128`), and clears the return-size guard, landing with `[128, rest]`. -/
theorem catBiteTraceSeg2a {cA gh bl σ σ₀ A I} {g : UInt256}
    {status d0 d1 d2 : UInt256} {rest : List UInt256}
    {mem o' : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (status :: d0 :: d1 :: d2 :: rest) mem aw o' acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (ho160 : 160 ≤ o'.size) (hosz : o'.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: rest → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1289⟩
      (⟨128⟩ :: rest) mem aw o' acc k' C' := by
  obtain ⟨_, _, rd1267⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1249⟩) (okPc := ⟨1265⟩) rd hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1268 := rd1267.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1269 := rd1268.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1270 := rd1269.pop (by native_decide) (by omega)
  have rd1272 := rd1270.push1 ⟨64⟩ (by native_decide) (by omega)
  have rd1273 := RD.mload 0 ⟨128⟩ aw rd1272 (by native_decide) hMload64Cost hMload64Value
    hMload64Aw (by omega)
  have rd1274 := rd1273.returndatasize (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1276 := rd1274.push1 ⟨160⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1277 := rd1276.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1278 := rd1277.lt (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o'.size) ⟨160⟩ = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' o'.size hosz]
    exact ho160
  rw [hlt] at rd1278
  have rd1279 := rd1278.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1279
  have rd1282 := rd1279.push2 ⟨1287⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1287 := rd1282.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd1288 := rd1287.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1288.pop (by native_decide) (by simp only [List.length_cons]; omega)⟩

/-- **Seg 2b** (`1289 → 1306`): read the three ilks tuple words used by `bite` — `iRate`@mem160,
`iSpot`@mem192, `iDust`@mem256 (the `iArt`/`iLine` slots are skipped) — via the interleaved MLOADs,
landing with `[iDust, 64, iRate, iSpot, 0,0,0,0, urn, ilk, R]`. -/
theorem catBiteTraceSeg2b {cA gh bl σ σ₀ A I} {g : UInt256}
    {urn ilk iRate iSpot iDust : UInt256} {R : List UInt256}
    {mem o' : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1289⟩
      (⟨128⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R) mem aw o' acc k C)
    (hRate : (if (⟨160⟩ : UInt256).toNat ≥ mem.size ∨ (⟨160⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 160 32))) = iRate)
    (hRateCost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨160⟩ : UInt256) :: ⟨128⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hRateAw : UInt256.ofNat (MachineState.M aw.toNat 160 32) = aw)
    (hSpot : (if (⟨192⟩ : UInt256).toNat ≥ mem.size ∨ (⟨192⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 192 32))) = iSpot)
    (hSpotCost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨192⟩ : UInt256) :: ⟨64⟩ :: iRate :: ⟨128⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hSpotAw : UInt256.ofNat (MachineState.M aw.toNat 192 32) = aw)
    (hDust : (if (⟨256⟩ : UInt256).toNat ≥ mem.size ∨ (⟨256⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 256 32))) = iDust)
    (hDustCost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨256⟩ : UInt256) :: ⟨64⟩ :: iRate :: iSpot :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hDustAw : UInt256.ofNat (MachineState.M aw.toNat 256 32) = aw)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1306⟩
      (iDust :: ⟨64⟩ :: iRate :: iSpot :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o' acc k' C' := by
  have rd1291 := rd.push1 ⟨32⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1292 := rd1291.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1293 := rd1292.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ from by native_decide] at rd1293
  have rd1294 := RD.mload 0 iRate aw rd1293 (by native_decide) hRateCost hRate hRateAw
    (by simp only [List.length_cons]; omega)
  have rd1296 := rd1294.push1 ⟨64⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1297 := rd1296.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1298 := rd1297.dup4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1299 := rd1298.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨64⟩ = ⟨192⟩ from by native_decide] at rd1299
  have rd1300 := RD.mload 0 iSpot aw rd1299 (by native_decide) hSpotCost hSpot hSpotAw
    (by simp only [List.length_cons]; omega)
  have rd1302 := rd1300.push1 ⟨128⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1303 := rd1302.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1304 := rd1303.swap4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1305 := rd1304.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ from by native_decide] at rd1305
  exact ⟨_, _, RD.mload 0 iDust aw rd1305 (by native_decide) hDustCost hDust hDustAw
    (by simp only [List.length_cons]; omega)⟩

/-- `DUP12` stepping primitive — missing from `Reasoning.Stepping` (only `dup11`/`dup13` exist);
proved here modeled on `dup11_xstep`. -/
theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

/-- `RD.DUP12` reach combinator (companion to the missing `dup12_xstep`). -/
theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

/-- **Seg 2c1** (`1306 → 1344`): `SLOAD ⟨3⟩` (the vat, for the urns target) then build the
`urns(bytes32,address)` calldata in memory — selector`@128`, `ilk`@132, masked `urn`@164 — so the
memory becomes `biteUrnsCalldataMem ilk (land biteAddrMaskWord urn) mem`.  Ends before the deep-swap
frame assembly with `[biteAddrMaskWord, 128, vat3, iDust, 64, iRate, iSpot, 0,0,0,0, urn, ilk, R]`. -/
theorem catBiteTraceSeg2c1 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {urn ilk iRate iSpot iDust : UInt256} {R : List UInt256}
    {mem o' : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1306⟩
      (iDust :: ⟨64⟩ :: iRate :: iSpot :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o' (cA', σ') k C)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩)
    (hFreeCost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) ::
          catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hFreeAw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hSel : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨128⟩ : UInt256) :: biteUrnsSelectorShifted :: ⟨128⟩ ::
          catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MSTORE = 0)
    (hSelAw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw)
    (hIlk : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨132⟩ : UInt256) :: ilk :: ⟨128⟩ ::
          catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MSTORE = 0)
    (hIlkAw : UInt256.ofNat (MachineState.M aw.toNat 132 32) = aw)
    (hUrn : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨164⟩ : UInt256) :: UInt256.land biteAddrMaskWord urn ::
          biteAddrMaskWord :: ⟨128⟩ :: catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MSTORE = 0)
    (hUrnAw : UInt256.ofNat (MachineState.M aw.toNat 164 32) = aw)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1344⟩
      (biteAddrMaskWord :: ⟨128⟩ :: catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R)
      (biteUrnsCalldataMem ilk (UInt256.land biteAddrMaskWord urn) mem) aw o' (cA', σ') k' C' := by
  have rd1306 := rd.push1 ⟨3⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨k1308, C1308, rd1308⟩ := rd1306.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1308' : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1309⟩
      (catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R) mem aw o' (cA', σ') k1308 C1308 := rd1308
  have rd1309 := rd1308'.dup3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1310 := RD.mload 0 ⟨128⟩ aw rd1309 (by native_decide) hFreeCost hFree hFreeAw
    (by simp only [List.length_cons]; omega)
  have rd1311 := rd1310.push4 ⟨151596951⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1316 := rd1311.push1 ⟨226⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1318 := rd1316.shl (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1319 := rd1318.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1320 := RD.mstore 0 (biteUrnsSelectorMem mem) aw rd1319 (by native_decide) hSel
    (by rfl) hSelAw (by simp only [List.length_cons]; omega)
  have rd1321 := rd1320.push1 ⟨4⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1323 := rd1321.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1324 := rd1323.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd1324
  have rd1325 := rd1324.dup13 (by native_decide) (by omega)
  have rd1326 := rd1325.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1327 := RD.mstore 0 (biteUrnsIlkMem ilk mem) aw rd1326 (by native_decide) hIlk
    (by rfl) hIlkAw (by simp only [List.length_cons]; omega)
  have rd1328 := rd1327.push1 ⟨1⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1330 := rd1328.push1 ⟨1⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1332 := rd1330.push1 ⟨160⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1334 := rd1332.shl (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1335 := rd1334.sub (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1336 := RD.dup12 rd1335 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1337 := rd1336.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1338 := rd1337.and (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1339 := rd1338.push1 ⟨36⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1341 := rd1339.dup4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1342 := rd1341.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd1342
  exact ⟨_, _, RD.mstore 0 (biteUrnsCalldataMem ilk (UInt256.land biteAddrMaskWord urn) mem) aw
    rd1342 (by native_decide) hUrn (by rfl) hUrnAw (by simp only [List.length_cons]; omega)⟩

/-- **Seg 2c2** (`1344 → 1383`): the deep-swap assembly of the `urns` `STATICCALL` frame.  Surfaces
`iRate`/`iSpot`/`iDust` into position, drops the padding zeros, computes `target = vat3 & addrMask`,
and lays `[target, target, 128, 68, 128, 64, …]` at the `EXTCODESIZE` guard (`catBiteUrnsStaticcall`
input).  `target := land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord`. -/
theorem catBiteTraceSeg2c2 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {urn ilk iRate iSpot iDust : UInt256} {R : List UInt256}
    {mem o' : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1344⟩
      (biteAddrMaskWord :: ⟨128⟩ :: catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R) mem aw o' (cA', σ') k C)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩)
    (hFreeCost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: biteAddrMaskWord :: ⟨128⟩ ::
          catSlotWord ⟨3⟩ σ' I :: iDust :: ⟨64⟩ :: iRate :: iSpot ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hFreeAw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
        UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨196⟩ :: ⟨606387804⟩ ::
        UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
        ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o' (cA', σ') k' C' := by
  have rd1345 := rd.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1346 := RD.mload 0 ⟨128⟩ aw rd1345 (by native_decide) hFreeCost hFree hFreeAw
    (by simp only [List.length_cons]; omega)
  have rd1347 := rd1346.swap6 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1348 := rd1347.swap10 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1349 := rd1348.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1350 := rd1349.swap6 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1351 := rd1350.swap8 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1352 := rd1351.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1353 := rd1352.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1354 := rd1353.swap6 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1355 := rd1354.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1357 := rd1355.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1358 := rd1357.swap5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1359 := rd1358.dup6 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1360 := rd1359.swap5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1361 := rd1360.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1362 := rd1361.and (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1363 := rd1362.swap3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1368 := rd1363.push4 ⟨606387804⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1369 := rd1368.swap3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1371 := rd1369.push1 ⟨68⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1372 := rd1371.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1373 := rd1372.dup3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1374 := rd1373.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd1374
  have rd1375 := rd1374.swap4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1376 := rd1375.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1377 := rd1376.dup3 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1378 := rd1377.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1379 := rd1378.sub (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.sub ⟨128⟩ ⟨128⟩ = ⟨0⟩ from by native_decide] at rd1379
  have rd1380 := rd1379.add (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show (⟨0⟩ : UInt256) + ⟨68⟩ = ⟨68⟩ from by native_decide] at rd1380
  have rd1381 := rd1380.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1382 := rd1381.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1382.dup1 (by native_decide) (by simp only [List.length_cons]; omega)⟩

/-- Acc-generic `vat.urns` guard + `STATICCALL` (the foundation `catBiteUrnsStaticcall` fixes the acc
to the original `(cA, σ)`; after the ilks STATICCALL the acc is `(cAx, σx)`).  Exposes the
`typedCallViaEVM` coupling from the post-ilks state `{… with accountMap := σx, createdAccounts := cAx}`. -/
theorem RD.catBiteUrnsStaticcallGen
    {cA gh bl σ σ₀ A I} {g : UInt256} {args : List Value}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {target outPtr aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (target :: target :: outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩ :: R)
      mem aw o (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode : config.externalABI.encode? "urns" args =
        some (mem.readWithPadding outPtr.toNat 68))
    (hov : R.length + 8 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (o'.write 0 mem outPtr.toNat (min (⟨64⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        awout o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 target) "urns" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') false
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1398⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1383⟩) (okPc := ⟨1395⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd1399, hosz⟩ :=
    RD.solcStaticcall rd1398 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o', A', _, k', C', rd1399, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := target)
    (mem := mem) (inOff := outPtr) (inSize := ⟨68⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- **Seg 3** (`1399 → 1447`): the urns `STATICCALL` success guard + 2-word return decode
(`ink`@mem128, `art`@mem160), landing with `[art, ink, R]`.  Composes the (already acc-generic)
`catBiteUrnsCallSucceeded` + `catBiteUrnsReturnDecodeOk`. -/
theorem catBiteTraceSeg3 {cA gh bl σ σ₀ A I} {g : UInt256}
    {status d0 d1 d2 inkW artW aw1 aw2 : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (status :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hlo : 64 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32)))
        = inkW)
    (hMload128Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨128⟩ : UInt256) :: ⟨128⟩ :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw1)
    (hMload160Value :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size ∨ (⟨160⟩ : UInt256) ≥ aw1 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨160⟩ : UInt256).toNat 32)))
        = artW)
    (hMload160Cost : ∀ s : State, s.machineState.activeWords = aw1 →
        s.machineState.stack = (⟨160⟩ : UInt256) :: inkW :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload160Aw : UInt256.ofNat (MachineState.M aw1.toNat 160 32) = aw2)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1447⟩
      (artW :: inkW :: R) mem aw2 o acc k' C' := by
  obtain ⟨_, _, rd1420⟩ := RD.catBiteUrnsCallSucceeded rd hstatus (by omega)
  exact RD.catBiteUrnsReturnDecodeOk rd1420 hlo hhi hMload64Value hMload64Cost hMload64Aw
    hMload128Value hMload128Cost hMload128Aw hMload160Value hMload160Cost hMload160Aw
    (by omega)

/-- **Seg 4** (`1447 → 1521`): `require(live == 1)` — `SLOAD ⟨2⟩`, drop the two padding zeros, and
take the equality-true JUMPI.  Success path (`hlive`). -/
theorem catBiteTraceSeg4 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1447⟩
      (art :: ink :: ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hlive : catSlotWord ⟨2⟩ σ' I = ⟨1⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd1449 := rd.push1 ⟨2⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨k1450, C1450, rd1450raw⟩ := rd1449.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1450 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1450⟩
      (catSlotWord ⟨2⟩ σ' I :: art :: ink :: ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') k1450 C1450 := rd1450raw
  have rd1451 := rd1450.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1452 := rd1451.swap4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1453 := rd1452.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1454 := rd1453.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1455 := rd1454.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1457 := rd1455.push1 ⟨1⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1458 := rd1457.eq (by native_decide) (by simp only [List.length_cons]; omega)
  rw [hlive, show UInt256.eq (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ from by native_decide] at rd1458
  have rd1461 := rd1458.push2 ⟨1521⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1461.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩

/-- **Seg 5** (`1521 → 1620`): `require(spot > 0 && inkSpot < artRateUnsafe)`.  Computes the two
`checkedMul`s (`artRate = art*rate`, `inkSpot = ink*spot`) via the shared routine `@3720`, then the
`LT` and the require.  Success path (`hspotPos`, `hunsafe`); `inkSpot`/`artRate` are transient. -/
theorem catBiteTraceSeg5 {cA gh bl σ σ₀ A I} {g : UInt256}
    {art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hspotPos : 0 < iSpot.toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k' C' := by
  have rd1522 := rd.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1524 := rd1522.push1 ⟨0⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1525 := rd1524.dup5 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1526 := rd1525.gt (by native_decide) (by simp only [List.length_cons]; omega)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < iSpot.toNat by simpa using hspotPos)] at rd1526
  have rd1527 := rd1526.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1528 := rd1527.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd1528
  have rd1531 := rd1528.push2 ⟨1554⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1532 := rd1531.jumpiNT (by native_decide) rfl (by simp only [List.length_cons]; omega)
  have rd1533 := rd1532.pop (by native_decide) (by simp only [List.length_cons]; omega)
  -- first checkedMul: artRate = art * rate
  have rd1536 := rd1533.push2 ⟨1542⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1537 := rd1536.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1538 := rd1537.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1541 := rd1538.push2 ⟨3720⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3720a := rd1541.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1542⟩ := RD.catBiteCheckedMul rd3720a
    (by rw [Nat.mul_comm]; exact hfitArtRate) (by native_decide)
    (by simp only [List.length_cons]; omega)
  -- second checkedMul: inkSpot = ink * spot
  have rd1543 := rd1542.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1546 := rd1543.push2 ⟨1552⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1547 := rd1546.dup4 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1548 := rd1547.dup7 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1551 := rd1548.push2 ⟨3720⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3720b := rd1551.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1552⟩ := RD.catBiteCheckedMul rd3720b
    (by rw [Nat.mul_comm]; exact hfitInkSpot) (by native_decide)
    (by simp only [List.length_cons]; omega)
  -- LT + require
  have rd1553 := rd1552.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1554 := rd1553.lt (by native_decide) (by simp only [List.length_cons]; omega)
  have hltunsafe : UInt256.lt (UInt256.mul ink iSpot) (UInt256.mul art iRate) = ⟨1⟩ := by
    apply ult_one
    rw [u256_mul_toNat, u256_mul_toNat, ← u256_mul_op_toNat, ← u256_mul_op_toNat]
    exact hunsafe
  rw [hltunsafe] at rd1554
  have rd1555 := rd1554.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1558 := rd1555.push2 ⟨1620⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1558.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩

/-! ### Seg 6 memory layout

The solc `Ilk memory milk = ilks[ilk]` codegen first calls the 96-byte allocator `@3818` (bumps the
free pointer `fp := mem[0x40]` and zero-inits `[fp, fp+96)`), then hashes `keccak(ilk ‖ 1)` in the
`[0,64)` scratch and copies the three struct fields into a *second* fresh 96-byte region at
`q := mem[0x40]` (`= fp+96`).  `catBiteHelperMem`/`catBiteScratchMem`/`catBiteMilkMem` name the three
memory snapshots (allocator output, post-`keccak`-scratch, final `milk` region). -/

/-- Memory after the `@3818` allocator: `mem[0x40] := fp+96`, then `[fp, fp+96)` zero-initialised. -/
noncomputable def catBiteHelperMem (mem : ByteArray) (fp : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨0⟩).write 0
    ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32)
        fp.toNat 32)
      (⟨32⟩ + fp).toNat 32)
    (⟨32⟩ + (⟨32⟩ + fp)).toNat 32

/-- Allocator memory plus the `keccak(ilk ‖ 1)` scratch: `mem[0] := ilk`, `mem[32] := 1`. -/
noncomputable def catBiteScratchMem (mem : ByteArray) (fp ilk : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨1⟩).write 0
    ((UInt256.toByteArray ilk).write 0 (catBiteHelperMem mem fp) 0 32)
    32 32

/-- Final memory: the `milk` struct `[flip, chop, dunk]` written at `[q, q+96)`, with `mem[0x40] :=
q+96`. -/
noncomputable def catBiteMilkMem
    (mem : ByteArray) (fp ilk q flip chop dunk : UInt256) : ByteArray :=
  (UInt256.toByteArray dunk).write 0
    ((UInt256.toByteArray chop).write 0
      ((UInt256.toByteArray flip).write 0
        ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32)
        q.toNat 32)
      (q + ⟨32⟩).toNat 32)
    (q + ⟨64⟩).toNat 32

/-! ### Seg 6 helpers: abstract active-words invariance + zero memory-expansion cost

`Seg 6` keeps memory (`mem`) and active-words (`aw`) fully abstract, so — as in `Seg 2b`/`Seg 2c1` —
every `MSTORE`/`MLOAD`/`KECCAK256` needs its active-words-unchanged + zero-cost side goals.  These
are all consequences of two range bounds (`aw` already covers the `[0, fp+96)` scratch and the
`[q, q+96)` `milk` struct), packaged once here. -/

theorem catBiteAwMInv32 (aw : UInt256) {off : Nat}
    (h : off + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 32 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem catBiteAwMInv64 (aw : UInt256) {off : Nat}
    (h : off + 64 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 64) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 64 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem catBiteMloadCost0 {aw off : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: t →
      memoryExpansionCost s .MLOAD = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]
  rw [hM]; simp

theorem catBiteMstoreCost0 {aw off val : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: val :: t →
      memoryExpansionCost s .MSTORE = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]
  rw [hM]; simp

theorem catBiteKeccakCost0 {aw off sz : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat sz.toNat) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: sz :: t →
      memoryExpansionCost s .KECCAK256 = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  rw [hM]; simp

set_option maxHeartbeats 2000000 in
/-- **Seg 6** (`1620 → 1708`): `Ilk memory milk = ilks[ilk]` (allocate `@3818`, `keccak(ilk‖1)`, load
`flip`/`chop`/`dunk` into the fresh `[q, q+96)` struct) then `checkedSub "room" = box - litter` via
`@3762`.  The three struct fields land in memory (`catBiteMilkMem`); `room` reaches the stack.  `fp`
is the free pointer (`mem[0x40]`) and `q = fp + 96` the struct pointer; `hFp`/`hQ`/`hKec` are the
free-pointer reads + the `keccak` scratch read, `hawFp`/`hawQ` the active-words range bounds. -/
theorem catBiteTraceSeg6 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk fp q : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') k C)
    (hFp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hQ : (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp ilk).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteScratchMem mem fp ilk).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = q)
    (hKec : (catBiteScratchMem mem fp ilk).readWithPadding 0 64 =
        UInt256.toByteArray ilk ++ UInt256.toByteArray ⟨1⟩)
    (hawFp : fp.toNat + 96 ≤ aw.toNat * 32)
    (hawQ : q.toNat + 96 ≤ aw.toNat * 32)
    (hfpsz : fp.toNat + 96 < UInt256.size)
    (hqsz : q.toNat + 96 < UInt256.size)
    (hle : (solcSlotWord σ' I ⟨6⟩).toNat ≤ (solcSlotWord σ' I ⟨5⟩).toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (UInt256.sub (solcSlotWord σ' I ⟨5⟩) (solcSlotWord σ' I ⟨6⟩) ::
        ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteMilkMem mem fp ilk q
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩)))
      aw o (cA', σ') k' C' := by
  -- offset arithmetic
  have e32fp : (⟨32⟩ + fp).toNat = fp.toNat + 32 := uadd_lit32_toNat fp (by omega)
  have e64fp : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_lit32_toNat _ (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  -- active-words invariance witnesses
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := catBiteAwMInv32 aw (by omega)
  have hMfp : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := catBiteAwMInv32 aw (by omega)
  have hM32fp : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + fp).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hM64fp : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + (⟨32⟩ + fp)).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMq : UInt256.ofNat (MachineState.M aw.toNat q.toNat 32) = aw := catBiteAwMInv32 aw (by omega)
  have hMq32 : UInt256.ofNat (MachineState.M aw.toNat (q + ⟨32⟩).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMq64 : UInt256.ofNat (MachineState.M aw.toNat (q + ⟨64⟩).toNat 32) = aw :=
    catBiteAwMInv32 aw (by omega)
  have hMkec : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := catBiteAwMInv64 aw (by omega)
  have hmask0 : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ = ⟨0⟩ :=
    by native_decide
  -- 1620 → 3818 (call the 96-byte allocator)
  have rd1621 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1624 := rd1621.push2 ⟨1628⟩ (by native_decide) (by evm_ov)
  have rd1627 := rd1624.push2 ⟨3818⟩ (by native_decide) (by evm_ov)
  have rd3818 := rd1627.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- 3818 allocator body
  have rd3819 := rd3818.jumpdest (by native_decide) (by evm_ov)
  have rd3821 := rd3819.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3822 := RD.mload 0 fp aw rd3821 (by native_decide) (catBiteMloadCost0 hM64) hFp hM64
    (by evm_ov)
  have rd3823 := rd3822.dup1 (by native_decide) (by evm_ov)
  have rd3825 := rd3823.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3826 := rd3825.add (by native_decide) (by evm_ov)
  have rd3828 := rd3826.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3829 := RD.mstore 0 ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) aw rd3828
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd3830 := rd3829.dup1 (by native_decide) (by evm_ov)
  have rd3832 := rd3830.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3834 := rd3832.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3836 := rd3834.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3838 := rd3836.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3839 := rd3838.shl (by native_decide) (by evm_ov)
  have rd3840 := rd3839.sub (by native_decide) (by evm_ov)
  have rd3841 := rd3840.and (by native_decide) (by evm_ov)
  rw [hmask0] at rd3841
  have rd3842 := rd3841.dup2 (by native_decide) (by evm_ov)
  have rd3843 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32) aw rd3842
    (by native_decide) (catBiteMstoreCost0 hMfp) (by rfl) hMfp (by evm_ov)
  have rd3845 := rd3843.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3846 := rd3845.add (by native_decide) (by evm_ov)
  have rd3848 := rd3846.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3849 := rd3848.dup2 (by native_decide) (by evm_ov)
  have rd3850 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32)
      (⟨32⟩ + fp).toNat 32) aw rd3849
    (by native_decide) (catBiteMstoreCost0 hM32fp) (by rfl) hM32fp (by evm_ov)
  have rd3852 := rd3850.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3853 := rd3852.add (by native_decide) (by evm_ov)
  have rd3855 := rd3853.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3856 := rd3855.dup2 (by native_decide) (by evm_ov)
  have rd3857 := RD.mstore 0 (catBiteHelperMem mem fp) aw rd3856
    (by native_decide) (catBiteMstoreCost0 hM64fp) (by rfl) hM64fp (by evm_ov)
  have rd3858 := rd3857.pop (by native_decide) (by evm_ov)
  have rd3859 := rd3858.swap1 (by native_decide) (by evm_ov)
  have rd1628 := rd3859.jump (by native_decide) (by jump_dest) (by evm_ov)
  -- 1628 → keccak scratch build
  have rd1629 := rd1628.jumpdest (by native_decide) (by evm_ov)
  have rd1630 := rd1629.pop (by native_decide) (by evm_ov)
  have rd1632 := rd1630.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1633 := rd1632.dup9 (by native_decide) (by evm_ov)
  have rd1634 := rd1633.dup2 (by native_decide) (by evm_ov)
  have rd1635 := RD.mstore 0 ((UInt256.toByteArray ilk).write 0 (catBiteHelperMem mem fp) 0 32)
    aw rd1634 (by native_decide) (catBiteMstoreCost0 hM0) (by rfl) hM0 (by evm_ov)
  have rd1637 := rd1635.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1639 := rd1637.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1640 := rd1639.dup2 (by native_decide) (by evm_ov)
  have rd1641 := rd1640.dup2 (by native_decide) (by evm_ov)
  have rd1642 := RD.mstore 0 (catBiteScratchMem mem fp ilk) aw rd1641
    (by native_decide) (catBiteMstoreCost0 hM32) (by rfl) hM32 (by evm_ov)
  have rd1644 := rd1642.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1645 := rd1644.dup1 (by native_decide) (by evm_ov)
  have rd1646 := rd1645.dup5 (by native_decide) (by evm_ov)
  have rd1647 := rd1646.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) aw (by native_decide)
    (catBiteKeccakCost0 hMkec)
    (by simp only [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKec]; exact mappingSlot_single ilk ⟨1⟩)
    hMkec (by evm_ov)
  -- 1647 → struct copy (flip@q, chop@q+32, dunk@q+64)
  have rd1648 := rd1647.dup2 (by native_decide) (by evm_ov)
  have rd1649 := RD.mload 0 q aw rd1648 (by native_decide) (catBiteMloadCost0 hM64) hQ hM64
    (by evm_ov)
  have rd1651 := rd1649.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd1652 := rd1651.dup2 (by native_decide) (by evm_ov)
  have rd1653 := rd1652.add (by native_decide) (by evm_ov)
  have rd1654 := rd1653.dup4 (by native_decide) (by evm_ov)
  have rd1655 := RD.mstore 0 ((UInt256.toByteArray (q + ⟨96⟩)).write 0
      (catBiteScratchMem mem fp ilk) 64 32) aw rd1654
    (by native_decide) (catBiteMstoreCost0 hM64) (by rfl) hM64 (by evm_ov)
  have rd1656 := rd1655.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1657⟩ := rd1656.sload (by native_decide) (by evm_ov)
  have rd1659 := rd1657.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1661 := rd1659.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1663 := rd1661.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd1664 := rd1663.shl (by native_decide) (by evm_ov)
  have rd1665 := rd1664.sub (by native_decide) (by evm_ov)
  have rd1666 := rd1665.and (by native_decide) (by evm_ov)
  have rd1667 := rd1666.dup2 (by native_decide) (by evm_ov)
  have rd1668 := RD.mstore 0 ((UInt256.toByteArray
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
      ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
    aw rd1667 (by native_decide) (catBiteMstoreCost0 hMq) (by rfl) hMq (by evm_ov)
  have rd1669 := rd1668.swap4 (by native_decide) (by evm_ov)
  have rd1670 := rd1669.dup2 (by native_decide) (by evm_ov)
  have rd1671 := rd1670.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1672⟩ := rd1671.sload (by native_decide) (by evm_ov)
  have rd1673 := rd1672.swap3 (by native_decide) (by evm_ov)
  have rd1674 := rd1673.dup5 (by native_decide) (by evm_ov)
  have rd1675 := rd1674.add (by native_decide) (by evm_ov)
  have rd1676 := rd1675.swap3 (by native_decide) (by evm_ov)
  have rd1677 := rd1676.swap1 (by native_decide) (by evm_ov)
  have rd1678 := rd1677.swap3 (by native_decide) (by evm_ov)
  have rd1679 := RD.mstore 0 ((UInt256.toByteArray
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))).write 0
      ((UInt256.toByteArray
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))).write 0
        ((UInt256.toByteArray (q + ⟨96⟩)).write 0 (catBiteScratchMem mem fp ilk) 64 32) q.toNat 32)
      (q + ⟨32⟩).toNat 32) aw rd1678
    (by native_decide) (catBiteMstoreCost0 hMq32) (by rfl) hMq32 (by evm_ov)
  have rd1681 := rd1679.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd1682 := rd1681.swap1 (by native_decide) (by evm_ov)
  have rd1683 := rd1682.swap2 (by native_decide) (by evm_ov)
  have rd1684 := rd1683.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1685⟩ := rd1684.sload (by native_decide) (by evm_ov)
  have rd1686 := rd1685.swap1 (by native_decide) (by evm_ov)
  have rd1687 := rd1686.dup3 (by native_decide) (by evm_ov)
  have rd1688 := rd1687.add (by native_decide) (by evm_ov)
  have rd1689 := RD.mstore 0 (catBiteMilkMem mem fp ilk q
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩))) aw rd1688
    (by native_decide) (catBiteMstoreCost0 hMq64) (by rfl) hMq64 (by evm_ov)
  -- 1689 → box/litter loads + checkedSub
  have rd1691 := rd1689.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1692⟩ := rd1691.sload (by native_decide) (by evm_ov)
  have rd1694 := rd1692.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1695⟩ := rd1694.sload (by native_decide) (by evm_ov)
  have rd1696 := rd1695.swap2 (by native_decide) (by evm_ov)
  have rd1697 := rd1696.swap3 (by native_decide) (by evm_ov)
  have rd1698 := rd1697.swap2 (by native_decide) (by evm_ov)
  have rd1699 := rd1698.dup3 (by native_decide) (by evm_ov)
  have rd1700 := rd1699.swap2 (by native_decide) (by evm_ov)
  have rd1703 := rd1700.push2 ⟨1708⟩ (by native_decide) (by evm_ov)
  have rd1704 := rd1703.swap2 (by native_decide) (by evm_ov)
  have rd1707 := rd1704.push2 ⟨3762⟩ (by native_decide) (by evm_ov)
  have rd3762 := rd1707.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.catBiteCheckedSub rd3762 hle (by native_decide) (by evm_ov)

/-! ## Seg 7 : the arithmetic body + `grab`/`fess` calls (`1708 → 2382`)

From `Seg 6`'s output (pc `1708`) through the `require`s, the `min`/`checkedMul`/inline-div DSMath
chain that computes `dart`/`dink`, the two void external `CALL`s (`vat.grab`, `vow.fess`), the
`tab`/`litterNew` arithmetic, and the `SSTORE litter@6`.  Split into `Seg7a…Seg7g`. -/

/-- `DUP16` stepping primitive — missing from `Reasoning.Stepping` (like `dup12`); modeled on
`dup12_xstep` / `Permit`'s local `dup16`. -/
theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
              oo :: pp :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp ::
          t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

/-- `RD.DUP16` reach combinator. -/
theorem RD.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp ::
        t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup16_xstep hc hp hdec hs hov)

/-- `PUSH8` reach combinator (via the width-generic `pushConst`); `bite` pushes `WAD` (`0xde0b…`)
with `PUSH8`. -/
theorem RD.push8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH8, some (argv, 8)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 9) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) :=
  h.pushConst argv (by decide) hdec hov

/-- **Seg 7a** (`1708 → 1810`): `require(litter < box && room >= dust)`.  Drops the extra padding
zero, `SLOAD`s `box@5`/`litter@6`, and takes both short-circuit branches on the success path. -/
theorem catBiteTraceSeg7a {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hlitterbox : (solcSlotWord σ' I ⟨6⟩).toNat < (solcSlotWord σ' I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1810⟩
      (room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  have rd1709 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1710 := rd1709.swap1 (by native_decide) (by evm_ov)
  have rd1711 := rd1710.pop (by native_decide) (by evm_ov)
  have rd1713 := rd1711.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1714raw⟩ := rd1713.sload (by native_decide) (by evm_ov)
  have rd1714 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1714⟩
      (solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1714raw
  have rd1716 := rd1714.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1717raw⟩ := rd1716.sload (by native_decide) (by evm_ov)
  have rd1717 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1717⟩
      (solcSlotWord σ' I ⟨6⟩ :: solcSlotWord σ' I ⟨5⟩ :: room :: ⟨0⟩ :: q :: art :: ink :: iDust ::
        iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd1717raw
  have rd1718 := rd1717.lt (by native_decide) (by evm_ov)
  rw [ult_one hlitterbox] at rd1718
  have rd1719 := rd1718.dup1 (by native_decide) (by evm_ov)
  have rd1720 := rd1719.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1720
  have rd1723 := rd1720.push2 ⟨1729⟩ (by native_decide) (by evm_ov)
  have rd1724 := rd1723.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd1725 := rd1724.pop (by native_decide) (by evm_ov)
  have rd1726 := rd1725.dup6 (by native_decide) (by evm_ov)
  have rd1727 := rd1726.dup2 (by native_decide) (by evm_ov)
  have rd1728 := rd1727.lt (by native_decide) (by evm_ov)
  rw [ult_zero hroomdust] at rd1728
  have rd1729 := rd1728.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1729
  have rd1730 := rd1729.jumpdest (by native_decide) (by evm_ov)
  have rd1733 := rd1730.push2 ⟨1810⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1733.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-- **Seg 7b** (`1810 → 1872`): the `dart` DSMath chain — `dunkRoom = min(milkDunk, room)` (`@3778`),
`dunkRoomWad = dunkRoom*WAD` (`@3720`), `dartDenomRate = dunkRoomWad / rate` (inline div, `rate ≠ 0`),
`dartCandidate = dartDenomRate / milkChop` (inline div, `milkChop ≠ 0`), `dart = min(art,
dartCandidate)` (`@3778`).  The `milkChop`/`milkDunk` struct fields are read from `mem[⟨32⟩+q]`/
`mem[⟨64⟩+q]` (hypotheses `hChop`/`hDunk`).  Computed values are surfaced as variables pinned by the
`h*` equations. -/
theorem catBiteTraceSeg7b {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256}
    {milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate dartCandidate dart : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1810⟩
      (room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem.size ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨32⟩ + q).toNat 32)))
        = milkChop)
    (hDunk : (if (⟨64⟩ + q).toNat ≥ mem.size ∨ (⟨64⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ + q).toNat 32)))
        = milkDunk)
    (haw : q.toNat + 96 ≤ aw.toNat * 32) (hqsz : q.toNat + 96 < UInt256.size)
    (hRatePos : iRate ≠ ⟨0⟩) (hChopPos : milkChop ≠ ⟨0⟩)
    (hDunkRoom : (if UInt256.gt milkDunk room = ⟨0⟩ then milkDunk else room) = dunkRoom)
    (hFitWad : (⟨1000000000000000000⟩ : UInt256).toNat * dunkRoom.toNat < UInt256.size)
    (hDunkRoomWad : UInt256.mul dunkRoom ⟨1000000000000000000⟩ = dunkRoomWad)
    (hDartDenom : UInt256.div dunkRoomWad iRate = dartDenomRate)
    (hDartCand : UInt256.div dartDenomRate milkChop = dartCandidate)
    (hDart : (if UInt256.gt art dartCandidate = ⟨0⟩ then art else dartCandidate) = dart)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1872⟩
      (dart :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have e64q : (⟨64⟩ + q).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hChopAw : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e32q]; omega)
  have hDunkAw : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e64q]; omega)
  have rd1811 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1814 := rd1811.push2 ⟨1872⟩ (by native_decide) (by evm_ov)
  have rd1815 := rd1814.dup5 (by native_decide) (by evm_ov)
  have rd1816 := rd1815.dup5 (by native_decide) (by evm_ov)
  have rd1818 := rd1816.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1819 := rd1818.add (by native_decide) (by evm_ov)
  have rd1820 := RD.mload 0 milkChop aw rd1819 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  have rd1821 := rd1820.dup11 (by native_decide) (by evm_ov)
  have rd1824 := rd1821.push2 ⟨1851⟩ (by native_decide) (by evm_ov)
  have rd1827 := rd1824.push2 ⟨1837⟩ (by native_decide) (by evm_ov)
  have rd1828 := rd1827.dup9 (by native_decide) (by evm_ov)
  have rd1830 := rd1828.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1831 := rd1830.add (by native_decide) (by evm_ov)
  have rd1832 := RD.mload 0 milkDunk aw rd1831 (by native_decide) (catBiteMloadCost0 hDunkAw)
    hDunk hDunkAw (by evm_ov)
  have rd1833 := rd1832.dup8 (by native_decide) (by evm_ov)
  have rd1836 := rd1833.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778a := rd1836.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1837⟩ := RD.catBiteMin rd3778a (by native_decide) (by evm_ov)
  rw [hDunkRoom] at rd1837
  have rd1837j := rd1837.jumpdest (by native_decide) (by evm_ov)
  have rd1838 := RD.push8 rd1837j ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  have rd1847 := rd1838.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720a := rd1847.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1851⟩ := RD.catBiteCheckedMul rd3720a hFitWad (by native_decide) (by evm_ov)
  rw [hDunkRoomWad] at rd1851
  have rd1851j := rd1851.jumpdest (by native_decide) (by evm_ov)
  have rd1852 := rd1851j.dup2 (by native_decide) (by evm_ov)
  have rd1853 := rd1852.push2 ⟨1858⟩ (by native_decide) (by evm_ov)
  have rd1858 := rd1853.jumpiT (by native_decide) hRatePos (by jump_dest) (by evm_ov)
  have rd1859 := rd1858.jumpdest (by native_decide) (by evm_ov)
  have rd1860 := rd1859.div (by native_decide) (by evm_ov)
  rw [hDartDenom] at rd1860
  have rd1861 := rd1860.dup2 (by native_decide) (by evm_ov)
  have rd1864 := rd1861.push2 ⟨1866⟩ (by native_decide) (by evm_ov)
  have rd1866 := rd1864.jumpiT (by native_decide) hChopPos (by jump_dest) (by evm_ov)
  have rd1867 := rd1866.jumpdest (by native_decide) (by evm_ov)
  have rd1868 := rd1867.div (by native_decide) (by evm_ov)
  rw [hDartCand] at rd1868
  have rd1871 := rd1868.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778b := rd1871.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1872⟩ := RD.catBiteMin rd3778b (by native_decide) (by evm_ov)
  rw [hDart] at rd1872
  exact ⟨_, _, rd1872⟩

/-- **Seg 7c** (`1872 → 1985`): `inkDart = ink*dart` (`@3720`), `dinkCandidate = inkDart / art`
(inline div, `art ≠ 0`), `dink = min(ink, dinkCandidate)` (`@3778`), then
`require(dart > 0 && dink > 0)`.  Drops `room` (already consumed).  Computed values surfaced via
`h*`. -/
theorem catBiteTraceSeg7c {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {room q art ink iDust iSpot iRate urn ilk : UInt256}
    {dart inkDart dinkCandidate dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1872⟩
      (dart :: room :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hInkDart : UInt256.mul ink dart = inkDart)
    (hDinkCand : UInt256.div inkDart art = dinkCandidate)
    (hDink : (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate) = dink)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1985⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1873 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1874 := rd1873.swap2 (by native_decide) (by evm_ov)
  have rd1875 := rd1874.pop (by native_decide) (by evm_ov)
  have rd1876 := rd1875.pop (by native_decide) (by evm_ov)
  have rd1878 := rd1876.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1881 := rd1878.push2 ⟨1899⟩ (by native_decide) (by evm_ov)
  have rd1882 := rd1881.dup6 (by native_decide) (by evm_ov)
  have rd1883 := rd1882.dup6 (by native_decide) (by evm_ov)
  have rd1886 := rd1883.push2 ⟨1892⟩ (by native_decide) (by evm_ov)
  have rd1887 := rd1886.dup9 (by native_decide) (by evm_ov)
  have rd1888 := rd1887.dup7 (by native_decide) (by evm_ov)
  have rd1891 := rd1888.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720 := rd1891.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1892⟩ := RD.catBiteCheckedMul rd3720 hFitInkDart (by native_decide) (by evm_ov)
  rw [hInkDart] at rd1892
  have rd1892j := rd1892.jumpdest (by native_decide) (by evm_ov)
  have rd1893 := rd1892j.dup2 (by native_decide) (by evm_ov)
  have rd1894 := rd1893.push2 ⟨1866⟩ (by native_decide) (by evm_ov)
  have rd1866 := rd1894.jumpiT (by native_decide) hArtPos (by jump_dest) (by evm_ov)
  have rd1867 := rd1866.jumpdest (by native_decide) (by evm_ov)
  have rd1868 := rd1867.div (by native_decide) (by evm_ov)
  rw [hDinkCand] at rd1868
  have rd1871 := rd1868.push2 ⟨3778⟩ (by native_decide) (by evm_ov)
  have rd3778 := rd1871.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd1899⟩ := RD.catBiteMin rd3778 (by native_decide) (by evm_ov)
  rw [hDink] at rd1899
  have rd1900 := rd1899.jumpdest (by native_decide) (by evm_ov)
  have rd1901 := rd1900.swap1 (by native_decide) (by evm_ov)
  have rd1902 := rd1901.pop (by native_decide) (by evm_ov)
  have rd1904 := rd1902.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1905 := rd1904.dup3 (by native_decide) (by evm_ov)
  have rd1906 := rd1905.gt (by native_decide) (by evm_ov)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < dart.toNat by simpa using hDartPos)] at rd1906
  have rd1907 := rd1906.dup1 (by native_decide) (by evm_ov)
  have rd1908 := rd1907.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1908
  have rd1911 := rd1908.push2 ⟨1917⟩ (by native_decide) (by evm_ov)
  have rd1912 := rd1911.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd1913 := rd1912.pop (by native_decide) (by evm_ov)
  have rd1915 := rd1913.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1916 := rd1915.dup2 (by native_decide) (by evm_ov)
  have rd1917 := rd1916.gt (by native_decide) (by evm_ov)
  rw [ugt_one (show (⟨0⟩ : UInt256).toNat < dink.toNat by simpa using hDinkPos)] at rd1917
  have rd1918 := rd1917.jumpdest (by native_decide) (by evm_ov)
  have rd1921 := rd1918.push2 ⟨1985⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1921.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-- **Seg 7d** (`1985 → 2073`): `require(dart <= 2^255 && dink <= 2^255)` — the `-int256(·)` bounds
checks (`2^255 = 1 << 255`).  Stack is unchanged on the success path. -/
theorem catBiteTraceSeg7d {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {q art ink iDust iSpot iRate urn ilk dart dink : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1985⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k C)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2073⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd1986 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1988 := rd1986.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1990 := rd1988.push1 ⟨255⟩ (by native_decide) (by evm_ov)
  have rd1991 := rd1990.shl (by native_decide) (by evm_ov)
  have rd1992 := rd1991.dup3 (by native_decide) (by evm_ov)
  have rd1993 := rd1992.gt (by native_decide) (by evm_ov)
  rw [ugt_zero hDartLim] at rd1993
  have rd1994 := rd1993.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1994
  have rd1995 := rd1994.dup1 (by native_decide) (by evm_ov)
  have rd1996 := rd1995.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1996
  have rd1999 := rd1996.push2 ⟨2009⟩ (by native_decide) (by evm_ov)
  have rd2000 := rd1999.jumpiNT (by native_decide) rfl (by evm_ov)
  have rd2001 := rd2000.pop (by native_decide) (by evm_ov)
  have rd2003 := rd2001.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2005 := rd2003.push1 ⟨255⟩ (by native_decide) (by evm_ov)
  have rd2006 := rd2005.shl (by native_decide) (by evm_ov)
  have rd2007 := rd2006.dup2 (by native_decide) (by evm_ov)
  have rd2008 := rd2007.gt (by native_decide) (by evm_ov)
  rw [ugt_zero hDinkLim] at rd2008
  have rd2009 := rd2008.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2009
  have rd2010 := rd2009.jumpdest (by native_decide) (by evm_ov)
  have rd2013 := rd2010.push2 ⟨2073⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2013.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-! ### Seg 7e/7g: `grab`/`fess` calldata-build helpers

The `grab`/`fess` calldata is laid at the *fresh* free pointer `p = mem[0x40] = q+96`, whose region
is beyond the active-words high-water mark — so each `MSTORE` genuinely expands memory.  These helpers
package the two obligations that arise: (1) the successive active-words updates collapse to a single
`M` at the largest offset (`catBiteMCollapse`), and (2) the free-pointer read at `[64,96)` survives all
the writes (`catBiteGrab*_read64`). -/

/-- `M(aw.toNat, o, 32) < UInt256.size` whenever the write window `[o, o+32)` fits in the word range. -/
private theorem catBiteMlt (a : UInt256) (o : ℕ) (ho : o + 32 < UInt256.size) :
    MachineState.M a.toNat o 32 < UInt256.size := by
  simp only [MachineState.M]
  have ha : a.toNat < UInt256.size := a.val.isLt
  omega

/-- Two successive same-size (32) active-words updates at increasing offsets `o1 ≤ o2` collapse to a
single update at `o2` (the first update is subsumed). -/
private theorem catBiteMCollapse (a : UInt256) (o1 o2 : ℕ) (hle : o1 ≤ o2)
    (hb : MachineState.M a.toNat o1 32 < UInt256.size) :
    UInt256.ofNat (MachineState.M (UInt256.ofNat (MachineState.M a.toNat o1 32)).toNat o2 32)
      = UInt256.ofNat (MachineState.M a.toNat o2 32) := by
  rw [UInt256.toNat_ofNat_of_lt hb]
  congr 1
  simp only [MachineState.M]
  rw [Nat.max_assoc]
  congr 1
  exact Nat.max_eq_right (by omega)

/-- Active-words after a size-32 memory op at offset `off`, kept **irreducible** so `isDefEq` treats
it as an atom (unfolding it exposes `M`'s `max`/`Div.div`/`if`, which blows up on the abstract free
pointer) — we `unfold` it only in the helper lemmas below. -/
@[irreducible] private noncomputable def catBiteAwStep (aw : UInt256) (off : ℕ) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat off 32)

/-- The collapse (`catBiteMCollapse`) re-expressed on `catBiteAwStep`, with the outer step in its
`ofNat (M …)` form so it can `rw` a threaded memory-cost / `hawout` goal. -/
private theorem catBiteAwStep_collapse (aw : UInt256) (o1 o2 : ℕ) (hle : o1 ≤ o2)
    (hb : MachineState.M aw.toNat o1 32 < UInt256.size) :
    UInt256.ofNat (MachineState.M (catBiteAwStep aw o1).toNat o2 32) = catBiteAwStep aw o2 := by
  unfold catBiteAwStep
  exact catBiteMCollapse aw o1 o2 hle hb

private theorem catBiteAwStep_toNat (aw : UInt256) (off : ℕ)
    (hb : MachineState.M aw.toNat off 32 < UInt256.size) :
    (catBiteAwStep aw off).toNat = MachineState.M aw.toNat off 32 := by
  unfold catBiteAwStep; exact UInt256.toNat_ofNat_of_lt hb

/-- The `MSTORE` memory-cost witness for an *expanding* write (companion to `catBiteMstoreCost0`):
the cost is `Cₘ (new active words) − Cₘ (old)`.  Proving the `memoryExpansionCost` unfold **once**
here (rather than inline per write) keeps the calldata-build traces within budget. -/
private theorem catBiteMstoreCostM {aw off val : UInt256} {t : List UInt256} :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: val :: t →
      memoryExpansionCost s .MSTORE
        = Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro s haw hstk
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]

/-! #### `grab` calldata memory (7 words at `p, p+4, p+36, p+68, p+100, p+132, p+164`) -/

noncomputable def catBiteGrabSelMemP (p : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.shiftLeft ⟨32419069⟩ ⟨230⟩).toByteArray.write 0 mem p.toNat 32

noncomputable def catBiteGrabIlkMemP (p ilk : UInt256) (mem : ByteArray) : ByteArray :=
  ilk.toByteArray.write 0 (catBiteGrabSelMemP p mem) (p + ⟨4⟩).toNat 32

noncomputable def catBiteGrabUrnMemP (p ilk urn : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.land biteAddrMaskWord urn).toByteArray.write 0 (catBiteGrabIlkMemP p ilk mem)
    (p + ⟨36⟩).toNat 32

noncomputable def catBiteGrabThisMemP (p ilk urn thisW : UInt256)
    (mem : ByteArray) : ByteArray :=
  thisW.toByteArray.write 0 (catBiteGrabUrnMemP p ilk urn mem) (p + ⟨68⟩).toNat 32

noncomputable def catBiteGrabVowMemP (p ilk urn thisW vowRaw : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.land biteAddrMaskWord vowRaw).toByteArray.write 0
    (catBiteGrabThisMemP p ilk urn thisW mem) (p + ⟨100⟩).toNat 32

noncomputable def catBiteGrabDinkMemP (p ilk urn thisW vowRaw dink : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.sub ⟨0⟩ dink).toByteArray.write 0 (catBiteGrabVowMemP p ilk urn thisW vowRaw mem)
    (p + ⟨132⟩).toNat 32

/-- The full 196-byte `grab` calldata laid at the free pointer `p` over base memory `mem`. -/
noncomputable def catBiteGrabCalldataMemP (p ilk urn thisW vowRaw dink dart : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.sub ⟨0⟩ dart).toByteArray.write 0 (catBiteGrabDinkMemP p ilk urn thisW vowRaw dink mem)
    (p + ⟨164⟩).toNat 32

/-! ##### `grab` memory size lower bounds (each write extends beyond the high-water mark) -/

theorem catBiteGrabSelMemP_size (p : UInt256) {mem : ByteArray} (hpmem : p.toNat ≤ mem.size) :
    p.toNat + 32 ≤ (catBiteGrabSelMemP p mem).size := by
  unfold catBiteGrabSelMemP
  rw [toByteArray_write32_size_of_le mem _ p.toNat mem.size (max mem.size (p.toNat + 32)) rfl hpmem
    rfl]
  omega

theorem catBiteGrabIlkMemP_size (p ilk : UInt256) {mem : ByteArray}
    (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨4⟩).toNat + 32 ≤ (catBiteGrabIlkMemP p ilk mem).size := by
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabSelMemP_size p hpmem
  unfold catBiteGrabIlkMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨4⟩).toNat (catBiteGrabSelMemP p mem).size
    (max (catBiteGrabSelMemP p mem).size ((p + ⟨4⟩).toNat + 32)) rfl (by omega) rfl]
  omega

theorem catBiteGrabUrnMemP_size (p ilk urn : UInt256) {mem : ByteArray}
    (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨36⟩).toNat + 32 ≤ (catBiteGrabUrnMemP p ilk urn mem).size := by
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabIlkMemP_size p ilk hpmem hpsz
  unfold catBiteGrabUrnMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨36⟩).toNat (catBiteGrabIlkMemP p ilk mem).size
    (max (catBiteGrabIlkMemP p ilk mem).size ((p + ⟨36⟩).toNat + 32)) rfl (by omega) rfl]
  omega

theorem catBiteGrabThisMemP_size (p ilk urn thisW : UInt256) {mem : ByteArray}
    (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨68⟩).toNat + 32 ≤ (catBiteGrabThisMemP p ilk urn thisW mem).size := by
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabUrnMemP_size p ilk urn hpmem hpsz
  unfold catBiteGrabThisMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨68⟩).toNat (catBiteGrabUrnMemP p ilk urn mem).size
    (max (catBiteGrabUrnMemP p ilk urn mem).size ((p + ⟨68⟩).toNat + 32)) rfl (by omega) rfl]
  omega

theorem catBiteGrabVowMemP_size (p ilk urn thisW vowRaw : UInt256) {mem : ByteArray}
    (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨100⟩).toNat + 32 ≤ (catBiteGrabVowMemP p ilk urn thisW vowRaw mem).size := by
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabThisMemP_size p ilk urn thisW hpmem hpsz
  unfold catBiteGrabVowMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨100⟩).toNat (catBiteGrabThisMemP p ilk urn thisW mem).size
    (max (catBiteGrabThisMemP p ilk urn thisW mem).size ((p + ⟨100⟩).toNat + 32)) rfl (by omega) rfl]
  omega

theorem catBiteGrabDinkMemP_size (p ilk urn thisW vowRaw dink : UInt256) {mem : ByteArray}
    (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨132⟩).toNat + 32 ≤ (catBiteGrabDinkMemP p ilk urn thisW vowRaw dink mem).size := by
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabVowMemP_size p ilk urn thisW vowRaw hpmem hpsz
  unfold catBiteGrabDinkMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨132⟩).toNat
    (catBiteGrabVowMemP p ilk urn thisW vowRaw mem).size
    (max (catBiteGrabVowMemP p ilk urn thisW vowRaw mem).size ((p + ⟨132⟩).toNat + 32)) rfl (by omega)
    rfl]
  omega

theorem catBiteGrabCalldataMemP_size (p ilk urn thisW vowRaw dink dart : UInt256)
    {mem : ByteArray} (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (p + ⟨164⟩).toNat + 32 ≤ (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).size := by
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteGrabDinkMemP_size p ilk urn thisW vowRaw dink hpmem hpsz
  unfold catBiteGrabCalldataMemP
  rw [toByteArray_write32_size_of_le _ _ (p + ⟨164⟩).toNat
    (catBiteGrabDinkMemP p ilk urn thisW vowRaw dink mem).size
    (max (catBiteGrabDinkMemP p ilk urn thisW vowRaw dink mem).size ((p + ⟨164⟩).toNat + 32)) rfl
    (by omega) rfl]
  omega

/-- The free-pointer read at `[64,96)` survives the 7 `grab` calldata writes (all at offsets `≥ p ≥ 96`). -/
theorem catBiteGrabCalldataMemP_read64 (p ilk urn thisW vowRaw dink dart : UInt256)
    {mem : ByteArray} (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hpsz : p.toNat + 196 < UInt256.size) :
    (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding 64 32
      = mem.readWithPadding 64 32 := by
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
  have hsSel := catBiteGrabSelMemP_size p hpmem
  have hsIlk := catBiteGrabIlkMemP_size p ilk hpmem hpsz
  have hsUrn := catBiteGrabUrnMemP_size p ilk urn hpmem hpsz
  have hsThis := catBiteGrabThisMemP_size p ilk urn thisW hpmem hpsz
  have hsVow := catBiteGrabVowMemP_size p ilk urn thisW vowRaw hpmem hpsz
  have hsDink := catBiteGrabDinkMemP_size p ilk urn thisW vowRaw dink hpmem hpsz
  unfold catBiteGrabCalldataMemP
  rw [write32_read_below _ _ (p + ⟨164⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabDinkMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabVowMemP
  rw [write32_read_below _ _ (p + ⟨100⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabThisMemP
  rw [write32_read_below _ _ (p + ⟨68⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabUrnMemP
  rw [write32_read_below _ _ (p + ⟨36⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabIlkMemP
  rw [write32_read_below _ _ (p + ⟨4⟩).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabSelMemP
  rw [write32_read_below _ _ p.toNat 64 (by rw [toByteArray_size]) hpmem (by omega)]

/-! #### `fess` calldata memory (2 words at `p2, p2+4`; selector `0x697efb78`) -/

noncomputable def catBiteFessSelMemP (p2 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1769929592⟩) ⟨224⟩).toByteArray.write 0 mem
    p2.toNat 32

/-- The full 36-byte `fess` calldata laid at the free pointer `p2` over base memory `mem`. -/
noncomputable def catBiteFessCalldataMemP (p2 dartRate : UInt256) (mem : ByteArray) :
    ByteArray :=
  dartRate.toByteArray.write 0 (catBiteFessSelMemP p2 mem) (⟨4⟩ + p2).toNat 32

theorem catBiteFessSelMemP_size (p2 : UInt256) {mem : ByteArray}
    (hpmem : p2.toNat ≤ mem.size) : p2.toNat + 32 ≤ (catBiteFessSelMemP p2 mem).size := by
  unfold catBiteFessSelMemP
  rw [toByteArray_write32_size_of_le mem _ p2.toNat mem.size (max mem.size (p2.toNat + 32)) rfl hpmem
    rfl]
  omega

theorem catBiteFessCalldataMemP_size (p2 dartRate : UInt256) {mem : ByteArray}
    (hpmem : p2.toNat ≤ mem.size) (hpsz : p2.toNat + 36 < UInt256.size) :
    (⟨4⟩ + p2).toNat + 32 ≤ (catBiteFessCalldataMemP p2 dartRate mem).size := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteFessSelMemP_size p2 hpmem
  unfold catBiteFessCalldataMemP
  rw [toByteArray_write32_size_of_le _ _ (⟨4⟩ + p2).toNat (catBiteFessSelMemP p2 mem).size
    (max (catBiteFessSelMemP p2 mem).size ((⟨4⟩ + p2).toNat + 32)) rfl (by omega) rfl]
  omega

/-- The free-pointer read at `[64,96)` survives the 2 `fess` calldata writes (at `p2, p2+4 ≥ 96`). -/
theorem catBiteFessCalldataMemP_read64 (p2 dartRate : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size) (hpsz : p2.toNat + 36 < UInt256.size) :
    (catBiteFessCalldataMemP p2 dartRate mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteFessSelMemP_size p2 hpmem
  unfold catBiteFessCalldataMemP
  rw [write32_read_below _ _ (⟨4⟩ + p2).toNat 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteFessSelMemP
  rw [write32_read_below _ _ p2.toNat 64 (by rw [toByteArray_size]) hpmem (by omega)]

section CalldataBuild
-- Keep `MachineState.M` opaque to `isDefEq`: unfolding its `max`/`Div.div`/`if` on the abstract free
-- pointer makes coercion/unification blow up (50s+ per `M` bound).  We unfold it only via explicit
-- `simp only [MachineState.M]` in the arithmetic side goals.
attribute [local irreducible] MachineState.M

set_option maxHeartbeats 2000000 in
/-- **`grab` calldata build** (`2073 → 2177`): marshal the 6-arg `vat.grab(...)` calldata into the
fresh free pointer `p = mem[0x40]` (7 `MSTORE`s at `p, p+4, …, p+164`; selector `0x7bab3f40`), leaving
the `EXTCODESIZE`/`CALL` frame that `RD.catBiteGrabCallGen` consumes at `2177`.  Because `[p, p+196)`
lies beyond the active-words high-water mark, each `MSTORE` genuinely expands memory (the active-words
are threaded `Cₘ awₖ − Cₘ awₖ₋₁`); `hFree64` pins the free pointer, `hawcov`/`hawsz`/`hpsz` bound it. -/
theorem catBiteTraceGrabBuild {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {q art ink iDust iSpot iRate urn ilk dart dink p : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2073⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hawcov : p.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p.toNat + 256 < UInt256.size)
    (hov : R.length + 22 ≤ 1024) :
    ∃ (awF : UInt256) (k' C' : ℕ), RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2177⟩
      (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        ⟨0⟩ :: p :: ⟨196⟩ :: p :: ⟨0⟩ :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
        UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteGrabCalldataMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩)
        dink dart mem)
      awF o (cA', σ') k' C' := by
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
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
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [h64]; omega)
  -- active-words after the 7 expanding MSTOREs, as opaque `catBiteAwStep` atoms
  have hstep1 : UInt256.ofNat (MachineState.M aw.toNat p.toNat 32) = catBiteAwStep aw p.toNat := by
    simp only [catBiteAwStep]
  have hM7lt : MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 < UInt256.size :=
    catBiteMlt aw (p + ⟨164⟩).toNat (by omega)
  have haw7val :
      (catBiteAwStep aw (p + ⟨164⟩).toNat).toNat = MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 :=
    catBiteAwStep_toNat aw (p + ⟨164⟩).toNat hM7lt
  have haw7ge : 96 ≤ (catBiteAwStep aw (p + ⟨164⟩).toNat).toNat * 32 := by
    rw [haw7val, e164]; simp only [MachineState.M]; omega
  have haw7sz : (catBiteAwStep aw (p + ⟨164⟩).toNat).toNat * 32 < UInt256.size := by
    rw [haw7val, e164]; simp only [MachineState.M]; omega
  have hM7out : UInt256.ofNat
      (MachineState.M (catBiteAwStep aw (p + ⟨164⟩).toNat).toNat (⟨64⟩ : UInt256).toNat 32)
      = catBiteAwStep aw (p + ⟨164⟩).toNat :=
    catBiteAwMInv32 (catBiteAwStep aw (p + ⟨164⟩).toNat) (by rw [h64]; omega)
  have hcol2 := catBiteAwStep_collapse aw p.toNat (p + ⟨4⟩).toNat (by omega)
    (catBiteMlt aw p.toNat (by omega))
  have hcol3 := catBiteAwStep_collapse aw (p + ⟨4⟩).toNat (p + ⟨36⟩).toNat (by omega)
    (catBiteMlt aw (p + ⟨4⟩).toNat (by omega))
  have hcol4 := catBiteAwStep_collapse aw (p + ⟨36⟩).toNat (p + ⟨68⟩).toNat (by omega)
    (catBiteMlt aw (p + ⟨36⟩).toNat (by omega))
  have hcol5 := catBiteAwStep_collapse aw (p + ⟨68⟩).toNat (p + ⟨100⟩).toNat (by omega)
    (catBiteMlt aw (p + ⟨68⟩).toNat (by omega))
  have hcol6 := catBiteAwStep_collapse aw (p + ⟨100⟩).toNat (p + ⟨132⟩).toNat (by omega)
    (catBiteMlt aw (p + ⟨100⟩).toNat (by omega))
  have hcol7 := catBiteAwStep_collapse aw (p + ⟨132⟩).toNat (p + ⟨164⟩).toNat (by omega)
    (catBiteMlt aw (p + ⟨132⟩).toNat (by omega))
  -- 2073 → 2084 : SLOAD vat@3, SLOAD vow@4, read free pointer
  have rd2074 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2076 := rd2074.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2077raw⟩ := rd2076.sload (by native_decide) (by evm_ov)
  have rd2077 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2077⟩
      (solcSlotWord σ' I ⟨3⟩ :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ ::
        urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd2077raw
  have rd2079 := rd2077.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2080d := rd2079.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2081raw⟩ := rd2080d.sload (by native_decide) (by evm_ov)
  have rd2081 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2081⟩
      (solcSlotWord σ' I ⟨4⟩ :: ⟨4⟩ :: solcSlotWord σ' I ⟨3⟩ :: dink :: dart :: q :: art :: ink ::
        iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd2081raw
  have rd2083 := rd2081.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2084d := rd2083.dup1 (by native_decide) (by evm_ov)
  have rd2085 := RD.mload 0 p aw rd2084d (by native_decide) (catBiteMloadCost0 hM64)
    (mloadWordValue_of_readWithPadding (by rw [h64]; omega)
      (by intro hh; have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt hawsz, h64] at hle; omega)
      (by rw [h64]; exact hFree64)) hM64 (by evm_ov)
  -- 2085 → 2094 : build selector, MSTORE #1 @ p
  have rd2090 := rd2085.push4 ⟨32419069⟩ (by native_decide) (by evm_ov)
  have rd2092 := rd2090.push1 ⟨230⟩ (by native_decide) (by evm_ov)
  have rd2093 := rd2092.shl (by native_decide) (by evm_ov)
  have rd2094d := rd2093.dup2 (by native_decide) (by evm_ov)
  have rd2094 := RD.mstore _ (catBiteGrabSelMemP p mem) (catBiteAwStep aw p.toNat) rd2094d
    (by native_decide) catBiteMstoreCostM rfl hstep1 (by evm_ov)
  -- 2095 → 2100 : ilk, MSTORE #2 @ p+4
  have rd2095 := rd2094.swap3 (by native_decide) (by evm_ov)
  have rd2096 := rd2095.dup4 (by native_decide) (by evm_ov)
  have rd2097 := rd2096.add (by native_decide) (by evm_ov)
  have rd2098 := RD.dup16 rd2097 (by native_decide) (by evm_ov)
  have rd2099 := rd2098.swap1 (by native_decide) (by evm_ov)
  have rd2100 := RD.mstore _ (catBiteGrabIlkMemP p ilk mem) (catBiteAwStep aw (p + ⟨4⟩).toNat) rd2099
    (by native_decide) catBiteMstoreCostM rfl hcol2 (by evm_ov)
  -- 2101 → 2116 : masked urn, MSTORE #3 @ p+36
  have rd2101 := rd2100.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2103 := rd2101.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2105 := rd2103.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2107 := rd2105.shl (by native_decide) (by evm_ov)
  have rd2108 := rd2107.sub (by native_decide) (by evm_ov)
  have rd2109 := RD.dup15 rd2108 (by native_decide) (by evm_ov)
  have rd2110 := rd2109.dup2 (by native_decide) (by evm_ov)
  have rd2111 := rd2110.and (by native_decide) (by evm_ov)
  have rd2112 := rd2111.push1 ⟨36⟩ (by native_decide) (by evm_ov)
  have rd2114 := rd2112.dup6 (by native_decide) (by evm_ov)
  have rd2115 := rd2114.add (by native_decide) (by evm_ov)
  have rd2116 := RD.mstore _ (catBiteGrabUrnMemP p ilk urn mem) (catBiteAwStep aw (p + ⟨36⟩).toNat)
    rd2115 (by native_decide) catBiteMstoreCostM rfl hcol3 (by evm_ov)
  -- 2117 → 2122 : address(this), MSTORE #4 @ p+68
  have rd2117 := rd2116.address (by native_decide) (by evm_ov)
  have rd2118 := rd2117.push1 ⟨68⟩ (by native_decide) (by evm_ov)
  have rd2120 := rd2118.dup6 (by native_decide) (by evm_ov)
  have rd2121 := rd2120.add (by native_decide) (by evm_ov)
  have rd2122 := RD.mstore _ (catBiteGrabThisMemP p ilk urn (UInt256.ofNat I.codeOwner.val) mem)
    (catBiteAwStep aw (p + ⟨68⟩).toNat) rd2121 (by native_decide) catBiteMstoreCostM rfl hcol4
    (by evm_ov)
  -- 2123 → 2130 : masked vow, MSTORE #5 @ p+100
  have rd2123 := rd2122.swap2 (by native_decide) (by evm_ov)
  have rd2124 := rd2123.dup3 (by native_decide) (by evm_ov)
  have rd2125 := rd2124.and (by native_decide) (by evm_ov)
  have rd2126 := rd2125.push1 ⟨100⟩ (by native_decide) (by evm_ov)
  have rd2128 := rd2126.dup5 (by native_decide) (by evm_ov)
  have rd2129 := rd2128.add (by native_decide) (by evm_ov)
  have rd2130 := RD.mstore _
    (catBiteGrabVowMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩) mem)
    (catBiteAwStep aw (p + ⟨100⟩).toNat) rd2129 (by native_decide) catBiteMstoreCostM rfl hcol5
    (by evm_ov)
  -- 2131 → 2140 : -int256(dink), MSTORE #6 @ p+132
  have rd2131 := rd2130.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2133 := rd2131.dup6 (by native_decide) (by evm_ov)
  have rd2134 := rd2133.dup2 (by native_decide) (by evm_ov)
  have rd2135 := rd2134.sub (by native_decide) (by evm_ov)
  have rd2136 := rd2135.push1 ⟨132⟩ (by native_decide) (by evm_ov)
  have rd2138 := rd2136.dup6 (by native_decide) (by evm_ov)
  have rd2139 := rd2138.add (by native_decide) (by evm_ov)
  have rd2140 := RD.mstore _
    (catBiteGrabDinkMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩) dink mem)
    (catBiteAwStep aw (p + ⟨132⟩).toNat) rd2139 (by native_decide) catBiteMstoreCostM rfl hcol6
    (by evm_ov)
  -- 2141 → 2148 : -int256(dart), MSTORE #7 @ p+164
  have rd2141 := rd2140.dup7 (by native_decide) (by evm_ov)
  have rd2142 := rd2141.dup2 (by native_decide) (by evm_ov)
  have rd2143 := rd2142.sub (by native_decide) (by evm_ov)
  have rd2144 := rd2143.push1 ⟨164⟩ (by native_decide) (by evm_ov)
  have rd2146 := rd2144.dup6 (by native_decide) (by evm_ov)
  have rd2147 := rd2146.add (by native_decide) (by evm_ov)
  have rd2148 := RD.mstore _
    (catBiteGrabCalldataMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩)
      dink dart mem) (catBiteAwStep aw (p + ⟨164⟩).toNat) rd2147 (by native_decide) catBiteMstoreCostM
    rfl hcol7 (by evm_ov)
  -- 2149 → 2150 : reload the free pointer (survives the writes)
  have rd2149 := rd2148.swap1 (by native_decide) (by evm_ov)
  have rd2150 := RD.mload 0 p (catBiteAwStep aw (p + ⟨164⟩).toNat) rd2149 (by native_decide)
    (catBiteMloadCost0 hM7out)
    (mloadWordValue_of_readWithPadding
      (by rw [h64]
          have hsz := catBiteGrabCalldataMemP_size p ilk urn (UInt256.ofNat I.codeOwner.val)
            (solcSlotWord σ' I ⟨4⟩) dink dart hpmem (by omega)
          omega)
      (by intro hh
          have hle : (catBiteAwStep aw (p + ⟨164⟩).toNat * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt haw7sz, h64] at hle; omega)
      (by rw [h64,
            catBiteGrabCalldataMemP_read64 p ilk urn (UInt256.ofNat I.codeOwner.val)
              (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega)]
          exact hFree64)) hM7out (by evm_ov)
  -- 2151 → 2176 : lay out the CALL frame (`vatMasked`, `196`, `p`, `p+196`, selector)
  have rd2151 := rd2150.swap2 (by native_decide) (by evm_ov)
  have rd2152 := rd2151.swap1 (by native_decide) (by evm_ov)
  have rd2153 := rd2152.swap4 (by native_decide) (by evm_ov)
  have rd2154 := rd2153.and (by native_decide) (by evm_ov)
  have rd2155 := rd2154.swap3 (by native_decide) (by evm_ov)
  have rd2156 := rd2155.push4 ⟨2074820416⟩ (by native_decide) (by evm_ov)
  have rd2161 := rd2156.swap3 (by native_decide) (by evm_ov)
  have rd2162 := rd2161.push1 ⟨196⟩ (by native_decide) (by evm_ov)
  have rd2164 := rd2162.dup1 (by native_decide) (by evm_ov)
  have rd2165 := rd2164.dup3 (by native_decide) (by evm_ov)
  have rd2166 := rd2165.add (by native_decide) (by evm_ov)
  have rd2167 := rd2166.swap4 (by native_decide) (by evm_ov)
  have rd2168 := rd2167.swap2 (by native_decide) (by evm_ov)
  have rd2169 := rd2168.dup3 (by native_decide) (by evm_ov)
  have rd2170 := rd2169.swap1 (by native_decide) (by evm_ov)
  have rd2171 := rd2170.sub (by native_decide) (by evm_ov)
  have hpp : UInt256.sub p p = ⟨0⟩ := by
    apply u256_inj; rw [usub_toNat (le_refl p.toNat)]; simp
  rw [hpp] at rd2171
  have rd2172 := rd2171.add (by native_decide) (by evm_ov)
  rw [show (⟨0⟩ : UInt256) + ⟨196⟩ = ⟨196⟩ from by native_decide] at rd2172
  have rd2173 := rd2172.dup2 (by native_decide) (by evm_ov)
  have rd2174 := rd2173.dup4 (by native_decide) (by evm_ov)
  have rd2175 := rd2174.dup8 (by native_decide) (by evm_ov)
  exact ⟨_, _, _, rd2175.dup1 (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
/-- **`fess` calldata build** (`2242 → 2284`): marshal the 1-arg `vow.fess(dartRate)` calldata into the
fresh free pointer `p2 = mem[0x40]` (2 `MSTORE`s at `p2, p2+4`; selector `0x697efb78`), leaving the
`EXTCODESIZE`/`CALL` frame that `RD.catBiteFessCallGen` consumes at `2284`.  As with `grab`, the writes
lie beyond the active-words high-water mark, so they expand memory (threaded via `catBiteAwStep`). -/
theorem catBiteTraceFessBuild {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {dartRate dink dart q art ink iDust iSpot iRate urn ilk p2 : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2242⟩
      (dartRate :: ⟨1769929592⟩ :: UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p2)
    (hp96 : 96 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hawcov : p2.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p2.toNat + 96 < UInt256.size)
    (hov : R.length + 22 ≤ 1024) :
    ∃ (awF : UInt256) (k' C' : ℕ), RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2284⟩
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        ⟨0⟩ :: p2 :: ⟨36⟩ :: p2 :: ⟨0⟩ :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
        UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteFessCalldataMemP p2 dartRate mem) awF o (cA', σ') k' C' := by
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [h64]; omega)
  have hstepF1 : UInt256.ofNat (MachineState.M aw.toNat p2.toNat 32) = catBiteAwStep aw p2.toNat := by
    simp only [catBiteAwStep]
  have hM2lt : MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 < UInt256.size :=
    catBiteMlt aw (⟨4⟩ + p2).toNat (by omega)
  have hawFval :
      (catBiteAwStep aw (⟨4⟩ + p2).toNat).toNat = MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 :=
    catBiteAwStep_toNat aw (⟨4⟩ + p2).toNat hM2lt
  have hawFge : 96 ≤ (catBiteAwStep aw (⟨4⟩ + p2).toNat).toNat * 32 := by
    rw [hawFval, e4]; simp only [MachineState.M]; omega
  have hawFsz : (catBiteAwStep aw (⟨4⟩ + p2).toNat).toNat * 32 < UInt256.size := by
    rw [hawFval, e4]; simp only [MachineState.M]; omega
  have hMFout : UInt256.ofNat
      (MachineState.M (catBiteAwStep aw (⟨4⟩ + p2).toNat).toNat (⟨64⟩ : UInt256).toNat 32)
      = catBiteAwStep aw (⟨4⟩ + p2).toNat :=
    catBiteAwMInv32 (catBiteAwStep aw (⟨4⟩ + p2).toNat) (by rw [h64]; omega)
  have hcolF2 := catBiteAwStep_collapse aw p2.toNat (⟨4⟩ + p2).toNat (by omega)
    (catBiteMlt aw p2.toNat (by omega))
  have hsub36 : UInt256.sub (⟨32⟩ + (⟨4⟩ + p2)) p2 = ⟨36⟩ := by
    apply u256_inj
    have he : (⟨32⟩ + (⟨4⟩ + p2)).toNat = p2.toNat + 36 := by
      rw [uadd_toNat, e4, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [usub_toNat (by rw [he]; omega), he, show (⟨36⟩ : UInt256).toNat = 36 from by decide]; omega
  -- 2242 → 2245 : read free pointer
  have rd2243 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2245 := rd2243.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2246 := RD.mload 0 p2 aw rd2245 (by native_decide) (catBiteMloadCost0 hM64)
    (mloadWordValue_of_readWithPadding (by rw [h64]; omega)
      (by intro hh; have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt hawsz, h64] at hle; omega)
      (by rw [h64]; exact hFree64)) hM64 (by evm_ov)
  -- 2246 → 2257 : build selector, MSTORE #1 @ p2
  have rd2247 := rd2246.dup3 (by native_decide) (by evm_ov)
  have rd2252 := rd2247.push4 ⟨4294967295⟩ (by native_decide) (by evm_ov)
  have rd2253 := rd2252.and (by native_decide) (by evm_ov)
  have rd2255 := rd2253.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd2256 := rd2255.shl (by native_decide) (by evm_ov)
  have rd2257d := rd2256.dup2 (by native_decide) (by evm_ov)
  have rd2257 := RD.mstore _ (catBiteFessSelMemP p2 mem) (catBiteAwStep aw p2.toNat) rd2257d
    (by native_decide) catBiteMstoreCostM rfl hstepF1 (by evm_ov)
  -- 2258 → 2264 : dartRate, MSTORE #2 @ p2+4
  have rd2258 := rd2257.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2260 := rd2258.add (by native_decide) (by evm_ov)
  have rd2261 := rd2260.dup1 (by native_decide) (by evm_ov)
  have rd2262 := rd2261.dup3 (by native_decide) (by evm_ov)
  have rd2263 := rd2262.dup2 (by native_decide) (by evm_ov)
  have rd2264 := RD.mstore _ (catBiteFessCalldataMemP p2 dartRate mem)
    (catBiteAwStep aw (⟨4⟩ + p2).toNat) rd2263 (by native_decide) catBiteMstoreCostM rfl hcolF2
    (by evm_ov)
  -- 2265 → 2275 : compute fess-end pointer, reload the free pointer
  have rd2265 := rd2264.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2267 := rd2265.add (by native_decide) (by evm_ov)
  have rd2268 := rd2267.swap2 (by native_decide) (by evm_ov)
  have rd2269 := rd2268.pop (by native_decide) (by evm_ov)
  have rd2270 := rd2269.pop (by native_decide) (by evm_ov)
  have rd2271 := rd2270.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2273 := rd2271.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2275 := RD.mload 0 p2 (catBiteAwStep aw (⟨4⟩ + p2).toNat) rd2273 (by native_decide)
    (catBiteMloadCost0 hMFout)
    (mloadWordValue_of_readWithPadding
      (by rw [h64]
          have hsz := catBiteFessCalldataMemP_size p2 dartRate hpmem (by omega)
          omega)
      (by intro hh
          have hle : (catBiteAwStep aw (⟨4⟩ + p2).toNat * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt hawFsz, h64] at hle; omega)
      (by rw [h64, catBiteFessCalldataMemP_read64 p2 dartRate hp96 hpmem (by omega)]
          exact hFree64)) hMFout (by evm_ov)
  -- 2276 → 2283 : lay out the CALL frame (`vowMasked`, `36`, `p2`, `fessEnd`)
  have rd2276 := rd2275.dup1 (by native_decide) (by evm_ov)
  have rd2277 := rd2276.dup4 (by native_decide) (by evm_ov)
  have rd2278 := rd2277.sub (by native_decide) (by evm_ov)
  rw [hsub36] at rd2278
  have rd2279 := rd2278.dup2 (by native_decide) (by evm_ov)
  have rd2280 := rd2279.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2282 := rd2280.dup8 (by native_decide) (by evm_ov)
  exact ⟨_, _, _, rd2282.dup1 (by native_decide) (by evm_ov)⟩

end CalldataBuild

/-- Acc-generic `vat.grab(...)` `EXTCODESIZE` guard + void `CALL` (`@2192`, `perm := I.perm`).  The
`grab` calldata (`inOff`/`inSize = 196`) is already in memory; steps the guard and the `CALL`, landing
at pc `2193` with the status flag, and exposes the `typedCallViaEVM` coupling from the current
post-arithmetic state `{… with accountMap := σx, createdAccounts := cAx}`.  Acc-generic counterpart of
`BiteCallGrab`'s `RD.catBiteGrabCall` (which fixes the acc to the original `(cA, σ)`). -/
theorem RD.catBiteGrabCallGen {cA gh bl σ σ₀ A I} {g : UInt256} {args : List Value}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {target inOff inSize outOff aw : UInt256} {mem rdata : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2177⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: ⟨0⟩ :: R)
      mem aw rdata (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode : config.externalABI.encode? "grab" args =
        some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hov : R.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' mem' : ByteArray) (A' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) mem' aw' o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 target) "grab" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd2193raw, hosz⟩ :=
    RD.call rd2192 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hpc : ((⟨2189⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2193⟩ : UInt256) := by native_decide
  rw [hpc] at rd2193raw
  refine ⟨cA', σ', z, o, _, A', _, k', C', rd2193raw, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm) (targetWord := target)
    (mem := mem) (inOff := inOff) (inSize := inSize)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- Acc-generic `vow.fess(dartRate)` `EXTCODESIZE` guard + void `CALL` (`@2299`, `perm := I.perm`),
landing at pc `2300` with the status flag; exposes the `typedCallViaEVM` coupling.  Acc-generic
counterpart of `BiteCallFess`'s `RD.catBiteFessCall`. -/
theorem RD.catBiteFessCallGen {cA gh bl σ σ₀ A I} {g : UInt256} {args : List Value}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {target inOff inSize outOff outSize aw : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2284⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode : config.externalABI.encode? "fess" args =
        some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hov : R.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' mem' : ByteArray) (A' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) mem' aw' o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 target) "fess" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2299⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd2300, hosz⟩ :=
    RD.call (pc := ⟨2299⟩) rd2299 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, _, A', _, k', C', rd2300, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm) (targetWord := target)
    (mem := mem) (inOff := inOff) (inSize := inSize)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- **Seg 7i** (`2321 → 2383`): the post-`fess` tail — re-derive `dartRate = dart*rate` (`@3720`),
`tabBase = dartRate*milkChop` (`@3720`, `milkChop` re-read from `mem[⟨32⟩+q]`), `tab = tabBase / WAD`
(inline div), `litterNew = litter + tab` (`@3802`), and `SSTORE litter@6 := litterNew`.  Lands at pc
`2383` (feeding the `kick` call) with `tab` on top and slot `6` updated in the account map. -/
theorem catBiteTraceSeg7i {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {q art ink iDust iSpot iRate urn ilk : UInt256}
    {dink dart milkChop dartRate tabBase tab litterNew : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2321⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k C)
    (hChop : (if (⟨32⟩ + q).toNat ≥ mem.size ∨ (⟨32⟩ + q) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨32⟩ + q).toNat 32)))
        = milkChop)
    (haw : q.toNat + 64 ≤ aw.toNat * 32) (hqsz : q.toNat + 64 < UInt256.size)
    (hperm : I.perm = true)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hChopFit : milkChop.toNat * dartRate.toNat < UInt256.size)
    (hLitFit : (solcSlotWord σ' I ⟨6⟩).toNat + tab.toNat < UInt256.size)
    (hDartRate : UInt256.mul dart iRate = dartRate)
    (hTabBase : UInt256.mul dartRate milkChop = tabBase)
    (hTab : UInt256.div tabBase ⟨1000000000000000000⟩ = tab)
    (hLitterNew : solcSlotWord σ' I ⟨6⟩ + tab = litterNew)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', sstoreAccountMap I.codeOwner σ' ⟨6⟩ litterNew) k' C' := by
  have e32q : (⟨32⟩ + q).toNat = q.toNat + 32 := uadd_lit32_toNat q (by omega)
  have hChopAw : UInt256.ofNat (MachineState.M aw.toNat (⟨32⟩ + q).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [e32q]; omega)
  have rd2321 := rd.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2323 := RD.push8 rd2321 ⟨1000000000000000000⟩ (by native_decide) (by evm_ov)
  have rd2332 := rd2323.push2 ⟨2354⟩ (by native_decide) (by evm_ov)
  have rd2335 := rd2332.push2 ⟨2344⟩ (by native_decide) (by evm_ov)
  have rd2338 := rd2335.dup6 (by native_decide) (by evm_ov)
  have rd2339 := rd2338.dup13 (by native_decide) (by evm_ov)
  have rd2340 := rd2339.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720a := rd2340.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2344⟩ := RD.catBiteCheckedMul rd3720a hRateFit (by native_decide) (by evm_ov)
  rw [hDartRate] at rd2344
  have rd2344j := rd2344.jumpdest (by native_decide) (by evm_ov)
  have rd2345 := rd2344j.dup7 (by native_decide) (by evm_ov)
  have rd2346 := rd2345.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2348 := rd2346.add (by native_decide) (by evm_ov)
  have rd2349 := RD.mload 0 milkChop aw rd2348 (by native_decide) (catBiteMloadCost0 hChopAw)
    hChop hChopAw (by evm_ov)
  have rd2350 := rd2349.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720b := rd2350.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2354⟩ := RD.catBiteCheckedMul rd3720b hChopFit (by native_decide) (by evm_ov)
  rw [hTabBase] at rd2354
  have rd2354j := rd2354.jumpdest (by native_decide) (by evm_ov)
  have rd2355 := rd2354j.dup2 (by native_decide) (by evm_ov)
  have rd2356 := rd2355.push2 ⟨2361⟩ (by native_decide) (by evm_ov)
  have rd2361 := rd2356.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)
  have rd2361j := rd2361.jumpdest (by native_decide) (by evm_ov)
  have rd2362 := rd2361j.div (by native_decide) (by evm_ov)
  rw [hTab] at rd2362
  have rd2363 := rd2362.swap1 (by native_decide) (by evm_ov)
  have rd2364 := rd2363.pop (by native_decide) (by evm_ov)
  have rd2365 := rd2364.push2 ⟨2376⟩ (by native_decide) (by evm_ov)
  have rd2368 := rd2365.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2370raw⟩ := rd2368.sload (by native_decide) (by evm_ov)
  have rd2370 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2371⟩
      (solcSlotWord σ' I ⟨6⟩ :: ⟨2376⟩ :: tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot ::
        iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd2370raw
  have rd2371 := rd2370.dup3 (by native_decide) (by evm_ov)
  have rd2372 := rd2371.push2 ⟨3802⟩ (by native_decide) (by evm_ov)
  have rd3802 := rd2372.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2376⟩ := RD.catBiteCheckedAdd rd3802 hLitFit (by native_decide) (by evm_ov)
  rw [hLitterNew] at rd2376
  have rd2376j := rd2376.jumpdest (by native_decide) (by evm_ov)
  have rd2377 := rd2376j.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd2379 := rd2377.dup2 (by native_decide) (by evm_ov)
  have rd2380 := rd2379.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2381⟩ := rd2380.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2381.pop (by native_decide) (by evm_ov)⟩

/-- **Seg 7f** (`2193 → 2242`): the `grab` call-success guard (`catBiteGrabCallSucceeded`, pops
`status` + the return slot `d0`) then `dartRate = dart*rate` (`@3720`), reading `vow@4` and masking it
(`vowMasked`) and pushing the `fess` selector into place.  `d0`/`d1`/`d2` are the dead frame words
(`p+196`/`grabSel`/`vatMasked`) the guard/setup discard. -/
theorem catBiteTraceSeg7f {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status d0 d1 d2 dink dart q art ink iDust iSpot iRate urn ilk dartRate : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
      (status :: d0 :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hDartRate : UInt256.mul dart iRate = dartRate)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2242⟩
      (dartRate :: ⟨1769929592⟩ :: UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cA', σ') k' C' := by
  -- grab success guard (inline): pop status + the return slot d0
  have rd2194 := rd.iszero (by native_decide) (by evm_ov)
  rw [isZero_eq_zero_of_ne hstatus] at rd2194
  have rd2195 := rd2194.dup1 (by native_decide) (by evm_ov)
  have rd2196 := rd2195.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2196
  have rd2199 := rd2196.push2 ⟨2209⟩ (by native_decide) (by evm_ov)
  have rd2209 := rd2199.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2210 := rd2209.jumpdest (by native_decide) (by evm_ov)
  have rd2211 := rd2210.pop (by native_decide) (by evm_ov)
  have rd2212 := rd2211.pop (by native_decide) (by evm_ov)
  have rd2214 := rd2212.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2215raw⟩ := rd2214.sload (by native_decide) (by evm_ov)
  have rd2215 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2215⟩
      (solcSlotWord σ' I ⟨4⟩ :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot ::
        iRate :: ⟨0⟩ :: urn :: ilk :: R) mem aw o (cA', σ') _ _ := rd2215raw
  have rd2217 := rd2215.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2219 := rd2217.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2221 := rd2219.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2222 := rd2221.shl (by native_decide) (by evm_ov)
  have rd2223 := rd2222.sub (by native_decide) (by evm_ov)
  have rd2224 := rd2223.and (by native_decide) (by evm_ov)
  have rd2225 := rd2224.swap2 (by native_decide) (by evm_ov)
  have rd2226 := rd2225.pop (by native_decide) (by evm_ov)
  have rd2231 := rd2226.push4 ⟨1769929592⟩ (by native_decide) (by evm_ov)
  have rd2232 := rd2231.swap1 (by native_decide) (by evm_ov)
  have rd2233 := rd2232.pop (by native_decide) (by evm_ov)
  have rd2236 := rd2233.push2 ⟨2242⟩ (by native_decide) (by evm_ov)
  have rd2237 := rd2236.dup5 (by native_decide) (by evm_ov)
  have rd2238 := RD.dup12 rd2237 (by native_decide) (by evm_ov)
  have rd2241 := rd2238.push2 ⟨3720⟩ (by native_decide) (by evm_ov)
  have rd3720 := rd2241.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2242⟩ := RD.catBiteCheckedMul rd3720 hRateFit (by native_decide) (by evm_ov)
  rw [hDartRate] at rd2242
  exact ⟨_, _, rd2242⟩

/-- **Seg 7h** (`2300 → 2321`): the `fess` call-success guard (status nonzero) followed by the three
`POP`s that discard the dead `fess`-frame words (`fessLen-end`/`fessSel`/`vowMasked` = `f0`/`f1`/`f2`),
leaving the `[dink, dart, …]` tail for the closing arithmetic. -/
theorem catBiteTraceSeg7h {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status f0 f1 f2 dink dart q art ink iDust iSpot iRate urn ilk : UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
      (status :: f0 :: f1 :: f2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: ilk :: R) mem aw o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2321⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o acc k' C' := by
  have rd2301 := rd.iszero (by native_decide) (by evm_ov)
  rw [isZero_eq_zero_of_ne hstatus] at rd2301
  have rd2302 := rd2301.dup1 (by native_decide) (by evm_ov)
  have rd2303 := rd2302.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2303
  have rd2306 := rd2303.push2 ⟨2316⟩ (by native_decide) (by evm_ov)
  have rd2316 := rd2306.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rd2317 := rd2316.jumpdest (by native_decide) (by evm_ov)
  have rd2318 := rd2317.pop (by native_decide) (by evm_ov)
  have rd2319 := rd2318.pop (by native_decide) (by evm_ov)
  have rd2320 := rd2319.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2320.pop (by native_decide) (by evm_ov)⟩


/-! ## Seg 8 : the final `milkFlip.kick(...)` external call + `id` return (`2383 → RETURN`)

From `Seg7i`'s output (pc `2383`) build the `kick(address,address,uint256,uint256,uint256)`
calldata, issue the `perm:=true` `CALL`, decode the returned `id`, emit the `Bite(...)` `LOG3`,
and ABI-encode+`RETURN` the `id` via the shared `@419` encoder — reaching
`RDret … (UInt256.toByteArray id)`, the full success result of `bite`. -/

theorem awInv32 (aw : UInt256) {off : Nat} (h : off + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 32 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem mloadCost0 {aw off : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: t →
      memoryExpansionCost s .MLOAD = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]
  rw [hM]; simp

theorem mstoreCost0 {aw off val : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: val :: t →
      memoryExpansionCost s .MSTORE = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero]
  rw [hM]; simp

theorem log3Cost0 {aw off sz : UInt256} {t : List UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat sz.toNat) = aw) :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: sz :: t →
      memoryExpansionCost s .LOG3 = 0 := by
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, List.getElem!_cons_zero,
    List.getElem!_cons_succ]
  rw [hM]; simp

-- ===== calldata build 2383 -> 2516 =====
set_option maxHeartbeats 40000000 in
theorem catBiteTraceSeg8aCalldata {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {tab dink dart q art ink iDust iSpot iRate urn ilk milkFlip : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cAx, σx) k C)
    (hFlip : (if q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32))) = milkFlip)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩)
    (hawq : q.toNat + 32 ≤ aw.toNat * 32)
    (haw292 : 292 ≤ aw.toNat * 32)
    (hmemsize : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (UInt256.land biteAddrMaskWord milkFlip :: UInt256.land biteAddrMaskWord milkFlip ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨292⟩ :: ⟨891151872⟩ :: UInt256.land biteAddrMaskWord milkFlip ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (kickCalldataMem (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
      aw o (cAx, σx) k' C' := by
  -- aw invariance witnesses
  have hMq : UInt256.ofNat (MachineState.M aw.toNat q.toNat 32) = aw := awInv32 aw hawq
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := awInv32 aw (by omega)
  have hM128 : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw := awInv32 aw (by omega)
  have hM132 : UInt256.ofNat (MachineState.M aw.toNat 132 32) = aw := awInv32 aw (by omega)
  have hM164 : UInt256.ofNat (MachineState.M aw.toNat 164 32) = aw := awInv32 aw (by omega)
  have hM196 : UInt256.ofNat (MachineState.M aw.toNat 196 32) = aw := awInv32 aw (by omega)
  have hM228 : UInt256.ofNat (MachineState.M aw.toNat 228 32) = aw := awInv32 aw (by omega)
  have hM260 : UInt256.ofNat (MachineState.M aw.toNat 260 32) = aw := awInv32 aw (by omega)
  -- offset-literal rewrites
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
  -- 2425 DUP5 (tab), 2426 DUP7 (dink), 2427 PUSH1 0, 2429 PUSH1 64, 2431 MLOAD (freeptr=128)
  have rd2426 := rd2425.dup5 (by native_decide) (by evm_ov)
  have rd2427 := rd2426.dup7 (by native_decide) (by evm_ov)
  have rd2429 := rd2427.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2431 := rd2429.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2432 := RD.mload 0 ⟨128⟩ aw rd2431 (by native_decide) (mloadCost0 hM64) hFree hM64 (by evm_ov)
  -- 2432 DUP7 (sel), 2433 PUSH4 ffffffff, 2438 AND, 2439 PUSH1 224, 2441 SHL, 2442 DUP2, 2443 MSTORE (sel@128)
  have rd2433 := rd2432.dup7 (by native_decide) (by evm_ov)
  have rd2438 := rd2433.push4 ⟨4294967295⟩ (by native_decide) (by evm_ov)
  have rd2439 := rd2438.and (by native_decide) (by evm_ov)
  rw [hsel] at rd2439
  have rd2441 := rd2439.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd2442 := rd2441.shl (by native_decide) (by evm_ov)
  have rd2443 := rd2442.dup2 (by native_decide) (by evm_ov)
  have rd2444 := RD.mstore 0 (kickSelectorMem mem) aw rd2443 (by native_decide) (mstoreCost0 hM128)
    (by rfl) hM128 (by evm_ov)
  -- 2444 PUSH1 4, 2446 ADD (->132), 2447 DUP1, 2448 DUP7 (urn), mask, 2458 DUP2, 2459 MSTORE (urn@132)
  have rd2446 := rd2444.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2447 := rd2446.add (by native_decide) (by evm_ov)
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide] at rd2447
  have rd2448 := rd2447.dup1 (by native_decide) (by evm_ov)
  have rd2449 := rd2448.dup7 (by native_decide) (by evm_ov)
  have rd2451 := rd2449.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2453 := rd2451.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2455 := rd2453.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2456 := rd2455.shl (by native_decide) (by evm_ov)
  have rd2457 := rd2456.sub (by native_decide) (by evm_ov)
  have rd2458 := rd2457.and (by native_decide) (by evm_ov)
  have rd2459 := rd2458.dup2 (by native_decide) (by evm_ov)
  have rd2460 := RD.mstore 0 (UInt256.toByteArray (UInt256.land biteAddrMaskWord urn) |>.write 0
      (kickSelectorMem mem) 132 32) aw rd2459 (by native_decide) (mstoreCost0 hM132) (by rfl) hM132
    (by evm_ov)
  -- 2460 PUSH1 32, 2462 ADD (->164), 2463 DUP6 (vow1), mask again, 2473 DUP2, 2474 MSTORE (vow@164)
  have rd2462 := rd2460.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2463 := rd2462.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ from by native_decide] at rd2463
  have rd2464 := rd2463.dup6 (by native_decide) (by evm_ov)
  have rd2466 := rd2464.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2468 := rd2466.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2470 := rd2468.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2471 := rd2470.shl (by native_decide) (by evm_ov)
  have rd2472 := rd2471.sub (by native_decide) (by evm_ov)
  have rd2473 := rd2472.and (by native_decide) (by evm_ov)
  have rd2474 := rd2473.dup2 (by native_decide) (by evm_ov)
  have rd2475 := RD.mstore 0 (UInt256.toByteArray (UInt256.land biteAddrMaskWord
        (UInt256.land biteAddrMaskWord (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) |>.write 0
      (UInt256.toByteArray (UInt256.land biteAddrMaskWord urn) |>.write 0 (kickSelectorMem mem) 132 32) 164 32)
      aw rd2474 (by native_decide) (mstoreCost0 hM164) (by rfl) hM164 (by evm_ov)
  -- 2475 PUSH1 32, 2477 ADD (->196), 2478 DUP5 (tab), 2479 DUP2, 2480 MSTORE (tab@196)
  have rd2477 := rd2475.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2478 := rd2477.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨164⟩ = ⟨196⟩ from by native_decide] at rd2478
  have rd2479 := rd2478.dup5 (by native_decide) (by evm_ov)
  have rd2480 := rd2479.dup2 (by native_decide) (by evm_ov)
  have rd2481 := RD.mstore 0 _ aw rd2480 (by native_decide) (mstoreCost0 hM196) (by rfl) hM196 (by evm_ov)
  -- 2481 PUSH1 32, 2483 ADD (->228), 2484 DUP4 (dink), 2485 DUP2, 2486 MSTORE (dink@228)
  have rd2483 := rd2481.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2484 := rd2483.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨196⟩ = ⟨228⟩ from by native_decide] at rd2484
  have rd2485 := rd2484.dup4 (by native_decide) (by evm_ov)
  have rd2486 := rd2485.dup2 (by native_decide) (by evm_ov)
  have rd2487 := RD.mstore 0 _ aw rd2486 (by native_decide) (mstoreCost0 hM228) (by rfl) hM228 (by evm_ov)
  -- 2487 PUSH1 32, 2489 ADD (->260), 2490 DUP3 (0), 2491 DUP2, 2492 MSTORE (0@260)
  have rd2489 := rd2487.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2490 := rd2489.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨228⟩ = ⟨260⟩ from by native_decide] at rd2490
  have rd2491 := rd2490.dup3 (by native_decide) (by evm_ov)
  have rd2492 := rd2491.dup2 (by native_decide) (by evm_ov)
  have rd2493 := RD.mstore 0 (kickCalldataMem (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem)
      aw rd2492 (by native_decide) (mstoreCost0 hM260) (by rfl) hM260 (by evm_ov)
  -- 2493 PUSH1 32, 2495 ADD (->292), 2496 SWAP6, 2497..2502 POP x6
  have rd2495 := rd2493.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2496 := rd2495.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨260⟩ = ⟨292⟩ from by native_decide] at rd2496
  have rd2497 := rd2496.swap6 (by native_decide) (by evm_ov)
  have rd2498 := rd2497.pop (by native_decide) (by evm_ov)
  have rd2499 := rd2498.pop (by native_decide) (by evm_ov)
  have rd2500 := rd2499.pop (by native_decide) (by evm_ov)
  have rd2501 := rd2500.pop (by native_decide) (by evm_ov)
  have rd2502 := rd2501.pop (by native_decide) (by evm_ov)
  have rd2503 := rd2502.pop (by native_decide) (by evm_ov)
  -- 2503 PUSH1 32, 2505 PUSH1 64, 2507 MLOAD (freeptr=128), 2508 DUP1, 2509 DUP4, 2510 SUB (->164)
  have rd2505 := rd2503.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2507 := rd2505.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have hcond : ¬((⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) := by
    intro h; rw [if_pos h] at hFree; exact absurd hFree (by decide)
  have hcalldataSize : (kickCalldataMem (UInt256.land biteAddrMaskWord urn)
      (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
        (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).size = mem.size :=
    kickCalldataMem_size _ _ tab dink hmemsize
  have hval2 : (if (⟨64⟩ : UInt256).toNat ≥ (kickCalldataMem (UInt256.land biteAddrMaskWord urn)
        (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
          (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((kickCalldataMem (UInt256.land biteAddrMaskWord urn)
          (UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
            (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))) tab dink mem).readWithPadding 64 32)))
        = ⟨128⟩ := by
    rw [hcalldataSize, if_neg hcond,
      kickCalldataMem_read64 _ _ tab dink hmemsize hread64]
    native_decide
  have rd2508 := RD.mload 0 ⟨128⟩ aw rd2507 (by native_decide) (mloadCost0 hM64) hval2 hM64 (by evm_ov)
  have rd2509 := rd2508.dup1 (by native_decide) (by evm_ov)
  have rd2510 := rd2509.dup4 (by native_decide) (by evm_ov)
  have rd2511 := rd2510.sub (by native_decide) (by evm_ov)
  rw [show UInt256.sub ⟨292⟩ ⟨128⟩ = ⟨164⟩ from by native_decide] at rd2511
  -- 2511 DUP2, 2512 PUSH1 0, 2514 DUP8, 2515 DUP1 -> reach 2516
  have rd2512 := rd2511.dup2 (by native_decide) (by evm_ov)
  have rd2514 := rd2512.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2515 := rd2514.dup8 (by native_decide) (by evm_ov)
  have rd2516 := rd2515.dup1 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2516⟩

-- kick args abbreviation
noncomputable abbrev seg8UrnM (urn : UInt256) : UInt256 := UInt256.land biteAddrMaskWord urn
noncomputable abbrev seg8VowM (σx : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land biteAddrMaskWord (UInt256.land biteAddrMaskWord
    (UInt256.div (solcSlotWord σx I ⟨4⟩) (UInt256.exp ⟨256⟩ ⟨0⟩)))
noncomputable abbrev seg8KickArgs (σx : AccountMap) (I : ExecutionEnv) (urn tab dink : UInt256) : List Value :=
  [.address (AccountAddress.ofNat (seg8UrnM urn).toNat),
   .address (AccountAddress.ofNat (seg8VowM σx I).toNat),
   .int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .int 0]

theorem seg8_maskBound (x : UInt256) : (UInt256.land biteAddrMaskWord x).toNat < EVM.addressModulus := by
  rw [show biteAddrMaskWord = solcAddrMask from by native_decide, u256_land_comm]
  exact solcAddrMask_result_canonical x

set_option maxHeartbeats 40000000 in
theorem catBiteTraceSeg8a {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {tab dink dart q art ink iDust iSpot iRate urn ilk milkFlip : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      mem aw o (cAx, σx) k C)
    (hFlip : (if q.toNat ≥ mem.size ∨ q ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding q.toNat 32))) = milkFlip)
    (hFree : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩)
    (hawq : q.toNat + 32 ≤ aw.toNat * 32)
    (haw292 : 292 ≤ aw.toNat * 32)
    (hmemsize : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx (UInt256.land biteAddrMaskWord milkFlip) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 40 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨292⟩ :: ⟨891151872⟩ :: UInt256.land biteAddrMaskWord milkFlip ::
          tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
        (o'.write 0 (kickCalldataMem (seg8UrnM urn) (seg8VowM σx I) tab dink mem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        aw' o' (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σx, createdAccounts := cAx }
        (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord milkFlip)) "kick" 0
        (seg8KickArgs σx I urn tab dink)
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨_, _, rd2516⟩ := catBiteTraceSeg8aCalldata rd hFlip hFree hawq haw292 hmemsize hread64 (by omega)
  obtain ⟨gasWord, _, _, rd2531⟩ := RD.catBiteKickGuardOk rd2516 hcodeSize
    (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, oo, Ain, callGas, k', C', hΘ, rd2532, hosz⟩ :=
    RD.catBiteKickPostCall rd2531 hdepth (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ'⟩ := hΘ
  have hencode : config.externalABI.encode? "kick" (seg8KickArgs σx I urn tab dink) =
      some ((kickCalldataMem (seg8UrnM urn) (seg8VowM σx I) tab dink mem).readWithPadding 128 164) :=
    kickEncode_eq (seg8UrnM urn) (seg8VowM σx I) tab dink hmemsize (seg8_maskBound urn)
      (seg8_maskBound _)
  refine ⟨cA', σ', z, oo, A', _, k', C', rd2532, ?_, hosz⟩
  refine callCoincides (A_in := Ain) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm) (targetWord := UInt256.land biteAddrMaskWord milkFlip)
    (mem := kickCalldataMem (seg8UrnM urn) (seg8VowM σx I) tab dink mem) (inOff := ⟨128⟩) (inSize := ⟨164⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ'

-- ===== Seg8b part1: 2532 -> 2631 (success guard + id extract + dtab checkedMul) =====
set_option maxHeartbeats 40000000 in
theorem catBiteTraceSeg8b1 {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status target tab dink dart q art ink iDust iSpot iRate id ret urn ilk : UInt256}
    {R3 : List UInt256} {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (status :: ⟨292⟩ :: ⟨891151872⟩ :: target ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk ::
        ⟨419⟩ :: ret :: R3) mem8 aw8 o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoszLt : o.size < UInt256.size)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = ⟨128⟩)
    (hId8 : (if (⟨128⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨128⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 128 32))) = id)
    (haw8ev : 288 ≤ aw8.toNat * 32)
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
  have hM128 : UInt256.ofNat (MachineState.M aw8.toNat 128 32) = aw8 := awInv32 aw8 (by omega)
  obtain ⟨_, _, rd2550⟩ := RD.catBiteKickCallSucceeded rd hstatus (by simp only [List.length_cons]; omega)
  have rd2551 := rd2550.pop (by native_decide) (by evm_ov)
  have rd2552 := rd2551.pop (by native_decide) (by evm_ov)
  have rd2553 := rd2552.pop (by native_decide) (by evm_ov)
  have rd2555 := rd2553.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2556 := RD.mload 0 ⟨128⟩ aw8 rd2555 (by native_decide) (mloadCost0 hM64) hFree8 hM64 (by evm_ov)
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
  have rd2573 := RD.mload 0 id aw8 rd2572 (by native_decide) (mloadCost0 hM128) hId8 hM128 (by evm_ov)
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

-- event memory (5 writes at 128,160,192,224,256) read-below-64 + size helpers
theorem seg8_wsize (base : ByteArray) (w : UInt256) (off : Nat)
    (h : off + 32 ≤ base.size) : ((UInt256.toByteArray w).write 0 base off 32).size = base.size := by
  rw [toByteArray_write32_size_of_le base w off base.size base.size rfl (by omega) (by omega)]

theorem seg8_wread64 (base : ByteArray) (w : UInt256) (off : Nat)
    (hoff : 96 ≤ off) (h : off + 32 ≤ base.size) :
    ((UInt256.toByteArray w).write 0 base off 32).readWithPadding 64 32 = base.readWithPadding 64 32 :=
  write32_read_below_len (UInt256.toByteArray w) base off 64 32 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem seg8_evMemRead64 (base : ByteArray) (v1 v2 v3 v4 v5 : UInt256)
    (hsz : 288 ≤ base.size) :
    ((UInt256.toByteArray v5).write 0 ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32) 224 32) 256 32).readWithPadding 64 32
      = base.readWithPadding 64 32 := by
  have s1 : ((UInt256.toByteArray v1).write 0 base 128 32).size = base.size := seg8_wsize base v1 128 (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32).size = base.size := by
    rw [seg8_wsize _ v2 160 (by omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32).size = base.size := by
    rw [seg8_wsize _ v3 192 (by omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32) 224 32).size = base.size := by
    rw [seg8_wsize _ v4 224 (by omega)]; exact s3
  rw [seg8_wread64 _ v5 256 (by omega) (by omega), seg8_wread64 _ v4 224 (by omega) (by omega),
    seg8_wread64 _ v3 192 (by omega) (by omega), seg8_wread64 _ v2 160 (by omega) (by omega),
    seg8_wread64 _ v1 128 (by omega) (by omega)]

-- general active-words invariance (arbitrary length)
theorem awInv160 (aw : UInt256) {off : Nat} (h : off + 160 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 160) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 160 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem seg8_evMemSize (base : ByteArray) (v1 v2 v3 v4 v5 : UInt256) (hsz : 288 ≤ base.size) :
    ((UInt256.toByteArray v5).write 0 ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32) 224 32) 256 32).size = base.size := by
  have s1 := seg8_wsize base v1 128 (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32).size = base.size := by
    rw [seg8_wsize _ v2 160 (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32).size = base.size := by
    rw [seg8_wsize _ v3 192 (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192 32) 224 32).size = base.size := by
    rw [seg8_wsize _ v4 224 (by rw [s3]; omega)]; exact s3
  rw [seg8_wsize _ v5 256 (by rw [s4]; omega)]; exact s4

-- ===== Seg8b part2: 2631 -> RETURN (event LOG3 + @419 uint256 return encoder) =====
set_option maxHeartbeats 40000000 in
theorem catBiteTraceSeg8b2 {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {dart dink q art ink iDust iSpot iRate id ret urn ilk flip2 : UInt256}
    {R3 : List UInt256} {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2631⟩
      (UInt256.mul dart iRate :: dart :: dink ::
        ⟨75576624561978822343662660390461596253028794313781746339941468162579799588392⟩ ::
        ilk :: UInt256.land urn biteAddrMaskWord ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: id :: urn :: ilk ::
        ⟨419⟩ :: ret :: R3) mem8 aw8 o acc k C)
    (hperm : I.perm = true)
    (hmem8size : 288 ≤ mem8.size)
    (haw8q : q.toNat + 32 ≤ aw8.toNat * 32)
    (haw8ev : 288 ≤ aw8.toNat * 32)
    (hFlipEv : (if q.toNat ≥ mem8.size ∨ q ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding q.toNat 32))) = flip2)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = ⟨128⟩)
    (hov : R3.length + 30 ≤ 1024) :
    RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id) := by
  have hMq : UInt256.ofNat (MachineState.M aw8.toNat q.toNat 32) = aw8 := awInv32 aw8 haw8q
  have hM64 : UInt256.ofNat (MachineState.M aw8.toNat 64 32) = aw8 := awInv32 aw8 (by omega)
  have hM128 : UInt256.ofNat (MachineState.M aw8.toNat 128 32) = aw8 := awInv32 aw8 (by omega)
  have hM160 : UInt256.ofNat (MachineState.M aw8.toNat 160 32) = aw8 := awInv32 aw8 (by omega)
  have hM192 : UInt256.ofNat (MachineState.M aw8.toNat 192 32) = aw8 := awInv32 aw8 (by omega)
  have hM224 : UInt256.ofNat (MachineState.M aw8.toNat 224 32) = aw8 := awInv32 aw8 (by omega)
  have hM256 : UInt256.ofNat (MachineState.M aw8.toNat 256 32) = aw8 := awInv32 aw8 (by omega)
  have hMlog : UInt256.ofNat (MachineState.M aw8.toNat 128 160) = aw8 := awInv160 aw8 (by omega)
  -- 2631 JUMPDEST, then event data build: dink@128, dart@160, dtab@192, flip@224, id@256
  have rdJD := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2632 := rdJD.dup9 (by native_decide) (by evm_ov)
  have rd2633 := RD.mload 0 flip2 aw8 rd2632 (by native_decide) (mloadCost0 hMq) hFlipEv hMq (by evm_ov)
  have rd2634 := rd2633.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2636 := rd2634.dup1 (by native_decide) (by evm_ov)
  have rd2637 := RD.mload 0 ⟨128⟩ aw8 rd2636 (by native_decide) (mloadCost0 hM64) hFree8 hM64 (by evm_ov)
  have rd2638 := rd2637.swap5 (by native_decide) (by evm_ov)
  have rd2639 := rd2638.dup6 (by native_decide) (by evm_ov)
  have rd2640 := RD.mstore 0 _ aw8 rd2639 (by native_decide) (mstoreCost0 hM128) (by rfl) hM128 (by evm_ov)
  have rd2641 := rd2640.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2643 := rd2641.dup6 (by native_decide) (by evm_ov)
  have rd2644 := rd2643.add (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ from by native_decide] at rd2644
  have rd2645 := rd2644.swap4 (by native_decide) (by evm_ov)
  have rd2646 := rd2645.swap1 (by native_decide) (by evm_ov)
  have rd2647 := rd2646.swap4 (by native_decide) (by evm_ov)
  have rd2648 := RD.mstore 0 _ aw8 rd2647 (by native_decide) (mstoreCost0 hM160) (by rfl) hM160 (by evm_ov)
  have rd2649 := rd2648.dup4 (by native_decide) (by evm_ov)
  have rd2650 := rd2649.dup4 (by native_decide) (by evm_ov)
  have rd2651 := rd2650.add (by native_decide) (by evm_ov)
  rw [show (⟨64⟩ : UInt256) + ⟨128⟩ = ⟨192⟩ from by native_decide] at rd2651
  have rd2652 := rd2651.swap2 (by native_decide) (by evm_ov)
  have rd2653 := rd2652.swap1 (by native_decide) (by evm_ov)
  have rd2654 := rd2653.swap2 (by native_decide) (by evm_ov)
  have rd2655 := RD.mstore 0 _ aw8 rd2654 (by native_decide) (mstoreCost0 hM192) (by rfl) hM192 (by evm_ov)
  have rd2656 := rd2655.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2658 := rd2656.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2660 := rd2658.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2662 := rd2660.shl (by native_decide) (by evm_ov)
  have rd2663 := rd2662.sub (by native_decide) (by evm_ov)
  have rd2664 := rd2663.and (by native_decide) (by evm_ov)
  have rd2665 := rd2664.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd2667 := rd2665.dup4 (by native_decide) (by evm_ov)
  have rd2668 := rd2667.add (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ from by native_decide] at rd2668
  have rd2669 := RD.mstore 0 _ aw8 rd2668 (by native_decide) (mstoreCost0 hM224) (by rfl) hM224 (by evm_ov)
  have rd2670 := rd2669.push1 ⟨128⟩ (by native_decide) (by evm_ov)
  have rd2672 := rd2670.dup3 (by native_decide) (by evm_ov)
  have rd2673 := rd2672.add (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ from by native_decide] at rd2673
  have rd2674 := rd2673.dup15 (by native_decide) (by evm_ov)
  have rd2675 := rd2674.swap1 (by native_decide) (by evm_ov)
  have rd2676 := RD.mstore 0 _ aw8 rd2675 (by native_decide) (mstoreCost0 hM256) (by rfl) hM256 (by evm_ov)
  -- free-ptr read from event memory (= 128), then LOG3
  have hcond : ¬((⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩) := by
    intro h; rw [if_pos h] at hFree8; exact absurd hFree8 (by decide)
  have hevRead : (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)).readWithPadding 64 32
      = mem8.readWithPadding 64 32 :=
    seg8_evMemRead64 mem8 dink dart (UInt256.mul dart iRate) (UInt256.land biteAddrMaskWord flip2) id hmem8size
  have hevSize : (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)).size = mem8.size :=
    seg8_evMemSize mem8 dink dart (UInt256.mul dart iRate) (UInt256.land biteAddrMaskWord flip2) id hmem8size
  have hFreeEv : (if (⟨64⟩ : UInt256).toNat ≥ (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian ((((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)).readWithPadding 64 32))) = ⟨128⟩ := by
    have h8 := hFree8; rw [if_neg hcond] at h8
    rw [hevSize, if_neg hcond, hevRead]; exact h8
  have rd2677 := RD.mload 0 ⟨128⟩ aw8 rd2676 (by native_decide) (mloadCost0 hM64) hFreeEv hM64 (by evm_ov)
  have rd2678 := rd2677.swap1 (by native_decide) (by evm_ov)
  have rd2679 := rd2678.dup2 (by native_decide) (by evm_ov)
  have rd2680 := rd2679.swap1 (by native_decide) (by evm_ov)
  have rd2681 := rd2680.sub (by native_decide) (by evm_ov)
  rw [show UInt256.sub ⟨128⟩ ⟨128⟩ = ⟨0⟩ from by native_decide] at rd2681
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
  -- @419 uint256 return encoder: mstore id@128 ; return [128,160)
  have rd420 := rd419.jumpdest (by native_decide) (by evm_ov)
  have rd422 := rd420.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd423 := rd422.dup1 (by native_decide) (by evm_ov)
  have rd424 := RD.mload 0 ⟨128⟩ aw8 rd423 (by native_decide) (mloadCost0 hM64) hFreeEv hM64 (by evm_ov)
  have rd425 := rd424.swap2 (by native_decide) (by evm_ov)
  have rd426 := rd425.dup3 (by native_decide) (by evm_ov)
  have rd427 := RD.mstore 0 _ aw8 rd426 (by native_decide) (mstoreCost0 hM128) (by rfl) hM128 (by evm_ov)
  -- second free-ptr read (m2[64] = 128, below the id@128 write)
  have hm2read : ((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)) 128 32).readWithPadding 64 32
      = mem8.readWithPadding 64 32 := by
    rw [seg8_wread64 _ id 128 (by omega) (by rw [hevSize]; omega), hevRead]
  have hFreeM2 : (if (⟨64⟩ : UInt256).toNat ≥ ((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)) 128 32).readWithPadding 64 32))) = ⟨128⟩ := by
    have h8 := hFree8; rw [if_neg hcond] at h8
    rw [seg8_wsize _ id 128 (by rw [hevSize]; omega), hevSize, if_neg hcond, hm2read]; exact h8
  have rd428 := RD.mload 0 ⟨128⟩ aw8 rd427 (by native_decide) (mloadCost0 hM64) hFreeM2 hM64 (by evm_ov)
  have rd429 := rd428.swap1 (by native_decide) (by evm_ov)
  have rd430 := rd429.dup2 (by native_decide) (by evm_ov)
  have rd431 := rd430.swap1 (by native_decide) (by evm_ov)
  have rd432 := rd431.sub (by native_decide) (by evm_ov)
  rw [show UInt256.sub ⟨128⟩ ⟨128⟩ = ⟨0⟩ from by native_decide] at rd432
  have rd434 := rd432.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd435 := rd434.add (by native_decide) (by evm_ov)
  rw [show (⟨32⟩ : UInt256) + ⟨0⟩ = ⟨32⟩ from by native_decide] at rd435
  have rd436 := rd435.swap1 (by native_decide) (by evm_ov)
  -- RETURN mem[128..160) = toByteArray id
  have hret : ((UInt256.toByteArray id).write 0 (((UInt256.toByteArray id).write 0 ((UInt256.toByteArray (UInt256.land biteAddrMaskWord flip2)).write 0
      ((UInt256.toByteArray (UInt256.mul dart iRate)).write 0 ((UInt256.toByteArray dart).write 0
        ((UInt256.toByteArray dink).write 0 mem8 128 32) 160 32) 192 32) 224 32) 256 32)) 128 32).readWithPadding 128 32
      = UInt256.toByteArray id :=
    toByteArray_write32_read_back _ id 128 (by rw [hevSize]; omega)
  exact RD.ret 0 (UInt256.toByteArray id) rd436 (by native_decide)
    (fun s haw hstk => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, List.getElem!_cons_zero,
        List.getElem!_cons_succ]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        hM128]; simp)
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, show (⟨32⟩ : UInt256).toNat = 32 from by decide]; exact hret)
    (by evm_ov)


end Benchmarks.Dss.Cat
