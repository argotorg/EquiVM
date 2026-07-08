import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteBodyMem

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — concrete-memory grab/fess/kick reach path (`catBiteBody` support)

The frozen `catBiteReach{Grab,Fess}Region` wrappers abstract their post-call memory (`∃ mem'`), so a
carried memory word (the `milk.chop` field re-read at pc 2349, `catBiteReach2300to2383`'s `hChop`)
cannot be threaded through them.  This file builds the *concrete*-memory grab/fess reach (the void
`CALL`s have `outSize = 0`, so `RD.call`'s return copy is a no-op and the pre-call calldata memory
survives verbatim) plus the "read below the free pointer `p`" seams that recover `milk.chop` from the
`grab`/`fess` calldata overlay (`chop@(q+32) = 256 < p = q+96 = 320`). -/

/-! ## Read-below-`p` seams: `grab`/`fess` calldata writes at `[p, …)` preserve reads at `off + 32 ≤ p` -/

/-- The 7 `grab` calldata writes (at `p, p+4, …, p+164`) leave any word strictly below `p` unchanged
(generic-offset clone of `catBiteGrabCalldataMemP_read64`). -/
theorem catBiteGrabCalldataMemP_readBelow (p ilk urn thisW vowRaw dink dart : UInt256)
    {mem : ByteArray} (off : ℕ) (hoff : off + 32 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hpsz : p.toNat + 196 < UInt256.size) :
    (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding off 32
      = mem.readWithPadding off 32 := by
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
  rw [write32_read_below _ _ (p + ⟨164⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabDinkMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabVowMemP
  rw [write32_read_below _ _ (p + ⟨100⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabThisMemP
  rw [write32_read_below _ _ (p + ⟨68⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabUrnMemP
  rw [write32_read_below _ _ (p + ⟨36⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabIlkMemP
  rw [write32_read_below _ _ (p + ⟨4⟩).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteGrabSelMemP
  rw [write32_read_below _ _ p.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

/-- The 2 `fess` calldata writes (at `p2, p2+4`) leave any word strictly below `p2` unchanged
(generic-offset clone of `catBiteFessCalldataMemP_read64`). -/
theorem catBiteFessCalldataMemP_readBelow (p2 dartRate : UInt256) {mem : ByteArray}
    (off : ℕ) (hoff : off + 32 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hpsz : p2.toNat + 36 < UInt256.size) :
    (catBiteFessCalldataMemP p2 dartRate mem).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hs := catBiteFessSelMemP_size p2 hpmem
  unfold catBiteFessCalldataMemP
  rw [write32_read_below _ _ (⟨4⟩ + p2).toNat off (by rw [toByteArray_size]) (by omega) (by omega)]
  unfold catBiteFessSelMemP
  rw [write32_read_below _ _ p2.toNat off (by rw [toByteArray_size]) hpmem (by omega)]

/-! ## Concrete-memory `grab`/`fess` reach regions

The frozen `catBiteReach{Grab,Fess}Region` abstract the post-`CALL` memory as `∃ mem'`.  Both calls are
VOID (`outSize = ⟨0⟩`), so `RD.call`'s return copy `o.write 0 mem outOff (min ⟨0⟩ …).toNat` is a no-op
(`min ⟨0⟩ x = ⟨0⟩`, `.toNat = 0`, `o.write 0 base off 0 = base`), and the pre-call calldata memory
survives verbatim.  These variants EXPOSE that concrete memory. -/

/-- `2073` → `2193`, exposing the concrete `grab` calldata memory (`catBiteGrabCalldataMemP`). -/
theorem catBiteReachGrabRegionC {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {dink dart q art ink iDust iSpot iRate urn p : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2073⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p)
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size)
    (hawcov : p.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p.toNat + 256 < UInt256.size)
    (hthisCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus)
    (hdink : dink.toNat ≤ 2 ^ 255) (hdart : dart.toNat ≤ 2 ^ 255)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ'
      (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
          UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
          (solcSlotWord σ' I ⟨4⟩) dink dart mem)
        aw' o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord))
        "grab" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
         .address (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat),
         .address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
         .address (AccountAddress.ofNat
           (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)).toNat),
         .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨awF, _, _, rd2177⟩ :=
    catBiteTraceGrabBuild rd hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteGrabEncode_eq p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
    (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega) hthisCanon hdink hdart
  obtain ⟨gasWord, _, _, rd2192⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, o', A_in, callGas, k', C', hΘpack, rd2193raw, hosz⟩ :=
    RD.call rd2192 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hpc : ((⟨2189⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨2193⟩ : UInt256) := by native_decide
  rw [hpc] at rd2193raw
  have hz : (min (⟨0⟩ : UInt256) (UInt256.ofNat o'.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o'.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o'.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hz, byteArray_write_len_zero] at rd2193raw
  refine ⟨cA'', σ'', z, o', A', _, k', C', rd2193raw, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord)
    (mem := catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
      (solcSlotWord σ' I ⟨4⟩) dink dart mem)
    (inOff := p) (inSize := ⟨196⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- `2193` → `2300`, exposing the concrete `fess` calldata memory (`catBiteFessCalldataMemP`).  The
guard/rate-recompute (`catBiteTraceSeg7f`) passes `mem` through, then `catBiteTraceFessBuild` writes
the `vow.fess(dartRate)` calldata into `mem`, and the void `CALL` preserves it. -/
theorem catBiteReachFessRegionC {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status d0 d1 d2 dink dart q art ink iDust iSpot iRate urn dartRate p2 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
      (status :: d0 :: d1 :: d2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hDartRate : UInt256.mul dart iRate = dartRate)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray p2)
    (hp96 : 96 ≤ p2.toNat) (hpmem : p2.toNat ≤ mem.size)
    (hawcov : p2.toNat ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hpsz : p2.toNat + 96 < UInt256.size)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ'
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
          UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteFessCalldataMemP p2 dartRate mem)
        aw' o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)))
        "fess" 0 [.int (Int.ofNat dartRate.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  obtain ⟨_, _, rd2242⟩ := catBiteTraceSeg7f rd hstatus hRateFit hDartRate (by simp)
  obtain ⟨awF, _, _, rd2284⟩ :=
    catBiteTraceFessBuild rd2242 hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteFessEncode_eq p2 dartRate hpmem (by omega)
  obtain ⟨gasWord, _, _, rd2299⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd2284 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, o', A_in, callGas, k', C', hΘpack, rd2300, hosz⟩ :=
    RD.call (pc := ⟨2299⟩) rd2299 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hz : (min (⟨0⟩ : UInt256) (UInt256.ofNat o'.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o'.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o'.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hz, byteArray_write_len_zero] at rd2300
  refine ⟨cA'', σ'', z, o', A', _, k', C', rd2300, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩))
    (mem := catBiteFessCalldataMemP p2 dartRate mem) (inOff := p2) (inSize := ⟨36⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-! ## `p`-parametric `kick` calldata memory (free pointer `p` abstract, not hardcoded `128`)

Generic-offset clones of the frozen `kickSelectorMem`/`kickCalldataMem` couplings
(`BiteCallKick.lean`): the `milkFlip.kick(urn, vow, tab, dink, 0)` scratch layout laid at an
abstract free pointer `p` instead of the concrete `128`.  Selector at `p`, the five argument words
at `p+4, p+36, p+68, p+100, p+132`; the 164-byte calldata slice reads back at `[p, p+164)`. -/

/-- Selector word `0x351de600` written at the abstract scratch offset `p`. -/
noncomputable def kickSelectorMemP (p : UInt256) (mem : ByteArray) : ByteArray :=
  kickSelectorShifted.toByteArray.write 0 mem p.toNat 32

/-- The full 164-byte `kick` calldata laid at the free pointer `p` over base memory `mem`. -/
noncomputable def kickCalldataMemP (p urn vow tab dink : UInt256) (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (dink.toByteArray.write 0
      (tab.toByteArray.write 0
        (vow.toByteArray.write 0
          (urn.toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32)
          (p + ⟨36⟩).toNat 32)
        (p + ⟨68⟩).toNat 32)
      (p + ⟨100⟩).toNat 32)
    (p + ⟨132⟩).toNat 32

theorem kickSelectorMemP_size (p : UInt256) {mem : ByteArray}
    (hpmem : p.toNat + 164 ≤ mem.size) :
    (kickSelectorMemP p mem).size = mem.size := by
  unfold kickSelectorMemP
  exact toByteArray_write32_size_of_le mem kickSelectorShifted p.toNat mem.size mem.size rfl
    (by omega) (by omega)

theorem kickCalldataMemP_size_aux1 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (urn.toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32).size = mem.size := by
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h0 := kickSelectorMemP_size p hpmem
  rw [e4]
  exact toByteArray_write32_size_of_le _ urn (p.toNat + 4) mem.size mem.size h0
    (by rw [h0]; omega) (by omega)

theorem kickCalldataMemP_size_aux2 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (vow.toByteArray.write 0 (urn.toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32)
      (p + ⟨36⟩).toNat 32).size = mem.size := by
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have s1 := kickCalldataMemP_size_aux1 p urn vow tab dink hp96 hpmem hpsz
  rw [e36]
  exact toByteArray_write32_size_of_le _ vow (p.toNat + 36) mem.size mem.size s1
    (by rw [s1]; omega) (by omega)

theorem kickCalldataMemP_size_aux3 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32) (p + ⟨36⟩).toNat 32)
      (p + ⟨68⟩).toNat 32).size = mem.size := by
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have s2 := kickCalldataMemP_size_aux2 p urn vow tab dink hp96 hpmem hpsz
  rw [e68]
  exact toByteArray_write32_size_of_le _ tab (p.toNat + 68) mem.size mem.size s2
    (by rw [s2]; omega) (by omega)

theorem kickCalldataMemP_size_aux4 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (dink.toByteArray.write 0 (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMemP p mem) (p + ⟨4⟩).toNat 32) (p + ⟨36⟩).toNat 32)
      (p + ⟨68⟩).toNat 32) (p + ⟨100⟩).toNat 32).size = mem.size := by
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have s3 := kickCalldataMemP_size_aux3 p urn vow tab dink hp96 hpmem hpsz
  rw [e100]
  exact toByteArray_write32_size_of_le _ dink (p.toNat + 100) mem.size mem.size s3
    (by rw [s3]; omega) (by omega)

theorem kickCalldataMemP_size (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (kickCalldataMemP p urn vow tab dink mem).size = mem.size := by
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have s4 := kickCalldataMemP_size_aux4 p urn vow tab dink hp96 hpmem hpsz
  unfold kickCalldataMemP
  rw [e132]
  exact toByteArray_write32_size_of_le _ ⟨0⟩ (p.toNat + 132) mem.size mem.size s4
    (by rw [s4]; omega) (by omega)

/-- The free-pointer word read `@64` survives the selector write (`96 ≤ p`). -/
theorem kickSelectorMemP_read64 (p : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size)
    (hpval : mem.readWithPadding 64 32 = UInt256.toByteArray p) :
    (kickSelectorMemP p mem).readWithPadding 64 32 = UInt256.toByteArray p := by
  unfold kickSelectorMemP
  rw [write32_read_below _ _ p.toNat 64 (by rw [toByteArray_size]) (by omega) (by omega), hpval]

theorem kickCalldataMemP_read64 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size)
    (hpval : mem.readWithPadding 64 32 = UInt256.toByteArray p) :
    (kickCalldataMemP p urn vow tab dink mem).readWithPadding 64 32 = UInt256.toByteArray p := by
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
  have h0 := kickSelectorMemP_size p hpmem
  have s1 := kickCalldataMemP_size_aux1 p urn vow tab dink hp96 hpmem hpsz
  have s2 := kickCalldataMemP_size_aux2 p urn vow tab dink hp96 hpmem hpsz
  have s3 := kickCalldataMemP_size_aux3 p urn vow tab dink hp96 hpmem hpsz
  have s4 := kickCalldataMemP_size_aux4 p urn vow tab dink hp96 hpmem hpsz
  have h0r := kickSelectorMemP_read64 p hp96 hpmem hpsz hpval
  unfold kickCalldataMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [s4]; omega) (by omega),
    write32_read_below _ _ (p + ⟨100⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [s3]; omega) (by omega),
    write32_read_below _ _ (p + ⟨68⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [s2]; omega) (by omega),
    write32_read_below _ _ (p + ⟨36⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [s1]; omega) (by omega),
    write32_read_below _ _ (p + ⟨4⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [h0]; omega) (by omega),
    h0r]

/-- The `kick` selector word occupies the first four bytes at the scratch offset `p`. -/
theorem kickSelectorMemP_selector (p : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (kickSelectorMemP p mem).extract p.toNat (p.toNat + 4) = kickerKickSelector := by
  have hread : (kickSelectorMemP p mem).readWithPadding p.toNat 4 = kickerKickSelector := by
    unfold kickSelectorMemP
    rw [write32_read_prefix_len _ _ p.toNat 4 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega) (by norm_num)]
    unfold kickSelectorShifted kickerKickSelector selectorBytes
    native_decide
  rw [readWithPadding_eq_extract' _ p.toNat 4 (by norm_num) (by norm_num)
      (by rw [kickSelectorMemP_size p hpmem]; omega)] at hread
  simpa using hread

theorem kickCalldataMemP_read128_164 (p urn vow tab dink : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size) (hpsz : p.toNat + 164 < UInt256.size) :
    (kickCalldataMemP p urn vow tab dink mem).readWithPadding p.toNat 164 =
      kickerKickSelector ++ urn.toByteArray ++ vow.toByteArray ++ tab.toByteArray ++
        dink.toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
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
  have h0 := kickSelectorMemP_size p hpmem
  have s1 := kickCalldataMemP_size_aux1 p urn vow tab dink hp96 hpmem hpsz
  have s2 := kickCalldataMemP_size_aux2 p urn vow tab dink hp96 hpmem hpsz
  have s3 := kickCalldataMemP_size_aux3 p urn vow tab dink hp96 hpmem hpsz
  have s4 := kickCalldataMemP_size_aux4 p urn vow tab dink hp96 hpmem hpsz
  set final := kickCalldataMemP p urn vow tab dink mem with hfinal
  have hfinalSize : p.toNat + 164 ≤ final.size := by
    have hcall := kickCalldataMemP_size p urn vow tab dink hp96 hpmem hpsz
    rw [hfinal]; omega
  -- selector [p, p+4)
  have hSel : final.readWithPadding p.toNat 4 = kickerKickSelector := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat p.toNat 4 (by rw [toByteArray_size])
        (by rw [s4]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨100⟩).toNat p.toNat 4 (by rw [toByteArray_size])
        (by rw [s3]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨68⟩).toNat p.toNat 4 (by rw [toByteArray_size])
        (by rw [s2]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨36⟩).toNat p.toNat 4 (by rw [toByteArray_size])
        (by rw [s1]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨4⟩).toNat p.toNat 4 (by rw [toByteArray_size])
        (by rw [h0]; omega) (by omega) (by omega) (by omega) (by norm_num)]
    have hsel := kickSelectorMemP_selector p hp96 hpmem hpsz
    rw [readWithPadding_eq_extract' _ p.toNat 4 (by norm_num) (by norm_num)
      (by rw [kickSelectorMemP_size p hpmem]; omega)]
    simpa using hsel
  -- urn [p+4, p+36)
  have hUrn : final.readWithPadding (p.toNat + 4) 32 = urn.toByteArray := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
        (by rw [s4]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
        (by rw [s3]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨68⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
        (by rw [s2]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨36⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
        (by rw [s1]; omega) (by omega) (by omega) (by omega) (by norm_num),
      e4, toByteArray_write32_read_back _ urn (p.toNat + 4) (by omega)]
  -- vow [p+36, p+68)
  have hVow : final.readWithPadding (p.toNat + 36) 32 = vow.toByteArray := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
        (by rw [s4]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
        (by rw [s3]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨68⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
        (by rw [s2]; omega) (by omega) (by omega) (by omega) (by norm_num),
      e36, toByteArray_write32_read_back _ vow (p.toNat + 36) (by omega)]
  -- tab [p+68, p+100)
  have hTab : final.readWithPadding (p.toNat + 68) 32 = tab.toByteArray := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 68) 32 (by rw [toByteArray_size])
        (by rw [s4]; omega) (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 68) 32 (by rw [toByteArray_size])
        (by rw [s3]; omega) (by omega) (by omega) (by omega) (by norm_num),
      e68, toByteArray_write32_read_back _ tab (p.toNat + 68) (by omega)]
  -- dink [p+100, p+132)
  have hDink : final.readWithPadding (p.toNat + 100) 32 = dink.toByteArray := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 100) 32 (by rw [toByteArray_size])
        (by rw [s4]; omega) (by omega) (by omega) (by omega) (by norm_num),
      e100, toByteArray_write32_read_back _ dink (p.toNat + 100) (by omega)]
  -- 0 [p+132, p+164)
  have hZero : final.readWithPadding (p.toNat + 132) 32 = (⟨0⟩ : UInt256).toByteArray := by
    rw [hfinal]
    unfold kickCalldataMemP
    rw [e132, toByteArray_write32_read_back _ (⟨0⟩ : UInt256) (p.toNat + 132) (by omega)]
  -- assemble
  rw [readWithPadding_eq_extract' final p.toNat 164 (by norm_num) (by norm_num) (by omega)]
  have hSelExt : final.extract p.toNat (p.toNat + 4) = kickerKickSelector := by
    rw [← readWithPadding_eq_extract' final p.toNat 4 (by norm_num) (by norm_num) (by omega)]
    exact hSel
  have hUrnExt : final.extract (p.toNat + 4) (p.toNat + 36) = urn.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 4) 32 (by norm_num) (by norm_num) (by omega)]
    exact hUrn
  have hVowExt : final.extract (p.toNat + 36) (p.toNat + 68) = vow.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 36) 32 (by norm_num) (by norm_num) (by omega)]
    exact hVow
  have hTabExt : final.extract (p.toNat + 68) (p.toNat + 100) = tab.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 68) 32 (by norm_num) (by norm_num) (by omega)]
    exact hTab
  have hDinkExt : final.extract (p.toNat + 100) (p.toNat + 132) = dink.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 100) 32 (by norm_num) (by norm_num) (by omega)]
    exact hDink
  have hZeroExt : final.extract (p.toNat + 132) (p.toNat + 164) = (⟨0⟩ : UInt256).toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 132) 32 (by norm_num) (by norm_num) (by omega)]
    exact hZero
  have hsplit : final.extract p.toNat (p.toNat + 164) =
      final.extract p.toNat (p.toNat + 4) ++ final.extract (p.toNat + 4) (p.toNat + 36) ++
        final.extract (p.toNat + 36) (p.toNat + 68) ++ final.extract (p.toNat + 68) (p.toNat + 100) ++
        final.extract (p.toNat + 100) (p.toNat + 132) ++ final.extract (p.toNat + 132) (p.toNat + 164) := by
    rw [show final.extract p.toNat (p.toNat + 164) =
        final.extract p.toNat (p.toNat + 4) ++ final.extract (p.toNat + 4) (p.toNat + 164) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 4) (p.toNat + 164) =
        final.extract (p.toNat + 4) (p.toNat + 36) ++ final.extract (p.toNat + 36) (p.toNat + 164) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 36) (p.toNat + 164) =
        final.extract (p.toNat + 36) (p.toNat + 68) ++ final.extract (p.toNat + 68) (p.toNat + 164) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 68) (p.toNat + 164) =
        final.extract (p.toNat + 68) (p.toNat + 100) ++ final.extract (p.toNat + 100) (p.toNat + 164) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 100) (p.toNat + 164) =
        final.extract (p.toNat + 100) (p.toNat + 132) ++ final.extract (p.toNat + 132) (p.toNat + 164) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    simp
  rw [hsplit, hSelExt, hUrnExt, hVowExt, hTabExt, hDinkExt, hZeroExt]

/-- Read below `p` survives the kick calldata writes (for the milk chop, but generic). -/
theorem kickCalldataMemP_readBelow (p urn vow tab dink : UInt256) {mem : ByteArray} (off : ℕ)
    (hoff : off + 32 ≤ p.toNat) (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat + 164 ≤ mem.size)
    (hpsz : p.toNat + 164 < UInt256.size) :
    (kickCalldataMemP p urn vow tab dink mem).readWithPadding off 32 = mem.readWithPadding off 32 := by
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
  have h0 := kickSelectorMemP_size p hpmem
  have s1 := kickCalldataMemP_size_aux1 p urn vow tab dink hp96 hpmem hpsz
  have s2 := kickCalldataMemP_size_aux2 p urn vow tab dink hp96 hpmem hpsz
  have s3 := kickCalldataMemP_size_aux3 p urn vow tab dink hp96 hpmem hpsz
  have s4 := kickCalldataMemP_size_aux4 p urn vow tab dink hp96 hpmem hpsz
  unfold kickCalldataMemP
  rw [write32_read_below _ _ (p + ⟨132⟩).toNat off (by rw [toByteArray_size]) (by rw [s4]; omega)
      (by omega),
    write32_read_below _ _ (p + ⟨100⟩).toNat off (by rw [toByteArray_size]) (by rw [s3]; omega)
      (by omega),
    write32_read_below _ _ (p + ⟨68⟩).toNat off (by rw [toByteArray_size]) (by rw [s2]; omega)
      (by omega),
    write32_read_below _ _ (p + ⟨36⟩).toNat off (by rw [toByteArray_size]) (by rw [s1]; omega)
      (by omega),
    write32_read_below _ _ (p + ⟨4⟩).toNat off (by rw [toByteArray_size]) (by rw [h0]; omega)
      (by omega)]
  unfold kickSelectorMemP
  rw [write32_read_below _ _ p.toNat off (by rw [toByteArray_size]) (by omega) (by omega)]

/-! ## Milk-struct reads at `@64` (free ptr `= q+96 =: p`) and `@q` (flip) — for the grab/fess/kick `hFree64`/`hFlip` -/

/-- The `@0x40` free pointer in the `milk` overlay reads back as `q+96` (the milk-struct MSTORE 0x40);
this is the real free pointer `p` that grab/fess/kick build at. Discharges `catBiteReachGrabRegionC`/
`FessRegionC`/`catBiteReachKickC`'s `hFree64`/`hread64`. -/
theorem catBiteMilkMem_read64 (mem : ByteArray) (fp ilk q flip chop dunk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size) :
    (catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding 64 32 =
      UInt256.toByteArray (q + ⟨96⟩) := by
  have hscr := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  have hq96 : q.toNat = fp.toNat + 96 := by
    rw [hqfp, uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h1 := toByteArray_write32_size_of_le _ (q + ⟨96⟩) 64 mem.size mem.size hscr
    (by rw [hscr]; omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ flip q.toNat mem.size (max mem.size (q.toNat + 32)) h1
    (by rw [h1]; omega) rfl
  have h3 := toByteArray_write32_size_of_le _ chop (q + ⟨32⟩).toNat (max mem.size (q.toNat + 32))
    (max mem.size (q.toNat + 64)) h2 (by rw [h2, eq32]; omega) (by rw [eq32]; omega)
  unfold catBiteMilkMem
  rw [write32_read_below _ _ (q + ⟨64⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [h3, eq64]; omega) (by rw [eq64]; omega),
    write32_read_below _ _ (q + ⟨32⟩).toNat 64 (by rw [toByteArray_size])
      (by rw [h2, eq32]; omega) (by rw [eq32]; omega),
    write32_read_below _ _ q.toNat 64 (by rw [toByteArray_size])
      (by rw [h1]; omega) (by omega),
    toByteArray_write32_read_back _ (q + ⟨96⟩) 64 (by rw [hscr]; omega)]

/-- The `milk.flip` word at `@q` reads back through the milk overlay (`chop@(q+32)`, `dunk@(q+64)` are
both at offset `≥ q+32`). Discharges `catBiteReachKickC`'s `hFlip` (through the grab/fess overlay). -/
theorem catBiteMilkMem_readflip (mem : ByteArray) (fp ilk q flip chop dunk : UInt256)
    (hfp96 : fp.toNat + 96 ≤ mem.size) (hqfp : q = ⟨96⟩ + fp)
    (hfpsz : fp.toNat + 96 < UInt256.size) (hqsz : q.toNat + 96 < UInt256.size) :
    (catBiteMilkMem mem fp ilk q flip chop dunk).readWithPadding q.toNat 32 =
      UInt256.toByteArray flip := by
  have hscr := catBiteScratchMem_size mem fp ilk hfp96 hfpsz
  have hq96 : q.toNat = fp.toNat + 96 := by
    rw [hqfp, uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have h1 := toByteArray_write32_size_of_le _ (q + ⟨96⟩) 64 mem.size mem.size hscr
    (by rw [hscr]; omega) (by omega)
  have h2 := toByteArray_write32_size_of_le _ flip q.toNat mem.size (max mem.size (q.toNat + 32)) h1
    (by rw [h1]; omega) rfl
  have h3 := toByteArray_write32_size_of_le _ chop (q + ⟨32⟩).toNat (max mem.size (q.toNat + 32))
    (max mem.size (q.toNat + 64)) h2 (by rw [h2, eq32]; omega) (by rw [eq32]; omega)
  unfold catBiteMilkMem
  rw [write32_read_below _ _ (q + ⟨64⟩).toNat q.toNat (by rw [toByteArray_size])
      (by rw [h3, eq64]; omega) (by rw [eq64]; omega),
    write32_read_below _ _ (q + ⟨32⟩).toNat q.toNat (by rw [toByteArray_size])
      (by rw [h2, eq32]; omega) (by rw [eq32]),
    toByteArray_write32_read_back _ flip q.toNat (by rw [h1]; omega)]

end Benchmarks.Dss.Cat
