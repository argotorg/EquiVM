import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteSuccessBranch
import Benchmarks.Dss.Cat.BiteRevertLeaves
import Benchmarks.Dss.Cat.BiteRevertPrim
import Benchmarks.Dss.Cat.BiteBodyMem
import Benchmarks.Dss.Cat.BiteBodyReach
import Benchmarks.Dss.Cat.BiteBodyKick
import Benchmarks.Dss.Cat.BiteCallDiverge
import Benchmarks.Dss.Cat.BiteGuardReach
import Benchmarks.Dss.Cat.BiteEVM
import Benchmarks.Dss.Cat.FileAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — active-words-exposing reach layer (cached, 8M heartbeats)

The aw-forgetting frozen call/build wrappers hide their post-call `activeWords`; these
re-derivations EXPOSE it (see individual docstrings). Split into this module so the expensive
8M-heartbeat grab build is cached and `BiteBody`'s integrator iterates fast. -/

/-- `MachineState.M` (Nat form): a memory touch of `sz` bytes at `off` inside the active window
(`off + sz ≤ a·32`) does not grow the active words. Needed to rewrite the *inner* `M` of a nested
post-`CALL` active-words expression `M (M a inOff inSize) outOff outSize`. -/
theorem catBiteMInvNat (a off sz : Nat) (h : off + sz ≤ a * 32) : MachineState.M a off sz = a := by
  rcases sz with _ | l
  · simp [MachineState.M]
  · show max a ((off + (l + 1) + 31) / 32) = a
    rw [max_eq_left]; omega

/-- Generalisation of the frozen `awInv32` to an arbitrary access size (`ofNat` form): reusable for
every call's post-`CALL` active-words invariance (`awInv32` only covers `sz = 32`; the calls copy
`68`/`196`/… bytes). -/
theorem catBiteAwInvGen (aw : UInt256) (off sz : Nat) (h : off + sz ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off sz) = aw := by
  apply u256_inj
  rw [catBiteMInvNat aw.toNat off sz h]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

/-- **ilks STATICCALL reach, exposing the concrete post-call active-words bound.** Identical
conclusion to the frozen `catBiteReachPostIlks` but additionally supplies `288 ≤ awout·32` — the bound
`catBiteReachPostUrns` needs and which the abstract wrapper's existential `awout` cannot provide. The
active words after the ilks return-copy (`outOff = 128`, `outSize = 160`) are `M (M 6 128 36) 128 160
= 9`, so `9·32 = 288`. Derives the call at the low level (`RD.uniswapStaticcall`) to keep `aw`
concrete instead of chaining the aw-forgetting wrapper. -/
theorem catBiteReachPostIlksAw {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (catBiteVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: catBiteIlksEndPtr :: catBiteIlksSelectorWord ::
          catBiteVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          UInt256.land biteAddrMaskWord (calldataWord I.calldata 36) :: biteIlkWord I ::
          ⟨419⟩ :: catSelWord I :: [])
        (o'.write 0 (catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
          catBiteIlksOutPtr.toNat (min catBiteIlksOutSize (UInt256.ofNat o'.size)).toNat)
        awout o' (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (catBiteVatTargetWord σ I)) "ilks" 0 [biteIlkVal I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') false
    ∧ o'.size < UInt256.size
    ∧ 288 ≤ awout.toNat * 32 := by
  obtain ⟨k, C, rd1163⟩ := catReachBiteRoutine (g := Sat256.ofUInt256 g) hcode hwv hsz68 hsize hsel
  obtain ⟨_, _, rd1233⟩ := RD.catBiteIlksToStaticcallGuard (hR := by simp) rd1163
  have hbytes : biteIlkBytes I = EVM.Word.toBytesBE (biteIlkWord I) := by
    simpa [biteIlkBytes, biteIlkWord, biteUrnsIlkBytes, biteUrnsIlkWord] using
      biteUrnsIlkBytes_eq_toBytesBE (I := I) hsz36
  have hencode : config.externalABI.encode? "ilks" [biteIlkVal I] =
      some ((catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem).readWithPadding
        catBiteIlksOutPtr.toNat catBiteIlksInSize.toNat) := by
    simpa [biteIlkVal] using
      catBiteIlksEncode_eq (biteIlkWord I) (biteIlkBytes I) solcFreePtrMem_size hbytes
  obtain ⟨gasWord, _, _, rd1248⟩ := RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1233⟩) (okPc := ⟨1245⟩)
    rd1233 hcodeSize (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd1249, hosz⟩ :=
    RD.uniswapStaticcall rd1248 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o', A', _, k', C', rd1249, ?_, hosz, by native_decide⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := catBiteVatTargetWord σ I)
    (mem := catBiteIlksCalldataMem (biteIlkWord I) solcFreePtrMem)
    (inOff := catBiteIlksOutPtr) (inSize := catBiteIlksInSize)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- **urns STATICCALL reach, exposing the concrete post-call active-words = input `aw`.** Same
preamble as the frozen `catBiteReachPostUrns` (`Seg2a/2b/2c1/2c2` are `aw`-preserving), but the final
urns call is derived at the low level so the post-call `aw = M (M aw 128 68) 128 64` is exposed;
for `aw ≥ 9` (from `catBiteReachPostIlksAw`'s `288 ≤ aw·32`) both `M`s collapse (`catBiteMInvNat`/
`catBiteAwInvGen`), so the output active-words are exactly the input `aw` — the bound threads through. -/
theorem catBiteReachPostUrnsAw {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status urn iRate iSpot iDust : UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (status :: catBiteIlksEndPtr :: catBiteIlksSelectorWord :: catBiteVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (haw : 288 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hmemsize : 288 ≤ mem.size)
    (ho160 : 160 ≤ o.size) (hosz : o.size < UInt256.size)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hRate : mem.readWithPadding 160 32 = UInt256.toByteArray iRate)
    (hSpot : mem.readWithPadding 192 32 = UInt256.toByteArray iSpot)
    (hDust : mem.readWithPadding 256 32 = UInt256.toByteArray iDust)
    (hurn : UInt256.land biteAddrMaskWord urn = biteUrnWord I)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ'
      (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ ::
          UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
          ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
          ⟨419⟩ :: catSelWord I :: [])
        (o'.write 0 (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
          (⟨128⟩ : UInt256).toNat (min (⟨64⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        aw o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord))
        "urns" 0 [biteIlkVal I, biteUrnVal I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') false
    ∧ o'.size < UInt256.size := by
  have hnotge : ∀ off : UInt256, off.toNat ≤ 256 → ¬ (off ≥ aw * ⟨32⟩) := by
    intro off hoff hh
    have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := hh
    rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hawsz] at hle
    omega
  have h64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := awInv32 aw (by omega)
  have h128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw := awInv32 aw (by omega)
  have h132Aw : UInt256.ofNat (MachineState.M aw.toNat 132 32) = aw := awInv32 aw (by omega)
  have h160Aw : UInt256.ofNat (MachineState.M aw.toNat 160 32) = aw := awInv32 aw (by omega)
  have h164Aw : UInt256.ofNat (MachineState.M aw.toNat 164 32) = aw := awInv32 aw (by omega)
  have h192Aw : UInt256.ofNat (MachineState.M aw.toNat 192 32) = aw := awInv32 aw (by omega)
  have h256Aw : UInt256.ofNat (MachineState.M aw.toNat 256 32) = aw := awInv32 aw (by omega)
  have hV64 : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩) (by show (64 : ℕ) < mem.size; omega)
      (hnotge ⟨64⟩ (by decide)) (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hFree64)
  have hVRate : (if (⟨160⟩ : UInt256).toNat ≥ mem.size ∨ (⟨160⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 160 32))) = iRate :=
    mloadWordValue_of_readWithPadding (off := ⟨160⟩) (v := iRate) (by show (160 : ℕ) < mem.size; omega)
      (hnotge ⟨160⟩ (by decide)) (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; exact hRate)
  have hVSpot : (if (⟨192⟩ : UInt256).toNat ≥ mem.size ∨ (⟨192⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 192 32))) = iSpot :=
    mloadWordValue_of_readWithPadding (off := ⟨192⟩) (v := iSpot) (by show (192 : ℕ) < mem.size; omega)
      (hnotge ⟨192⟩ (by decide)) (by rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]; exact hSpot)
  have hVDust : (if (⟨256⟩ : UInt256).toNat ≥ mem.size ∨ (⟨256⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 256 32))) = iDust :=
    mloadWordValue_of_readWithPadding (off := ⟨256⟩) (v := iDust) (by show (256 : ℕ) < mem.size; omega)
      (hnotge ⟨256⟩ (by decide)) (by rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]; exact hDust)
  obtain ⟨_, _, rd1289⟩ := catBiteTraceSeg2a rd hstatus ho160 hosz hV64 (mloadCost0 h64Aw) h64Aw (by simp)
  obtain ⟨_, _, rd1306⟩ := catBiteTraceSeg2b rd1289 hVRate (mloadCost0 h160Aw) h160Aw
    hVSpot (mloadCost0 h192Aw) h192Aw hVDust (mloadCost0 h256Aw) h256Aw (by simp)
  obtain ⟨_, _, rd1344⟩ := catBiteTraceSeg2c1 rd1306 hV64 (mloadCost0 h64Aw) h64Aw
    (mstoreCost0 h128Aw) h128Aw (mstoreCost0 h132Aw) h132Aw (mstoreCost0 h164Aw) h164Aw (by simp)
  have hV64' : (if (⟨64⟩ : UInt256).toNat ≥
        (biteUrnsCalldataMem (biteIlkWord I) (UInt256.land biteAddrMaskWord urn) mem).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((biteUrnsCalldataMem (biteIlkWord I) (UInt256.land biteAddrMaskWord urn) mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩)
      (by rw [biteUrnsCalldataMem_size (by omega)]; show (64 : ℕ) < mem.size; omega)
      (hnotge ⟨64⟩ (by decide))
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        biteUrnsCalldataMem_read64 (by omega) hFree64])
  obtain ⟨_, _, rd1383⟩ := catBiteTraceSeg2c2 rd1344 hV64' (mloadCost0 h64Aw) h64Aw (by simp)
  rw [hurn] at rd1383
  have hencode : config.externalABI.encode? "urns" [biteIlkVal I, biteUrnVal I] =
      some ((biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem).readWithPadding
        (⟨128⟩ : UInt256).toNat 68) :=
    biteUrnsEncode_eq I (by omega) hsz36
  -- urns STATICCALL at the low level, exposing the concrete post-call active-words.
  obtain ⟨gasWord, _, _, rd1398⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1383⟩) (okPc := ⟨1395⟩) rd1383 hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA'', σ'', z, o', A_in, callGas, k', C', hΘpack, rd1399, hosz'⟩ :=
    RD.uniswapStaticcall rd1398 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have hawEq : UInt256.ofNat (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨68⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) = aw := by
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      catBiteMInvNat aw.toNat 128 68 (by omega)]
    exact catBiteAwInvGen aw 128 64 (by omega)
  rw [hawEq] at rd1399
  refine ⟨cA'', σ'', z, o', A', k', C', rd1399, ?_, hosz'⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord)
    (mem := biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
    (inOff := ⟨128⟩) (inSize := ⟨68⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- **milk-struct region reach (Seg6) with aw GROWTH.** Re-derivation of the frozen
`catBiteTraceSeg6` (1620→1708) that GROWS the active words 9→10 at the `dunk` MSTORE `@q+64=288`
(the write `[288,320)` extends past `aw=9`'s window `[0,288)`), instead of the frozen version's
unsatisfiable `q+96 ≤ aw·32` (aw≥10) no-growth assertion. All earlier milk writes stay within `aw=9`;
only the dunk grows it (cost `Cₘ(10)−Cₘ(9)=3`, via `mstoreCost_of_stack`). Output active-words `⟨10⟩`.
Specialised to the real free-ptr layout `aw=9`, `q=224` (=96+fp, fp=128). -/
theorem catBiteReachSeg6Aw {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iDust iSpot iRate urn ilk fp q : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1620⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R) mem ⟨9⟩ o (cA', σ') k C)
    (hqNat : q.toNat = 224)
    (hFp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ (⟨9⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hQ : (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp ilk).size
          ∨ (⟨64⟩ : UInt256) ≥ (⟨9⟩ : UInt256) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteScratchMem mem fp ilk).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = q)
    (hKec : (catBiteScratchMem mem fp ilk).readWithPadding 0 64 =
        UInt256.toByteArray ilk ++ UInt256.toByteArray ⟨1⟩)
    (hawFp : fp.toNat + 96 ≤ (⟨9⟩ : UInt256).toNat * 32)
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
      ⟨10⟩ o (cA', σ') k' C' := by
  have h9 : (⟨9⟩ : UInt256).toNat = 9 := by native_decide
  -- offset arithmetic
  have e32fp : (⟨32⟩ + fp).toNat = fp.toNat + 32 := uadd_lit32_toNat fp (by omega)
  have e64fp : (⟨32⟩ + (⟨32⟩ + fp)).toNat = fp.toNat + 64 := by
    rw [uadd_lit32_toNat _ (by omega)]; omega
  have eq32 : (q + ⟨32⟩).toNat = q.toNat + 32 := uadd_word_lit32_toNat q (by omega)
  have eq64 : (q + ⟨64⟩).toNat = q.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  -- active-words invariance witnesses (all within aw=9 EXCEPT the dunk, handled by growth)
  have hM0 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 0 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM32 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 32 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM64 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 64 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMfp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat fp.toNat 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM32fp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (⟨32⟩ + fp).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hM64fp : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (⟨32⟩ + (⟨32⟩ + fp)).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMq : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat q.toNat 32) = ⟨9⟩ := catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMq32 : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat (q + ⟨32⟩).toNat 32) = ⟨9⟩ :=
    catBiteAwMInv32 ⟨9⟩ (by omega)
  have hMkec : UInt256.ofNat (MachineState.M (⟨9⟩ : UInt256).toNat 0 64) = ⟨9⟩ := catBiteAwMInv64 ⟨9⟩ (by omega)
  have hmask0 : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ = ⟨0⟩ :=
    by native_decide
  have hDunkOff : (q + ⟨64⟩).toNat = 288 := by rw [eq64, hqNat]
  -- 1620 → 3818 (call the 96-byte allocator)
  have rd1621 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1624 := rd1621.push2 ⟨1628⟩ (by native_decide) (by evm_ov)
  have rd1627 := rd1624.push2 ⟨3818⟩ (by native_decide) (by evm_ov)
  have rd3818 := rd1627.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3819 := rd3818.jumpdest (by native_decide) (by evm_ov)
  have rd3821 := rd3819.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3822 := RD.mload 0 fp ⟨9⟩ rd3821 (by native_decide) (catBiteMloadCost0 hM64) hFp hM64
    (by evm_ov)
  have rd3823 := rd3822.dup1 (by native_decide) (by evm_ov)
  have rd3825 := rd3823.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd3826 := rd3825.add (by native_decide) (by evm_ov)
  have rd3828 := rd3826.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd3829 := RD.mstore 0 ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) ⟨9⟩ rd3828
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
      ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32) ⟨9⟩ rd3842
    (by native_decide) (catBiteMstoreCost0 hMfp) (by rfl) hMfp (by evm_ov)
  have rd3845 := rd3843.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3846 := rd3845.add (by native_decide) (by evm_ov)
  have rd3848 := rd3846.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3849 := rd3848.dup2 (by native_decide) (by evm_ov)
  have rd3850 := RD.mstore 0 ((UInt256.toByteArray ⟨0⟩).write 0
      ((UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray (⟨96⟩ + fp)).write 0 mem 64 32) fp.toNat 32)
      (⟨32⟩ + fp).toNat 32) ⟨9⟩ rd3849
    (by native_decide) (catBiteMstoreCost0 hM32fp) (by rfl) hM32fp (by evm_ov)
  have rd3852 := rd3850.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd3853 := rd3852.add (by native_decide) (by evm_ov)
  have rd3855 := rd3853.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd3856 := rd3855.dup2 (by native_decide) (by evm_ov)
  have rd3857 := RD.mstore 0 (catBiteHelperMem mem fp) ⟨9⟩ rd3856
    (by native_decide) (catBiteMstoreCost0 hM64fp) (by rfl) hM64fp (by evm_ov)
  have rd3858 := rd3857.pop (by native_decide) (by evm_ov)
  have rd3859 := rd3858.swap1 (by native_decide) (by evm_ov)
  have rd1628 := rd3859.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1629 := rd1628.jumpdest (by native_decide) (by evm_ov)
  have rd1630 := rd1629.pop (by native_decide) (by evm_ov)
  have rd1632 := rd1630.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1633 := rd1632.dup9 (by native_decide) (by evm_ov)
  have rd1634 := rd1633.dup2 (by native_decide) (by evm_ov)
  have rd1635 := RD.mstore 0 ((UInt256.toByteArray ilk).write 0 (catBiteHelperMem mem fp) 0 32)
    ⟨9⟩ rd1634 (by native_decide) (catBiteMstoreCost0 hM0) (by rfl) hM0 (by evm_ov)
  have rd1637 := rd1635.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1639 := rd1637.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1640 := rd1639.dup2 (by native_decide) (by evm_ov)
  have rd1641 := rd1640.dup2 (by native_decide) (by evm_ov)
  have rd1642 := RD.mstore 0 (catBiteScratchMem mem fp ilk) ⟨9⟩ rd1641
    (by native_decide) (catBiteMstoreCost0 hM32) (by rfl) hM32 (by evm_ov)
  have rd1644 := rd1642.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd1645 := rd1644.dup1 (by native_decide) (by evm_ov)
  have rd1646 := rd1645.dup5 (by native_decide) (by evm_ov)
  have rd1647 := rd1646.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) ⟨9⟩ (by native_decide)
    (catBiteKeccakCost0 hMkec)
    (by simp only [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, hKec]; exact mappingSlot_single ilk ⟨1⟩)
    hMkec (by evm_ov)
  have rd1648 := rd1647.dup2 (by native_decide) (by evm_ov)
  have rd1649 := RD.mload 0 q ⟨9⟩ rd1648 (by native_decide) (catBiteMloadCost0 hM64) hQ hM64
    (by evm_ov)
  have rd1651 := rd1649.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd1652 := rd1651.dup2 (by native_decide) (by evm_ov)
  have rd1653 := rd1652.add (by native_decide) (by evm_ov)
  have rd1654 := rd1653.dup4 (by native_decide) (by evm_ov)
  have rd1655 := RD.mstore 0 ((UInt256.toByteArray (q + ⟨96⟩)).write 0
      (catBiteScratchMem mem fp ilk) 64 32) ⟨9⟩ rd1654
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
    ⟨9⟩ rd1667 (by native_decide) (catBiteMstoreCost0 hMq) (by rfl) hMq (by evm_ov)
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
      (q + ⟨32⟩).toNat 32) ⟨9⟩ rd1678
    (by native_decide) (catBiteMstoreCost0 hMq32) (by rfl) hMq32 (by evm_ov)
  have rd1681 := rd1679.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd1682 := rd1681.swap1 (by native_decide) (by evm_ov)
  have rd1683 := rd1682.swap2 (by native_decide) (by evm_ov)
  have rd1684 := rd1683.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1685⟩ := rd1684.sload (by native_decide) (by evm_ov)
  have rd1686 := rd1685.swap1 (by native_decide) (by evm_ov)
  have rd1687 := rd1686.dup3 (by native_decide) (by evm_ov)
  have rd1688 := rd1687.add (by native_decide) (by evm_ov)
  -- the `dunk` MSTORE @q+64=288 GROWS aw 9 → 10 (write [288,320) extends past aw=9's [0,288))
  have rd1689 := RD.mstore 3 (catBiteMilkMem mem fp ilk q
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk)))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩))
      (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩))) ⟨10⟩ rd1688
    (by native_decide)
    (fun s hs hst => mstoreCost_of_stack hs hst (by rw [hDunkOff]; native_decide))
    (by rfl) (by rw [hDunkOff]; native_decide) (by evm_ov)
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

/-! ## Local copies of the `catBiteAwStep` active-words machinery (private in the frozen `BiteTrace`)

The `grab`/`fess`/`kick` calldata builds thread their *growing* active words through an irreducible
`catBiteAwStep` atom (so `isDefEq` doesn't unfold `M`'s `max`/`div` on the abstract free pointer and
blow up).  Those helpers are `private` in `BiteTrace` (file-scoped, invisible here), so we re-declare
local copies — permitted local lemmas, no new axiom. -/

theorem catBiteMltL (a : UInt256) (o : ℕ) (ho : o + 32 < UInt256.size) :
    MachineState.M a.toNat o 32 < UInt256.size := by
  simp only [MachineState.M]
  have ha : a.toNat < UInt256.size := a.val.isLt
  omega

theorem catBiteMCollapseL (a : UInt256) (o1 o2 : ℕ) (hle : o1 ≤ o2)
    (hb : MachineState.M a.toNat o1 32 < UInt256.size) :
    UInt256.ofNat (MachineState.M (UInt256.ofNat (MachineState.M a.toNat o1 32)).toNat o2 32)
      = UInt256.ofNat (MachineState.M a.toNat o2 32) := by
  rw [UInt256.toNat_ofNat_of_lt hb]
  congr 1
  simp only [MachineState.M]
  rw [Nat.max_assoc]
  congr 1
  exact Nat.max_eq_right (by omega)

@[irreducible] noncomputable def catBiteAwStepL (aw : UInt256) (off : ℕ) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat off 32)

theorem catBiteAwStepL_collapse (aw : UInt256) (o1 o2 : ℕ) (hle : o1 ≤ o2)
    (hb : MachineState.M aw.toNat o1 32 < UInt256.size) :
    UInt256.ofNat (MachineState.M (catBiteAwStepL aw o1).toNat o2 32) = catBiteAwStepL aw o2 := by
  unfold catBiteAwStepL
  exact catBiteMCollapseL aw o1 o2 hle hb

theorem catBiteAwStepL_toNat (aw : UInt256) (off : ℕ)
    (hb : MachineState.M aw.toNat off 32 < UInt256.size) :
    (catBiteAwStepL aw off).toNat = MachineState.M aw.toNat off 32 := by
  unfold catBiteAwStepL; exact UInt256.toNat_ofNat_of_lt hb

theorem catBiteMstoreCostML {aw off val : UInt256} {t : List UInt256} :
    ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: val :: t →
      memoryExpansionCost s .MSTORE
        = Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  intro s haw hstk
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]

/-- Void-`CALL` active-words collapse (`inSize=196`, `outSize=0`): the `grab` void `CALL`'s post
active-words `M (M awF·toNat p 196) p 0` collapse back to `awF` when `awF` already covers `[p,p+196)`.
Proven by term-mode `catBiteMInvNat` applications (never `rw`-matching `catBiteAwStepL.toNat` in a
goal, which would unfold `M` on the abstract free pointer and blow up). -/
theorem catBiteAwStepL_callCollapse (aw p : UInt256) (o : ℕ)
    (hcov : p.toNat + 196 ≤ (catBiteAwStepL aw o).toNat * 32) :
    UInt256.ofNat (MachineState.M (MachineState.M (catBiteAwStepL aw o).toNat p.toNat 196)
      p.toNat 0) = catBiteAwStepL aw o := by
  have h1 : MachineState.M (catBiteAwStepL aw o).toNat p.toNat 196 = (catBiteAwStepL aw o).toNat :=
    catBiteMInvNat _ p.toNat 196 hcov
  have h2 : MachineState.M (catBiteAwStepL aw o).toNat p.toNat 0 = (catBiteAwStepL aw o).toNat :=
    catBiteMInvNat _ p.toNat 0 (by omega)
  rw [h1, h2]
  exact u256_ofNat_toNat _

set_option maxHeartbeats 8000000 in
/-- **`grab` calldata build (2073→2177) EXPOSING the grown active-words** `awF = catBiteAwStepL aw
(p+⟨164⟩)`. Verbatim re-derivation of the frozen `catBiteTraceGrabBuild` (which already grows aw
correctly through the 7 expanding MSTOREs, dodging heartbeat blowup via the `catBiteAwStep` atom) but
with the final `awF` EXPOSED in the conclusion instead of hidden under `∃` — so the downstream `fess`
reach can discharge its `p2 ≤ aw·32` precondition. Uses the local `catBiteAwStepL` machinery (the
`BiteTrace` originals are `private`). The `awF` bound is recovered via `catBiteAwStepL_toNat`
(`aw=10, p=320 ⇒ awF.toNat=17`). -/
theorem catBiteTraceGrabBuildAw {cA gh bl σ σ₀ A I} {g : UInt256}
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
    ∃ (k' C' : ℕ), RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2177⟩
      (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        ⟨0⟩ :: p :: ⟨196⟩ :: p :: ⟨0⟩ :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
        UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteGrabCalldataMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩)
        dink dart mem)
      (catBiteAwStepL aw (p + ⟨164⟩).toNat) o (cA', σ') k' C' := by
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
  have hstep1 : UInt256.ofNat (MachineState.M aw.toNat p.toNat 32) = catBiteAwStepL aw p.toNat := by
    simp only [catBiteAwStepL]
  have hM7lt : MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 < UInt256.size :=
    catBiteMltL aw (p + ⟨164⟩).toNat (by omega)
  have haw7val :
      (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat = MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 :=
    catBiteAwStepL_toNat aw (p + ⟨164⟩).toNat hM7lt
  have haw7ge : 96 ≤ (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat * 32 := by
    rw [haw7val, e164]; simp only [MachineState.M]; omega
  have haw7sz : (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat * 32 < UInt256.size := by
    rw [haw7val, e164]; simp only [MachineState.M]; omega
  have hM7out : UInt256.ofNat
      (MachineState.M (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat (⟨64⟩ : UInt256).toNat 32)
      = catBiteAwStepL aw (p + ⟨164⟩).toNat :=
    catBiteAwMInv32 (catBiteAwStepL aw (p + ⟨164⟩).toNat) (by rw [h64]; omega)
  have hcol2 := catBiteAwStepL_collapse aw p.toNat (p + ⟨4⟩).toNat (by omega)
    (catBiteMltL aw p.toNat (by omega))
  have hcol3 := catBiteAwStepL_collapse aw (p + ⟨4⟩).toNat (p + ⟨36⟩).toNat (by omega)
    (catBiteMltL aw (p + ⟨4⟩).toNat (by omega))
  have hcol4 := catBiteAwStepL_collapse aw (p + ⟨36⟩).toNat (p + ⟨68⟩).toNat (by omega)
    (catBiteMltL aw (p + ⟨36⟩).toNat (by omega))
  have hcol5 := catBiteAwStepL_collapse aw (p + ⟨68⟩).toNat (p + ⟨100⟩).toNat (by omega)
    (catBiteMltL aw (p + ⟨68⟩).toNat (by omega))
  have hcol6 := catBiteAwStepL_collapse aw (p + ⟨100⟩).toNat (p + ⟨132⟩).toNat (by omega)
    (catBiteMltL aw (p + ⟨100⟩).toNat (by omega))
  have hcol7 := catBiteAwStepL_collapse aw (p + ⟨132⟩).toNat (p + ⟨164⟩).toNat (by omega)
    (catBiteMltL aw (p + ⟨132⟩).toNat (by omega))
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
  have rd2090 := rd2085.push4 ⟨32419069⟩ (by native_decide) (by evm_ov)
  have rd2092 := rd2090.push1 ⟨230⟩ (by native_decide) (by evm_ov)
  have rd2093 := rd2092.shl (by native_decide) (by evm_ov)
  have rd2094d := rd2093.dup2 (by native_decide) (by evm_ov)
  have rd2094 := RD.mstore _ (catBiteGrabSelMemP p mem) (catBiteAwStepL aw p.toNat) rd2094d
    (by native_decide) catBiteMstoreCostML rfl hstep1 (by evm_ov)
  have rd2095 := rd2094.swap3 (by native_decide) (by evm_ov)
  have rd2096 := rd2095.dup4 (by native_decide) (by evm_ov)
  have rd2097 := rd2096.add (by native_decide) (by evm_ov)
  have rd2098 := RD.dup16 rd2097 (by native_decide) (by evm_ov)
  have rd2099 := rd2098.swap1 (by native_decide) (by evm_ov)
  have rd2100 := RD.mstore _ (catBiteGrabIlkMemP p ilk mem) (catBiteAwStepL aw (p + ⟨4⟩).toNat) rd2099
    (by native_decide) catBiteMstoreCostML rfl hcol2 (by evm_ov)
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
  have rd2116 := RD.mstore _ (catBiteGrabUrnMemP p ilk urn mem) (catBiteAwStepL aw (p + ⟨36⟩).toNat)
    rd2115 (by native_decide) catBiteMstoreCostML rfl hcol3 (by evm_ov)
  have rd2117 := rd2116.uniswapAddress (by native_decide) (by evm_ov)
  have rd2118 := rd2117.push1 ⟨68⟩ (by native_decide) (by evm_ov)
  have rd2120 := rd2118.dup6 (by native_decide) (by evm_ov)
  have rd2121 := rd2120.add (by native_decide) (by evm_ov)
  have rd2122 := RD.mstore _ (catBiteGrabThisMemP p ilk urn (UInt256.ofNat I.codeOwner.val) mem)
    (catBiteAwStepL aw (p + ⟨68⟩).toNat) rd2121 (by native_decide) catBiteMstoreCostML rfl hcol4
    (by evm_ov)
  have rd2123 := rd2122.swap2 (by native_decide) (by evm_ov)
  have rd2124 := rd2123.dup3 (by native_decide) (by evm_ov)
  have rd2125 := rd2124.and (by native_decide) (by evm_ov)
  have rd2126 := rd2125.push1 ⟨100⟩ (by native_decide) (by evm_ov)
  have rd2128 := rd2126.dup5 (by native_decide) (by evm_ov)
  have rd2129 := rd2128.add (by native_decide) (by evm_ov)
  have rd2130 := RD.mstore _
    (catBiteGrabVowMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩) mem)
    (catBiteAwStepL aw (p + ⟨100⟩).toNat) rd2129 (by native_decide) catBiteMstoreCostML rfl hcol5
    (by evm_ov)
  have rd2131 := rd2130.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2133 := rd2131.dup6 (by native_decide) (by evm_ov)
  have rd2134 := rd2133.dup2 (by native_decide) (by evm_ov)
  have rd2135 := rd2134.sub (by native_decide) (by evm_ov)
  have rd2136 := rd2135.push1 ⟨132⟩ (by native_decide) (by evm_ov)
  have rd2138 := rd2136.dup6 (by native_decide) (by evm_ov)
  have rd2139 := rd2138.add (by native_decide) (by evm_ov)
  have rd2140 := RD.mstore _
    (catBiteGrabDinkMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩) dink mem)
    (catBiteAwStepL aw (p + ⟨132⟩).toNat) rd2139 (by native_decide) catBiteMstoreCostML rfl hcol6
    (by evm_ov)
  have rd2141 := rd2140.dup7 (by native_decide) (by evm_ov)
  have rd2142 := rd2141.dup2 (by native_decide) (by evm_ov)
  have rd2143 := rd2142.sub (by native_decide) (by evm_ov)
  have rd2144 := rd2143.push1 ⟨164⟩ (by native_decide) (by evm_ov)
  have rd2146 := rd2144.dup6 (by native_decide) (by evm_ov)
  have rd2147 := rd2146.add (by native_decide) (by evm_ov)
  have rd2148 := RD.mstore _
    (catBiteGrabCalldataMemP p ilk urn (UInt256.ofNat I.codeOwner.val) (solcSlotWord σ' I ⟨4⟩)
      dink dart mem) (catBiteAwStepL aw (p + ⟨164⟩).toNat) rd2147 (by native_decide) catBiteMstoreCostML
    rfl hcol7 (by evm_ov)
  have rd2149 := rd2148.swap1 (by native_decide) (by evm_ov)
  have rd2150 := RD.mload 0 p (catBiteAwStepL aw (p + ⟨164⟩).toNat) rd2149 (by native_decide)
    (catBiteMloadCost0 hM7out)
    (mloadWordValue_of_readWithPadding
      (by rw [h64]
          have hsz := catBiteGrabCalldataMemP_size p ilk urn (UInt256.ofNat I.codeOwner.val)
            (solcSlotWord σ' I ⟨4⟩) dink dart hpmem (by omega)
          omega)
      (by intro hh
          have hle : (catBiteAwStepL aw (p + ⟨164⟩).toNat * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt haw7sz, h64] at hle; omega)
      (by rw [h64,
            catBiteGrabCalldataMemP_read64 p ilk urn (UInt256.ofNat I.codeOwner.val)
              (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega)]
          exact hFree64)) hM7out (by evm_ov)
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
  exact ⟨_, _, rd2175.dup1 (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 8000000 in
/-- **`fess` calldata build (2242→2284) EXPOSING the grown active-words** `awF = catBiteAwStepL aw
(⟨4⟩+p2)`. Local re-derivation of the frozen `catBiteTraceFessBuild` (2 expanding MSTOREs) exposing
the final `awF` for the downstream reach. -/
theorem catBiteTraceFessBuildAw {cA gh bl σ σ₀ A I} {g : UInt256}
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
    ∃ (k' C' : ℕ), RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2284⟩
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        ⟨0⟩ :: p2 :: ⟨36⟩ :: p2 :: ⟨0⟩ :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
        UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
        dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteFessCalldataMemP p2 dartRate mem) (catBiteAwStepL aw (⟨4⟩ + p2).toNat)
      o (cA', σ') k' C' := by
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw :=
    catBiteAwMInv32 aw (by rw [h64]; omega)
  have hstepF1 : UInt256.ofNat (MachineState.M aw.toNat p2.toNat 32) = catBiteAwStepL aw p2.toNat := by
    simp only [catBiteAwStepL]
  have hM2lt : MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 < UInt256.size :=
    catBiteMltL aw (⟨4⟩ + p2).toNat (by omega)
  have hawFval :
      (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat = MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 :=
    catBiteAwStepL_toNat aw (⟨4⟩ + p2).toNat hM2lt
  have hawFge : 96 ≤ (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat * 32 := by
    rw [hawFval, e4]; simp only [MachineState.M]; omega
  have hawFsz : (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat * 32 < UInt256.size := by
    rw [hawFval, e4]; simp only [MachineState.M]; omega
  have hMFout : UInt256.ofNat
      (MachineState.M (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat (⟨64⟩ : UInt256).toNat 32)
      = catBiteAwStepL aw (⟨4⟩ + p2).toNat :=
    catBiteAwMInv32 (catBiteAwStepL aw (⟨4⟩ + p2).toNat) (by rw [h64]; omega)
  have hcolF2 := catBiteAwStepL_collapse aw p2.toNat (⟨4⟩ + p2).toNat (by omega)
    (catBiteMltL aw p2.toNat (by omega))
  have hsub36 : UInt256.sub (⟨32⟩ + (⟨4⟩ + p2)) p2 = ⟨36⟩ := by
    apply u256_inj
    have he : (⟨32⟩ + (⟨4⟩ + p2)).toNat = p2.toNat + 36 := by
      rw [uadd_toNat, e4, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [usub_toNat (by rw [he]; omega), he, show (⟨36⟩ : UInt256).toNat = 36 from by decide]; omega
  have rd2243 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd2245 := rd2243.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2246 := RD.mload 0 p2 aw rd2245 (by native_decide) (catBiteMloadCost0 hM64)
    (mloadWordValue_of_readWithPadding (by rw [h64]; omega)
      (by intro hh; have hle : (aw * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt hawsz, h64] at hle; omega)
      (by rw [h64]; exact hFree64)) hM64 (by evm_ov)
  have rd2247 := rd2246.dup3 (by native_decide) (by evm_ov)
  have rd2252 := rd2247.push4 ⟨4294967295⟩ (by native_decide) (by evm_ov)
  have rd2253 := rd2252.and (by native_decide) (by evm_ov)
  have rd2255 := rd2253.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd2256 := rd2255.shl (by native_decide) (by evm_ov)
  have rd2257d := rd2256.dup2 (by native_decide) (by evm_ov)
  have rd2257 := RD.mstore _ (catBiteFessSelMemP p2 mem) (catBiteAwStepL aw p2.toNat) rd2257d
    (by native_decide) catBiteMstoreCostML rfl hstepF1 (by evm_ov)
  have rd2258 := rd2257.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd2260 := rd2258.add (by native_decide) (by evm_ov)
  have rd2261 := rd2260.dup1 (by native_decide) (by evm_ov)
  have rd2262 := rd2261.dup3 (by native_decide) (by evm_ov)
  have rd2263 := rd2262.dup2 (by native_decide) (by evm_ov)
  have rd2264 := RD.mstore _ (catBiteFessCalldataMemP p2 dartRate mem)
    (catBiteAwStepL aw (⟨4⟩ + p2).toNat) rd2263 (by native_decide) catBiteMstoreCostML rfl hcolF2
    (by evm_ov)
  have rd2265 := rd2264.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd2267 := rd2265.add (by native_decide) (by evm_ov)
  have rd2268 := rd2267.swap2 (by native_decide) (by evm_ov)
  have rd2269 := rd2268.pop (by native_decide) (by evm_ov)
  have rd2270 := rd2269.pop (by native_decide) (by evm_ov)
  have rd2271 := rd2270.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2273 := rd2271.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2275 := RD.mload 0 p2 (catBiteAwStepL aw (⟨4⟩ + p2).toNat) rd2273 (by native_decide)
    (catBiteMloadCost0 hMFout)
    (mloadWordValue_of_readWithPadding
      (by rw [h64]
          have hsz := catBiteFessCalldataMemP_size p2 dartRate hpmem (by omega)
          omega)
      (by intro hh
          have hle : (catBiteAwStepL aw (⟨4⟩ + p2).toNat * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat := hh
          rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
            Nat.mod_eq_of_lt hawFsz, h64] at hle; omega)
      (by rw [h64, catBiteFessCalldataMemP_read64 p2 dartRate hp96 hpmem (by omega)]
          exact hFree64)) hMFout (by evm_ov)
  have rd2276 := rd2275.dup1 (by native_decide) (by evm_ov)
  have rd2277 := rd2276.dup4 (by native_decide) (by evm_ov)
  have rd2278 := rd2277.sub (by native_decide) (by evm_ov)
  rw [hsub36] at rd2278
  have rd2279 := rd2278.dup2 (by native_decide) (by evm_ov)
  have rd2280 := rd2279.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2282 := rd2280.dup8 (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2282.dup1 (by native_decide) (by evm_ov)⟩

end Benchmarks.Dss.Cat
