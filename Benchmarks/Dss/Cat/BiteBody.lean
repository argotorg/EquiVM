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
import Benchmarks.Dss.Cat.BiteBodyAw

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-- `bite`'s calldata decodes to `biteLocals I` for ANY calldata of length `≥ 68`. The generic
`decodeCalldata_legacyBytes32_address_ok` (needing only `hsz68`) applies directly, since bite's
param types `[bytes32, addr]` are defeq `[abiBytes32, abiAddress]` and its output store is `biteLocals I`.
This is the decode the integrator needs — `catDecode_bite`'s spurious `hbig`/`hcanon` (neither derivable
from `hsize`) are avoided entirely. -/
theorem biteDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
      (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "urn"] [bytes32, addr] I.calldata
    = some (biteLocals I)
  exact decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "ilk") (y := "urn") hsz68

/-! # Cat `bite(bytes32,address)` — the reach-walk integrator (`catBiteBody`)

Chains the concrete-mem spine (`catReachBiteEntry` → `catBiteReachPostIlks` → `PostUrns` →
`1399to1521` → `1521to1708` → `1708to2073` → `catBiteReachGrabRegionC` → `FessRegionC` →
`2300to2383` → `catBiteReachKickC`) from entry to the final `RDret`, discharging each wrapper's
memory hypotheses via the committed seams (`BiteBodyMem`/`BiteBodyReach`), branching at each divergence
to the call-divergence bridges (`BiteCallDiverge`) and business leaves (`BiteRevertLeaves`), and
feeding the all-success tail to `catBiteSuccessBranch`.

Model: Jug `jugDripBody` (`Benchmarks/Dss/Jug/Drip.lean:9`). All infrastructure (spine wrappers, milk
seams `catBiteMilkMem_read64`/`_readflip` in `BiteBodyReach`, the 9 divergence bridges, the 20
business leaves, `catBiteSuccessBranch`) is green. -/

/-- Bridge: the EVM `EXTCODESIZE(vat)` word being `⟨0⟩` on `σ_evm` transfers, via `accountMapEquiv`,
to the Solm-side `vat` account having empty code (the `hvatCode0 = 0` shape the source reverts want). -/
theorem catBiteVatCodeZero_of_uniswap {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatCode : Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  have htgt : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have hSolm : Reasoning.Theory.extCodeSizeWord σ_solm (catBiteVatTargetWord σ_solm I) = ⟨0⟩ := by
    rw [← htgt, ← extCodeSizeWord_accountMapEquiv hAccounts]; exact hvatCode
  have haddr : biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      = AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, initState, catBiteVatTargetWord, catAddressReturnWord, catSlotWord]
  unfold Reasoning.Theory.extCodeSizeWord at hSolm
  rw [haddr]
  simp only [initState, State.lookupAccount]
  cases hacc : σ_solm.find? (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I)) with
  | none => native_decide
  | some acc => rw [hacc] at hSolm; simpa [Option.option] using congrArg UInt256.toNat hSolm

/-- Bridge (dual of `catBiteVatCodeZero_of_uniswap`): the EVM `EXTCODESIZE(vat)` word being nonzero on
`σ_evm` transfers, via `accountMapEquiv`, to the Solm-side `vat` account having nonempty code (the
`0 < hvatCode0` shape the ilks fail / decode / success bodies want). -/
theorem catBiteVatCodePos_of_uniswap {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatCode : Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat := by
  have htgt : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have hSolm : Reasoning.Theory.extCodeSizeWord σ_solm (catBiteVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    rw [← htgt, ← extCodeSizeWord_accountMapEquiv hAccounts]; exact hvatCode
  have haddr : biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      = AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, initState, catBiteVatTargetWord, catAddressReturnWord, catSlotWord]
  unfold Reasoning.Theory.extCodeSizeWord at hSolm
  rw [haddr]
  simp only [initState, State.lookupAccount]
  cases hacc : σ_solm.find? (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I)) with
  | none => exfalso; apply hSolm; rw [hacc]; native_decide
  | some acc =>
      rw [hacc] at hSolm
      have hne : (UInt256.ofNat acc.code.size) ≠ ⟨0⟩ := by simpa [Option.option] using hSolm
      simp only [Option.option]
      exact Nat.pos_of_ne_zero (fun h => hne (uint256_toNat_eq_zero h))

/-- **ilks no-code divergence case.** From the `bite` entry, walk the routine + `ilks` `EXTCODESIZE`
guard to pc `1233`; the vat has empty code (`hvatCode`), so the guard reverts. -/
theorem catBiteBodyIlksNoCode {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨k, C, rd1163⟩ := catReachBiteRoutine (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hsize hsel
  obtain ⟨k', C', rd1233⟩ := RD.catBiteIlksToStaticcallGuard (hR := by simp) rd1163
  exact catBiteIlksNoCodeLeaf hcode hdispatch hdecode rd1233 hvatCode (by simp)
    (catBiteSourceIlksNoCodeRevert hwv (catBiteVatCodeZero_of_uniswap hAccounts hvatCode))

/-- `EVM.address` is the identity on an `AccountAddress` (reduces mod `addressModulus`, a no-op since
the address is already in range). Local clone of the Jug/Vow `evmAddress_accountAddress`. -/
private theorem catEvmAddress_accountAddress (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

/-- Target-word ↔ vat-address reconciliation (σ-generic). The ilks/urns STATICCALL target word
`catBiteVatTargetWord σ I` (as an `AccountAddress`) equals the Solm `biteVatAddr` under `EVM.address`. -/
theorem catBiteVatEvmAddr_eq_target {cA gh bl σ σ₀ A I} {g : UInt256} :
    EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) =
      AccountAddress.ofUInt256 (catBiteVatTargetWord σ I) := by
  have haddr : biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      = AccountAddress.ofUInt256 (catBiteVatTargetWord σ I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, initState, catBiteVatTargetWord, catAddressReturnWord, catSlotWord]
  rw [haddr]; exact catEvmAddress_accountAddress _

/-- **ilks call-failed core.** The ilks `STATICCALL` returned `success = 0` (cursor `@1249`, `⟨0⟩` on
top). Map the σ_evm ilks-fail call to σ_solm, feed `catBiteSourceIlksFailRevert`, and bridge via
`catBiteIlksFailLeaf`. -/
theorem catBiteBodyIlksFailCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σi : AccountMap} {cAi : Batteries.RBSet AccountAddress compare}
    {evmIlk : EVM.State} {oi mem : ByteArray} {awi : UInt256} {ki Ci : ℕ} {R : List UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatCode : Reasoning.Theory.extCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hIlksFailCall : typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I)) "ilks" 0 [biteIlkVal I]
      (false, evmIlk, oi) false)
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (⟨0⟩ :: R) mem awi oi (cAi, σi) ki Ci)
    (hosz : oi.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨σs, As, hIlksSolm, _hEq⟩ := catBiteMapIlksCall hAccounts hIlksFailCall
  have htw : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have htgt : (AccountAddress.ofUInt256 (catBiteVatTargetWord σ_evm I))
      = EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) := by
    rw [htw]; exact (catBiteVatEvmAddr_eq_target).symm
  rw [htgt] at hIlksSolm
  exact catBiteIlksFailLeaf hcode hdispatch hdecode rd hosz hov
    (catBiteSourceIlksFailRevert hwv (catBiteVatCodePos_of_uniswap hAccounts hvatCode) hIlksSolm)

section CatBiteAwCollapse
-- Freeze `M` around the two post-`CALL` active-words collapses so the targeted `rw [hawEq]` cannot
-- `whnf`-unfold `M`'s `max`/`div` over the symbolic free pointer and drag in the giant calldata-mem
-- term (the source of the 4M-heartbeat `whnf` blowup). `catBiteAwStepL` is already global-irreducible.
attribute [local irreducible] MachineState.M

set_option maxHeartbeats 400000 in
/-- **`grab` CALL reach EXPOSING the grown active-words** `awF = catBiteAwStepL aw (p+⟨164⟩)`.
Wraps the cached `catBiteTraceGrabBuildAw` with the guard + void `RD.call` + `callCoincides`; the
post-call active words collapse back to `awF` (the void CALL's `M (M awF p 196) p 0 = awF`, via
`catBiteAwStepL_callCollapse`) — so the aw is exposed for the downstream `fess` reach. -/
theorem catBiteReachGrabAw {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'
      (UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
          UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
          (solcSlotWord σ' I ⟨4⟩) dink dart mem)
        (catBiteAwStepL aw (p + ⟨164⟩).toNat) o' (cA'', σ'') k' C'
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
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hM7lt : MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 < UInt256.size :=
    catBiteMltL aw (p + ⟨164⟩).toNat (by omega)
  have haw7val :
      (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat = MachineState.M aw.toNat (p + ⟨164⟩).toNat 32 :=
    catBiteAwStepL_toNat aw (p + ⟨164⟩).toNat hM7lt
  have hcov : p.toNat + 196 ≤ (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat * 32 := by
    rw [haw7val, e164]; simp only [MachineState.M]; omega
  obtain ⟨_, _, rd2177⟩ := catBiteTraceGrabBuildAw rd hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteGrabEncode_eq p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
    (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega) hthisCanon hdink hdart
  obtain ⟨gasWord, _, _, rd2192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2177⟩) (okPc := ⟨2189⟩) rd2177 hcodeSize
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
  -- Collapse the void CALL's post active-words `M (M awF p 196) p 0 = awF` via a STANDALONE `have`
  -- over `UInt256` (never mentioning the memory term); the targeted `rw` then abstracts only that
  -- node, so `whnf` never unfolds `M` into the giant calldata-mem term.
  have hawEq :
      UInt256.ofNat (MachineState.M (MachineState.M (catBiteAwStepL aw (p + ⟨164⟩).toNat).toNat
          p.toNat (⟨196⟩ : UInt256).toNat) p.toNat (⟨0⟩ : UInt256).toNat)
        = catBiteAwStepL aw (p + ⟨164⟩).toNat := by
    rw [show (⟨196⟩ : UInt256).toNat = 196 from by decide,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide]
    -- `o` is left to unification (`_`): instantiating it EXPLICITLY to the compound free pointer
    -- `(p + ⟨164⟩).toNat` is what makes `whnf` diverge; inferring it from the goal's RHS is cheap.
    exact catBiteAwStepL_callCollapse aw p _ 196 hcov
  rw [hawEq] at rd2193raw
  refine ⟨cA'', σ'', z, o', A', k', C', rd2193raw, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord)
    (mem := catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
      (solcSlotWord σ' I ⟨4⟩) dink dart mem)
    (inOff := p) (inSize := ⟨196⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

set_option maxHeartbeats 400000 in
/-- **`fess` CALL reach EXPOSING the grown active-words** `awF = catBiteAwStepL aw (⟨4⟩+p2)`. Mirrors
`catBiteReachFessRegionC` (Seg7f grab-guard/dartRate + the cached `catBiteTraceFessBuildAw` + guard +
void `RD.call` + `callCoincides`); the post-call `M (M awF p2 36) p2 0` collapses to `awF` (inSize=36
`callCollapse`, applied via `simp only`) — exposed for the downstream `kick` reach. -/
theorem catBiteReachFessAw {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'
      (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
          UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        (catBiteFessCalldataMemP p2 dartRate mem)
        (catBiteAwStepL aw (⟨4⟩ + p2).toNat) o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)))
        "fess" 0 [.int (Int.ofNat dartRate.toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') I.perm
    ∧ o'.size < UInt256.size := by
  have e4 : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hM2lt : MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 < UInt256.size :=
    catBiteMltL aw (⟨4⟩ + p2).toNat (by omega)
  have hawFval :
      (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat = MachineState.M aw.toNat (⟨4⟩ + p2).toNat 32 :=
    catBiteAwStepL_toNat aw (⟨4⟩ + p2).toNat hM2lt
  have hcov : p2.toNat + 36 ≤ (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat * 32 := by
    rw [hawFval, e4]; simp only [MachineState.M]; omega
  obtain ⟨_, _, rd2242⟩ := catBiteTraceSeg7f rd hstatus hRateFit hDartRate (by simp)
  obtain ⟨_, _, rd2284⟩ := catBiteTraceFessBuildAw rd2242 hFree64 hp96 hpmem hawcov hawsz hpsz (by simp)
  have hencode := catBiteFessEncode_eq p2 dartRate hpmem (by omega)
  obtain ⟨gasWord, _, _, rd2299⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd2284 hcodeSize
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
  -- Collapse the void CALL's post active-words `M (M awF p2 36) p2 0 = awF` via a STANDALONE `have`
  -- over `UInt256` (never mentioning the memory term); the targeted `rw` abstracts only that node.
  have hawEq :
      UInt256.ofNat (MachineState.M (MachineState.M (catBiteAwStepL aw (⟨4⟩ + p2).toNat).toNat
          p2.toNat (⟨36⟩ : UInt256).toNat) p2.toNat (⟨0⟩ : UInt256).toNat)
        = catBiteAwStepL aw (⟨4⟩ + p2).toNat := by
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide]
    -- `o` left to unification (see grab): explicit `(⟨4⟩ + p2).toNat` is what makes `whnf` diverge.
    exact catBiteAwStepL_callCollapse aw p2 _ 36 hcov
  rw [hawEq] at rd2300
  refine ⟨cA'', σ'', z, o', A', k', C', rd2300, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := I.perm)
    (targetWord := UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩))
    (mem := catBiteFessCalldataMemP p2 dartRate mem) (inOff := p2) (inSize := ⟨36⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

end CatBiteAwCollapse

-- The full `catBiteBody` proof (dispatch → short / ilks-no-code leaves → vat-has-code spine walk)
-- is `catBiteBodyImpl` in `BiteWalk.lean` (which imports this file's reach lemmas), wired to the
-- public `catBiteBody` in `Bite.lean`.

end Benchmarks.Dss.Cat
