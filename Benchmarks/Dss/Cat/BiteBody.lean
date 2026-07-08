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
    (hvatCode : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  have htgt : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have hSolm : Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (catBiteVatTargetWord σ_solm I) = ⟨0⟩ := by
    rw [← htgt, ← uniswapExtCodeSizeWord_accountMapEquiv hAccounts]; exact hvatCode
  have haddr : biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      = AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, initState, catBiteVatTargetWord, catAddressReturnWord, catSlotWord]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hSolm
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
    (hvatCode : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat := by
  have htgt : catBiteVatTargetWord σ_evm I = catBiteVatTargetWord σ_solm I := by
    simp only [catBiteVatTargetWord, catAddressReturnWord, catSlotWord, solcSlotWord]
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]
  have hSolm : Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (catBiteVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    rw [← htgt, ← uniswapExtCodeSizeWord_accountMapEquiv hAccounts]; exact hvatCode
  have haddr : biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      = AccountAddress.ofUInt256 (catBiteVatTargetWord σ_solm I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    simp only [biteVatAddr, initState, catBiteVatTargetWord, catAddressReturnWord, catSlotWord]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hSolm
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
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩) :
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
    (hvatCode : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) ≠ ⟨0⟩)
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

set_option maxHeartbeats 4000000 in
theorem catBiteBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩ rfl hsel
  by_cases hshort : I.calldata.size < 68
  · exact catBiteShort hcode hsize hwv hsz4 hshort hsel hAccounts
  · rw [not_lt] at hshort
    have hsz68 : 68 ≤ I.calldata.size := hshort
    have hsz36 : 36 ≤ I.calldata.size := by omega
    have hdispatch : dispatchMsg contract I.calldata = some biteTransition := catDispatch_bite hsel
    have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
          (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I) :=
      biteDecode_ok hsz68
    -- ilks vat-code guard: no code → revert leaf; has code → continue the spine walk.
    by_cases hvatCode :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (catBiteVatTargetWord σ_evm I) = ⟨0⟩
    · exact catBiteBodyIlksNoCode hcode hsize hwv hsel hsz68 hAccounts hdispatch hdecode hvatCode
    · -- vat has code. Remaining non-short spine walk: PostIlks (ilks call: depth-limit / fail /
      -- decode-short leaves; success →) → PostUrns → 1399to1521 (live) → 1521to1708 (spot/artRate/
      -- inkSpot/unsafe) → 1708to2073 (room/dunkRoomWad/milkChop/inkDart/dink/dartLimit) →
      -- GrabRegionC → FessRegionC → 2300to2383 (litter) → KickC → catBiteSuccessBranch. (See report.)
      sorry

end Benchmarks.Dss.Cat
