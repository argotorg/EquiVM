import Benchmarks.Dss.Cat.BiteTrace
import Benchmarks.Dss.Cat.BiteCallGrab
import Benchmarks.Dss.Cat.BiteCallFess
import Benchmarks.Dss.Cat.BiteConnectGrab

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite(bytes32,address)` — the connect (compose + revert traces)

`BiteConnect` assembles the frozen `BiteTrace` segment reach-lemmas into the full success trace
(`catBiteSuccessTrace`), builds the short revert traces, and connects the `bite` body
(`catBiteBody`) via the `reEquivExecution*` glue against `BiteSource`'s Solm-body lemmas. -/

/-- The shared DSMath checked-multiply routine `@3720` on the **overflow** path: when `a*b ≥ 2^256`
the `(p/a)==b` guard is `0`, the `JUMPI` falls through, and the `PUSH1 0; DUP1; REVERT` stub fires.
Used by the six `checkedMul` overflow reverts (inkSpot / artRate / dunkRoomWad / inkDart / dartRate /
tabBase). -/
theorem RD.catBiteCheckedMulRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3720⟩
      (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have ha : a ≠ ⟨0⟩ := by
    intro h; subst h
    rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_mul] at hover
    exact absurd hover (by decide)
  have hiszero0 : UInt256.isZero a = ⟨0⟩ := isZero_eq_zero_of_ne ha
  have hneq : UInt256.div (UInt256.mul b a) a ≠ b := by
    intro heq
    have hval := congrArg UInt256.toNat heq
    rw [udiv_toNat, u256_mul_toNat] at hval
    have hdivmul : b.toNat * a.toNat ≤ (b.toNat * a.toNat) % UInt256.size := by
      calc b.toNat * a.toNat
          = (((b.toNat * a.toNat) % UInt256.size) / a.toNat) * a.toNat := by rw [hval]
        _ ≤ (b.toNat * a.toNat) % UInt256.size := Nat.div_mul_le_self _ _
    have hmod : (b.toNat * a.toNat) % UInt256.size < UInt256.size := Nat.mod_lt _ (by decide)
    have hcomm : a.toNat * b.toNat = b.toNat * a.toNat := Nat.mul_comm _ _
    omega
  have heq0 : UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun h1 => hneq (uInt256_eq_one_eq h1))
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
  rw [heq0] at rd3747
  have rd3748 := rd3747.jumpdest (by native_decide) (by evm_ov)
  have rd3751 := rd3748.push2 ⟨3756⟩ (by native_decide) (by evm_ov)
  have rd3752 := rd3751.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd3752 (by native_decide) (by native_decide)
    (by native_decide) (by evm_ov)

/-- Entry (`375`) → routine (`1163`) → ilks `STATICCALL` (Seg 1, at pc `1249`): the first view call.
Pure trace chaining; the ilks `typedCallViaEVM` coupling threads out. -/
theorem catBiteReachPostIlks {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (catBiteVatTargetWord σ I) ≠ ⟨0⟩)
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
    ∧ o'.size < UInt256.size := by
  have hsz36 : 36 ≤ I.calldata.size := by omega
  obtain ⟨k, C, rd1163⟩ := catReachBiteRoutine hcode hwv hsz68 hsize hsel
  exact catBiteTraceSeg1 (R := [⟨419⟩, catSelWord I]) hsz36 rd1163 hcodeSize hdepth (by simp)

/-- Post-ilks (`1249`, ilks succeeded) → urns `STATICCALL` (`1399`): the ilks-return decode
(`Seg2a`/`Seg2b`), `urns` calldata build (`Seg2c1`/`Seg2c2`), and the urns `STATICCALL`
(`RD.catBiteUrnsStaticcallGen`).  The urns `typedCallViaEVM` coupling threads out.  The post-ilks
memory facts (`hFree64`/`hRate`/`hSpot`/`hDust`) and `aw`/size bounds are taken as hypotheses
(discharged by `catBiteBody` from the ilks-return decode). -/
theorem catBiteReachPostUrns {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'
      (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (o' : ByteArray) (A'' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ ::
          UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
          ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
          ⟨419⟩ :: catSelWord I :: [])
        (o'.write 0 (biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem)
          (⟨128⟩ : UInt256).toNat (min (⟨64⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        awout o' (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord))
        "urns" 0 [biteIlkVal I, biteUrnVal I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, o') false
    ∧ o'.size < UInt256.size := by
  -- active-words invariance + not-≥ bounds for offsets ≤ 256
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
  -- if-forms for the MLOAD values, from the raw reads
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
  -- Seg2a: ilks call-success guard + returndatasize check → 1289
  obtain ⟨_, _, rd1289⟩ := catBiteTraceSeg2a rd hstatus ho160 hosz hV64 (mloadCost0 h64Aw) h64Aw (by simp)
  -- Seg2b: read iRate/iSpot/iDust → 1306
  obtain ⟨_, _, rd1306⟩ := catBiteTraceSeg2b rd1289 hVRate (mloadCost0 h160Aw) h160Aw
    hVSpot (mloadCost0 h192Aw) h192Aw hVDust (mloadCost0 h256Aw) h256Aw (by simp)
  -- Seg2c1: build urns calldata → 1344
  obtain ⟨_, _, rd1344⟩ := catBiteTraceSeg2c1 rd1306 hV64 (mloadCost0 h64Aw) h64Aw
    (mstoreCost0 h128Aw) h128Aw (mstoreCost0 h132Aw) h132Aw (mstoreCost0 h164Aw) h164Aw (by simp)
  -- Seg2c2: assemble urns STATICCALL frame → 1383
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
  -- reconcile the built calldata memory: land mask urn = biteUrnWord I
  rw [hurn] at rd1383
  -- urns STATICCALL → 1399, producing the `urns` typedCallViaEVM coupling
  have hencode : config.externalABI.encode? "urns" [biteIlkVal I, biteUrnVal I] =
      some ((biteUrnsCalldataMem (biteIlkWord I) (biteUrnWord I) mem).readWithPadding
        (⟨128⟩ : UInt256).toNat 68) :=
    biteUrnsEncode_eq I (by omega) hsz36
  exact RD.catBiteUrnsStaticcallGen (outPtr := ⟨128⟩) rd1383 hcodeSize hdepth hencode (by simp)

/-- Post-urns (`1399`, urns succeeded) → `require(live == 1)` cleared (`1521`): urns 2-word return
decode (`Seg3`: `ink`@128, `art`@160) then the live check (`Seg4`). -/
theorem catBiteReach1399to1521 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status urn ink art iRate iSpot iDust : UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (status :: ⟨196⟩ :: ⟨606387804⟩ :: UInt256.land (catSlotWord ⟨3⟩ σ' I) biteAddrMaskWord ::
        ⟨0⟩ :: ⟨0⟩ :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
        ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
    (haw : 192 ≤ aw.toNat * 32) (hawsz : aw.toNat * 32 < UInt256.size)
    (hmemsize : 192 ≤ mem.size)
    (hlo : 64 ≤ o.size) (hhi : o.size < UInt256.size)
    (hFree64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hInk : mem.readWithPadding 128 32 = UInt256.toByteArray ink)
    (hArt : mem.readWithPadding 160 32 = UInt256.toByteArray art)
    (hlive : catSlotWord ⟨2⟩ σ' I = ⟨1⟩) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
        ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k' C' := by
  have hnotge : ∀ off : UInt256, off.toNat ≤ 160 → ¬ (off ≥ aw * ⟨32⟩) := by
    intro off hoff hh
    have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := hh
    rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt hawsz] at hle
    omega
  have h64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := awInv32 aw (by omega)
  have h128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw := awInv32 aw (by omega)
  have h160Aw : UInt256.ofNat (MachineState.M aw.toNat 160 32) = aw := awInv32 aw (by omega)
  have hV64 : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding (off := ⟨64⟩) (v := ⟨128⟩) (by show (64 : ℕ) < mem.size; omega)
      (hnotge ⟨64⟩ (by decide)) (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact hFree64)
  have hVInk : (if (⟨128⟩ : UInt256).toNat ≥ mem.size ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32)))
        = ink :=
    mloadWordValue_of_readWithPadding (off := ⟨128⟩) (v := ink) (by show (128 : ℕ) < mem.size; omega)
      (hnotge ⟨128⟩ (by decide)) (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hInk)
  have hVArt : (if (⟨160⟩ : UInt256).toNat ≥ mem.size ∨ (⟨160⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨160⟩ : UInt256).toNat 32)))
        = art :=
    mloadWordValue_of_readWithPadding (off := ⟨160⟩) (v := art) (by show (160 : ℕ) < mem.size; omega)
      (hnotge ⟨160⟩ (by decide)) (by rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]; exact hArt)
  obtain ⟨_, _, rd1447⟩ := catBiteTraceSeg3 rd hstatus hlo hhi hV64 (mloadCost0 h64Aw) h64Aw
    hVInk (mloadCost0 h128Aw) h128Aw hVArt (mloadCost0 h160Aw) h160Aw (by simp)
  exact catBiteTraceSeg4 rd1447 hlive (by simp)

/-- `1521` → `1708`: `require(spot > 0 && inkSpot < artRateUnsafe)` (`Seg5`) then the
`ilks[ilk]` struct load (keccak allocator) + `room = box - litter` checkedSub (`Seg6`).  The
free-pointer / keccak-scratch facts (`hFp`/`hQ`/`hKec`) are taken as hypotheses (discharged by
`catBiteBody` from the concrete post-urns memory, `fp = 128`, `q = 224`). -/
theorem catBiteReach1521to1708 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {art ink iRate iSpot iDust urn fp q : UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1521⟩
      (art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
        ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hspotPos : 0 < iSpot.toNat)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hFp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fp)
    (hQ : (if (⟨64⟩ : UInt256).toNat ≥ (catBiteScratchMem mem fp (biteIlkWord I)).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((catBiteScratchMem mem fp (biteIlkWord I)).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = q)
    (hKec : (catBiteScratchMem mem fp (biteIlkWord I)).readWithPadding 0 64 =
        UInt256.toByteArray (biteIlkWord I) ++ UInt256.toByteArray ⟨1⟩)
    (hawFp : fp.toNat + 96 ≤ aw.toNat * 32)
    (hawQ : q.toNat + 96 ≤ aw.toNat * 32)
    (hfpsz : fp.toNat + 96 < UInt256.size)
    (hqsz : q.toNat + 96 < UInt256.size)
    (hle : (solcSlotWord σ' I ⟨6⟩).toNat ≤ (solcSlotWord σ' I ⟨5⟩).toNat) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (UInt256.sub (solcSlotWord σ' I ⟨5⟩) (solcSlotWord σ' I ⟨6⟩) ::
        ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn :: biteIlkWord I ::
        ⟨419⟩ :: catSelWord I :: [])
      (catBiteMilkMem mem fp (biteIlkWord I) q
        (UInt256.land biteAddrMaskWord (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ (biteIlkWord I))))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨1⟩))
        (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ (biteIlkWord I) + ⟨2⟩)))
      aw o (cA', σ') k' C' := by
  obtain ⟨_, _, rd1620⟩ := catBiteTraceSeg5 rd hspotPos hfitArtRate hfitInkSpot hunsafe (by simp)
  exact catBiteTraceSeg6 rd1620 hFp hQ hKec hawFp hawQ hfpsz hqsz hle (by simp)

/-- `1708` → `2073`: the `dart`/`dink` DSMath chain (`Seg7a` room require, `Seg7b` dart, `Seg7c` dink
+ `require(dart>0 && dink>0)`, `Seg7d` int256 bounds).  `milkChop`/`milkDunk` are read from the
`milk` struct at `mem[32+q]`/`mem[64+q]`; the derived values are pinned by the `h*` equations. -/
theorem catBiteReach1708to2073 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {room q art ink iDust iSpot iRate urn : UInt256}
    {milkChop milkDunk dunkRoom dunkRoomWad dartDenomRate dartCandidate dart : UInt256}
    {inkDart dinkCandidate dink : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1708⟩
      (room :: ⟨0⟩ :: ⟨0⟩ :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hlitterbox : (solcSlotWord σ' I ⟨6⟩).toNat < (solcSlotWord σ' I ⟨5⟩).toNat)
    (hroomdust : iDust.toNat ≤ room.toNat)
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
    (hArtPos : art ≠ ⟨0⟩)
    (hFitInkDart : dart.toNat * ink.toNat < UInt256.size)
    (hInkDart : UInt256.mul ink dart = inkDart)
    (hDinkCand : UInt256.div inkDart art = dinkCandidate)
    (hDink : (if UInt256.gt ink dinkCandidate = ⟨0⟩ then ink else dinkCandidate) = dink)
    (hDartPos : 0 < dart.toNat) (hDinkPos : 0 < dink.toNat)
    (hDartLim : dart.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat)
    (hDinkLim : dink.toNat ≤ (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩).toNat) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2073⟩
      (dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k' C' := by
  obtain ⟨_, _, rd1810⟩ := catBiteTraceSeg7a rd hlitterbox hroomdust (by simp)
  obtain ⟨_, _, rd1872⟩ := catBiteTraceSeg7b rd1810 hChop hDunk haw hqsz hRatePos hChopPos
    hDunkRoom hFitWad hDunkRoomWad hDartDenom hDartCand hDart (by simp)
  obtain ⟨_, _, rd1985⟩ := catBiteTraceSeg7c rd1872 hArtPos hFitInkDart hInkDart hDinkCand hDink
    hDartPos hDinkPos (by simp)
  exact catBiteTraceSeg7d rd1985 hDartLim hDinkLim (by simp)

/-- `2300` (fess succeeded) → `2383`: the fess call-success guard + tail POPs (`Seg7h`), then
`dartRate`/`tabBase`/`tab`/`litterNew` arithmetic and the `SSTORE litter@6` (`Seg7i`).  Ends with
slot `6` updated to `litterNew` in the account map. -/
theorem catBiteReach2300to2383 {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {status f0 f1 f2 dink dart q art ink iDust iSpot iRate urn : UInt256}
    {milkChop dartRate tabBase tab litterNew : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
      (status :: f0 :: f1 :: f2 :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate ::
        ⟨0⟩ :: urn :: biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', σ') k C)
    (hstatus : status ≠ ⟨0⟩)
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
    (hLitterNew : solcSlotWord σ' I ⟨6⟩ + tab = litterNew) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2383⟩
      (tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem aw o (cA', sstoreAccountMap I.codeOwner σ' ⟨6⟩ litterNew) k' C' := by
  obtain ⟨_, _, rd2321⟩ := catBiteTraceSeg7h rd hstatus (by simp)
  exact catBiteTraceSeg7i rd2321 hChop haw hqsz hperm hRateFit hChopFit hLitFit
    hDartRate hTabBase hTab hLitterNew (by simp)

/-- `2532` (kick succeeded) → `RETURN`: the kick call-success guard + `id` extract + `dtab`
checkedMul (`Seg8b1`), then the `Bite(...)` `LOG3` event and the shared `@419` uint256 return
encoder (`Seg8b2`), producing `RDret … (toByteArray id)` — the full success result of `bite`. -/
theorem catBiteReach2532toRet {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status target tab dink dart q art ink iDust iSpot iRate id urn milkFlip : UInt256}
    {mem8 o : ByteArray} {aw8 : UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (status :: ⟨292⟩ :: ⟨891151872⟩ :: target ::
        tab :: dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
        biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
      mem8 aw8 o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoszLt : o.size < UInt256.size)
    (hFree8 : (if (⟨64⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨64⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 64 32))) = ⟨128⟩)
    (hId8 : (if (⟨128⟩ : UInt256).toNat ≥ mem8.size ∨ (⟨128⟩ : UInt256) ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding 128 32))) = id)
    (hperm : I.perm = true)
    (hmem8size : 288 ≤ mem8.size)
    (haw8q : q.toNat + 32 ≤ aw8.toNat * 32)
    (haw8ev : 288 ≤ aw8.toNat * 32)
    (hRateFit : iRate.toNat * dart.toNat < UInt256.size)
    (hFlipEv : (if q.toNat ≥ mem8.size ∨ q ≥ aw8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem8.readWithPadding q.toNat 32))) = milkFlip) :
    RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id) := by
  obtain ⟨_, _, rd2631⟩ := catBiteTraceSeg8b1 (R3 := []) rd hstatus ho32 hoszLt hFree8 hId8
    haw8ev hRateFit (by simp)
  exact catBiteTraceSeg8b2 (R3 := []) rd2631 hperm hmem8size haw8q haw8ev hFlipEv hFree8 (by simp)

/-- The `fess` memory-encoding coupling for the trace's `catBiteFessCalldataMemP` (bridged to
`fessEncode_eq` — the selector words agree by `land` commutativity and `(⟨4⟩+p2).toNat = p2.toNat+4`). -/
theorem catBiteFessEncode_eq (p2 dartRate : UInt256) {mem : ByteArray}
    (hp : p2.toNat ≤ mem.size) (hp2sz : p2.toNat + 4 < UInt256.size) :
    config.externalABI.encode? "fess" [.int (Int.ofNat dartRate.toNat)] =
      some ((catBiteFessCalldataMemP p2 dartRate mem).readWithPadding p2.toNat 36) := by
  have hbridge : catBiteFessCalldataMemP p2 dartRate mem = fessCalldataMem p2 dartRate mem := by
    unfold catBiteFessCalldataMemP fessCalldataMem catBiteFessSelMemP fessSelectorMem
      fessSelectorShifted
    have hsel : UInt256.land ⟨4294967295⟩ ⟨1769929592⟩ = UInt256.land ⟨1769929592⟩ ⟨4294967295⟩ := by
      native_decide
    have hoff : (⟨4⟩ + p2).toNat = p2.toNat + 4 := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.add_comm,
        Nat.mod_eq_of_lt hp2sz]
    rw [hsel, hoff]
  rw [hbridge]; exact fessEncode_eq p2 dartRate hp

/-- `2193` (grab succeeded) → `2300`: the grab call-success guard + `dartRate` recompute (`Seg7f`),
the `fess` calldata build (`catBiteTraceFessBuild`), and the `vow.fess(dartRate)` `CALL`
(`RD.catBiteFessCallGen`).  The fess `typedCallViaEVM` coupling threads out. -/
theorem catBiteReachFessRegion {cA gh bl σ σ₀ A I} {g : UInt256}
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
      (o' mem' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (⟨32⟩ + (⟨4⟩ + p2)) :: ⟨1769929592⟩ ::
          UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩) ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        mem' aw' o' (cA'', σ'') k' C'
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
  have hencode : config.externalABI.encode? "fess" [.int (Int.ofNat dartRate.toNat)] =
      some ((catBiteFessCalldataMemP p2 dartRate mem).readWithPadding (p2 : UInt256).toNat 36) :=
    catBiteFessEncode_eq p2 dartRate hpmem (by omega)
  exact RD.catBiteFessCallGen (inOff := p2) (inSize := ⟨36⟩) rd2284 hcodeSize hdepth hencode (by simp)

/-- `2073` → `2193`: the `vat.grab(...)` calldata build (`catBiteTraceGrabBuild`, 7 `MSTORE`s at the
fresh free pointer `p`) and the void `CALL` (`RD.catBiteGrabCallGen`, via `catBiteGrabEncode_eq`).
The grab `typedCallViaEVM` coupling threads out. -/
theorem catBiteReachGrabRegion {cA gh bl σ σ₀ A I} {g : UInt256}
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
      (o' mem' : ByteArray) (A'' aw' : _) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (p + ⟨196⟩) :: ⟨2074820416⟩ ::
          UInt256.land (solcSlotWord σ' I ⟨3⟩) biteAddrMaskWord ::
          dink :: dart :: q :: art :: ink :: iDust :: iSpot :: iRate :: ⟨0⟩ :: urn ::
          biteIlkWord I :: ⟨419⟩ :: catSelWord I :: [])
        mem' aw' o' (cA'', σ'') k' C'
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
  have hencode : config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE (biteIlkWord I)),
       .address (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat),
       .address (AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat),
       .address (AccountAddress.ofNat
         (UInt256.land biteAddrMaskWord (solcSlotWord σ' I ⟨4⟩)).toNat),
       .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))] =
      some ((catBiteGrabCalldataMemP p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
        (solcSlotWord σ' I ⟨4⟩) dink dart mem).readWithPadding (p : UInt256).toNat 196) :=
    catBiteGrabEncode_eq p (biteIlkWord I) urn (UInt256.ofNat I.codeOwner.val)
      (solcSlotWord σ' I ⟨4⟩) dink dart hp96 hpmem (by omega) hthisCanon hdink hdart
  exact RD.catBiteGrabCallGen (inOff := p) (inSize := ⟨196⟩) rd2177 hcodeSize hdepth hencode (by simp)

/-- The `bite` SUCCESS-branch reEquiv: the chained-spine `RDret` (returning `id`) refines the Solm
success body (`catBiteSourceSuccess`), coupled by the final account-map equivalence. -/
theorem catBiteSuccessBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {evmKick : EVM.State}
    {id : UInt256} {cs : Frame}
    (hcode : I.code = catBytecode)
    (hret : RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id))
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hbody :
      ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (biteLocals I) biteTransition.body (.returned cs evmKick (some [bw id])))
    (hcreated : acc.1 = evmKick.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmKick.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc : returnEquiv (UInt256.toByteArray id) (some [bw id]) biteTransition.returnType :=
    returnEquiv_of_encode (uint256ReturnEncoding id)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody hcreated
    hAccountsFinal henc

/-- The full `bite` SUCCESS leaf: the chained-spine `RDret` (returning `id`, on `σ_evm`) refines the
Solm success body run on `σ_solm` (`catBiteSourceSuccess`), coupled by the final account-map
equivalence.  The σ_evm→σ_solm mapping of the 5 calls is done by the caller (`catBiteBody`); this
lemma just runs the source and finishes the reEquiv. -/
theorem catBiteSuccessLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmIlk evmUrn evmGrab evmFess evmLit evmKick : EVM.State}
    {ilksOut urnsOut grabOut fessOut kickOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art id : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = catBytecode)
    (hret : RDret catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc (UInt256.toByteArray id))
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (hsz36 : 36 ≤ I.calldata.size) (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size)
    (hfitArtRate : art.toNat * iRate.toNat < UInt256.size)
    (hfitDunkRoomWad : (biteDunkRoomV I evmUrn).toNat * wadU.toNat < UInt256.size)
    (hfitInkDart : ink.toNat * (biteDartV I evmUrn iRate art).toNat < UInt256.size)
    (hfitDartRate : (biteDartV I evmUrn iRate art).toNat * iRate.toNat < UInt256.size)
    (hfitTabBase :
      (biteDartRateV I evmUrn iRate art).toNat * (biteChopW I evmUrn).toNat < UInt256.size)
    (hfitLitterNew : (biteLitW evmFess).toNat + (biteTabV I evmUrn iRate art).toNat < UInt256.size)
    (hspotPos : 0 < iSpot.toNat) (hratePos : 0 < iRate.toNat) (hartPos : 0 < art.toNat)
    (hmilkChopPos : 0 < (biteChopW I evmUrn).toNat)
    (hunsafe : (ink * iSpot).toNat < (art * iRate).toNat)
    (hlitLtBox : (biteLitW evmUrn).toNat < (biteBoxW evmUrn).toNat)
    (hroomGeDust : iDust.toNat ≤ (biteRoomV evmUrn).toNat)
    (hdartPos : 0 < (biteDartV I evmUrn iRate art).toNat)
    (hdinkPos : 0 < (biteDinkV I evmUrn iRate art ink).toNat)
    (hdartLim : Int.ofNat (biteDartV I evmUrn iRate art).toNat ≤ int256Limit)
    (hdinkLim : Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat ≤ int256Limit)
    (hvatCodeMid :
      0 < (UInt256.ofNat
        ((evmUrn.lookupAccount (biteVatAddr evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hGrabCall :
      typedCallViaEVM config evmUrn (EVM.address (biteVatAddr evmUrn)) "grab" 0
        [biteIlkVal I, biteUrnVal I, .address evmUrn.executionEnv.codeOwner,
          .address (biteVowAddrV evmUrn), .int (-(Int.ofNat (biteDinkV I evmUrn iRate art ink).toNat)),
          .int (-(Int.ofNat (biteDartV I evmUrn iRate art).toNat))] (true, evmGrab, grabOut) true)
    (hGrabDec : config.externalABI.decode? "grab" grabOut = some [])
    (hvowCode :
      0 < (UInt256.ofNat
        ((evmGrab.lookupAccount (biteVowAddrV evmGrab)).option 0 (fun acc => acc.code.size))).toNat)
    (hFessCall :
      typedCallViaEVM config evmGrab (EVM.address (biteVowAddrV evmGrab)) "fess" 0
        [bw (biteDartRateV I evmUrn iRate art)] (true, evmFess, fessOut) true)
    (hFessDec : config.externalABI.decode? "fess" fessOut = some [])
    (hLitStore :
      storageLocStore evmFess (wordLoc ⟨6⟩)
        (.int (Int.ofNat (biteLitterNewV I evmUrn evmFess iRate art).toNat)) = some evmLit)
    (hflipCode :
      0 < (UInt256.ofNat
        ((evmLit.lookupAccount (biteFlipAddrV I evmUrn)).option 0 (fun acc => acc.code.size))).toNat)
    (hKickCall :
      typedCallViaEVM config evmLit (EVM.address (biteFlipAddrV I evmUrn)) "kick" 0
        [biteUrnVal I, .address (biteVowAddrV evmLit), bw (biteTabV I evmUrn iRate art),
          bw (biteDinkV I evmUrn iRate art ink), .int 0] (true, evmKick, kickOut) true)
    (hKickDec : config.externalABI.decode? "kick" kickOut = some [bw id])
    (hcreated : acc.1 = evmKick.createdAccounts)
    (hAccountsFinal : accountMapEquiv acc.2 evmKick.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody := catBiteSourceSuccess (σ := σ_solm) hsz36 hwv hvatCode0 hIlksCall hIlksDec
    hvatCodeIlk hUrnsCall hUrnsDec hlive hfitInkSpot hfitArtRate hfitDunkRoomWad hfitInkDart
    hfitDartRate hfitTabBase hfitLitterNew hspotPos hratePos hartPos hmilkChopPos hunsafe hlitLtBox
    hroomGeDust hdartPos hdinkPos hdartLim hdinkLim hvatCodeMid hGrabCall hGrabDec hvowCode hFessCall
    hFessDec hLitStore hflipCode hKickCall hKickDec
  exact catBiteSuccessBodyCore hcode hret hdispatch hdecode hbody hcreated hAccountsFinal

/-! ## σ_evm → σ_solm call-mapping lemmas (thread `EVMStateEquiv` across the 5 external calls) -/

/-- Shift the caller substate of a value-`0` typed call (local copy of the Vow lemma, needed to
reconcile `typedCallViaEVM_accountMapEquiv`'s equal-substate requirement with the σ_solm state). -/
theorem biteTypedCallZeroSetSubstate {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A'
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

/-- Map the ilks `STATICCALL` (from `initState`) to the σ_solm side, producing the σ_solm-side call
and the `EVMStateEquiv` coupling for the next call. -/
theorem catBiteMapIlksCall {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tgt : EVM.Address} {args : List Value} {evmIlk : EVM.State} {ilksOut : ByteArray} {name : Ident}
    {z : Bool} {perm : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      tgt name 0 args (z, evmIlk, ilksOut) perm) :
    ∃ (σ_solm' : AccountMap) (A_solm' : Substate),
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) tgt name 0 args
        (z, { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_solm', substate := A_solm', createdAccounts := evmIlk.createdAccounts },
          ilksOut) perm
    ∧ EVMStateEquiv evmIlk
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_solm', substate := A_solm', createdAccounts := evmIlk.createdAccounts } :=
  typedCallViaEVM_initState_EVMStateEquiv hcall
    (by rw [typedCallViaEVM_executionEnv_eq hcall]; rfl) hAccounts

/-- Map an intermediate-state (post-ilks) value-`0` call to the σ_solm side, threading the
`EVMStateEquiv` coupling.  Serves the urns/grab/fess/kick calls (all from `{initState … with …}`). -/
theorem catBiteMapCall {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {σ_x_evm σ_x_solm : AccountMap} {A_x_evm A_x_solm : Substate}
    {cA_x : Batteries.RBSet AccountAddress compare}
    {tgt : EVM.Address} {name : Ident} {args : List Value} {z perm : Bool}
    {evm'_evm : EVM.State} {out : ByteArray}
    (hState : EVMStateEquiv
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_x_evm, substate := A_x_evm, createdAccounts := cA_x }
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_x_solm, substate := A_x_solm, createdAccounts := cA_x })
    (hcall : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_x_evm, substate := A_x_evm, createdAccounts := cA_x }
      tgt name 0 args (z, evm'_evm, out) perm)
    (hdepthNe : I.depth ≠ 1024) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_x_solm, substate := A_x_solm, createdAccounts := cA_x }
        tgt name 0 args
        (z, { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm, substate := A'_solm,
              createdAccounts := evm'_evm.createdAccounts }, out) perm
    ∧ EVMStateEquiv evm'_evm
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'_solm, substate := A'_solm,
            createdAccounts := evm'_evm.createdAccounts } := by
  have hdepthNeBase :
      ({ initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_x_solm, substate := A_x_evm,
          createdAccounts := cA_x } : EVM.State).executionEnv.depth ≠ 1024 := by
    simpa [initState] using hdepthNe
  obtain ⟨σ'_solm, A'_solm0, hcallBase, hAcc'⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_x_solm, substate := A_x_evm, createdAccounts := cA_x })
      hcall (by simpa using hState.accountMap) (by simp [initState]) rfl
      (by simp [initState]) (by simp [initState]) (by simp) (by simpa using hState.executionEnv.symm)
  obtain ⟨A'_solm, hcallSolm⟩ := biteTypedCallZeroSetSubstate hcallBase hdepthNeBase A_x_solm
  refine ⟨σ'_solm, A'_solm, ?_, ?_, ?_, ?_⟩
  · simpa using hcallSolm
  · rw [typedCallViaEVM_executionEnv_eq hcall]
    simpa [initState] using hState.executionEnv
  · rfl
  · simpa using hAcc'

/-! ## Short-calldata revert (`size < 68`) -/

/-- The `bite` argument decode fails for calldata shorter than `4 + 64 = 68` bytes. -/
theorem catBiteDecode_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
      (transitionSignature biteTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "urn"] [bytes32, addr] I.calldata = none
  rw [decodeCalldataWithMode]
  show decodeCalldata ["ilk", "urn"] [abiBytes32, .elem .address] I.calldata
    DecodeMode.legacySolc05 = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, .elem .address] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega : (I.calldata.toList.drop 4).length < 64)]

/-- Calldata size `< 68` → the length check reverts, matched to the Solm decode failure. -/
theorem catBiteShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach := catReachBiteEntry (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨375⟩) (ret := ⟨419⟩)
    (decoded := ⟨397⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_bite hsel)
    (catBiteDecode_none_short hsz4 hshort)

end Benchmarks.Dss.Cat
