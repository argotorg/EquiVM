import Benchmarks.Dss.Vow.FlapKickBody
import Benchmarks.Dss.Vow.FlopBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` top-level runtime helper facts -/

theorem flapFlapperTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I := by
  simp [vowAddressReturnWord, vowSlotWord_accountMapEquiv hAccounts ⟨2⟩]

theorem flapFlapperCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (vowAddressReturnWord ⟨2⟩ σ I) ≠
        ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (vowAddressReturnWord ⟨2⟩ τ I) ≠
      ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨2⟩ σ I)
  have htarget : vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I :=
    flapFlapperTargetWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem flapFlapperCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (vowAddressReturnWord ⟨2⟩ σ I) =
        ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (vowAddressReturnWord ⟨2⟩ τ I) =
      ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (vowAddressReturnWord ⟨2⟩ σ I)
  have htarget : vowAddressReturnWord ⟨2⟩ σ I = vowAddressReturnWord ⟨2⟩ τ I :=
    flapFlapperTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem vowFlapSin0CallDepthLimitBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hcodeSizeSinNE :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) ≠
        ⟨0⟩)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hdepthEq : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd937⟩ :=
    RD.vowFlapSin0CallDepthLimit hreach hcodeSizeSinNE hdepthEq
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let A_sin := (evm0.addAccessedAccount (EVM.address (kissVatAddress σ_solm I))).substate
  have hcallSinDepth :
      typedCallViaEVM config evm0
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (false,
          { evm0 with accountMap := σ_solm, substate := A_sin, createdAccounts := cA },
          ByteArray.empty) false := by
    simpa [evm0, A_sin, initState] using
      (callNotMade_depthLimit (cfg := config) (evm := evm0)
        (tgt := EVM.address (kissVatAddress σ_solm I)) (name := "sin")
        (args := [.address I.codeOwner]) (callPerm := false)
        (initialHealSinEncode_eq I) (by simpa [evm0, initState] using hdepthEq))
  exact vowFlapSin0CallFailureBodyCore (acc := (cA, σ_evm))
    (evmSin := { evm0 with accountMap := σ_solm, substate := A_sin, createdAccounts := cA })
    (outSin := ByteArray.empty) hcode hwv hdispatch hdecode rd937
    (by decide +native) hvatCodeSolm hcallSinDepth

theorem RD.vowFlapSin0PostCallDecodeOk
    {cA gh bl σ σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {outSin : ByteArray} {k C : ℕ}
    (rd937 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
      (UInt256.ofNat 6) outSin acc k C)
    (ho32 : 32 ≤ outSin.size) (hosz : outSin.size < UInt256.size) :
    let vatSin0 := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨978⟩
      (vatSin0 :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32)
      (UInt256.ofNat 6) outSin acc k' C' := by
  intro vatSin0
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd937Write := rd937
  rw [hmin] at rd937Write
  obtain ⟨_, _, rd955⟩ :=
    RD.vowFlapSin0CallSuccessToDecode rd937Write (by simp)
  have hmem :
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size = 164 :=
    initialHealSinWrite_size I outSin 32 (by omega) ho32
  have hread64 :
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    initialHealSinWrite_read64 I outSin 32 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmem]
      decide +native
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      initialHealSinWrite_read128_32 I outSin ho32]
  obtain ⟨k', C', rd978Raw⟩ :=
    RD.vowFlapSin0ReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)))
      rd955 ho32 hosz hmload64 hmload128
  exact ⟨k', C', by simpa [vatSin0] using rd978Raw⟩

theorem RD.vowFlapDai0PostCallDecodeOk
    {cA gh bl σ σ₀ A I} {g sel target surplusNeed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outDai : ByteArray} {k C : ℕ}
    (rd1072 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
      (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: target :: surplusNeed ::
        ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outDai.write 0 (vatDaiCalldataMem I mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
      (UInt256.ofNat 6) outDai acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outDai.size) (hosz : outDai.size < UInt256.size) :
    let vatDai := UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1113⟩
      (vatDai :: surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 32)
      (UInt256.ofNat 6) outDai acc k' C' := by
  intro vatDai
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1072Write := rd1072
  rw [hmin] at rd1072Write
  obtain ⟨_, _, rd1090⟩ :=
    RD.vowFlapDai0CallSuccessToDecode rd1072Write (by simp)
  have hmemWrite :
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size = 164 :=
    vatDaiWrite_size I outDai 32 hmem (by omega) ho32
  have hread64Write :
      (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    vatDaiWrite_read64 I outDai 32 hmem hread64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outDai.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (outDai.write 0 (vatDaiCalldataMem I mem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmemWrite]
      decide +native
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      vatDaiWrite_read128_32 I outDai hmem ho32]
  obtain ⟨k', C', rd1113Raw⟩ :=
    RD.vowFlapDai0ReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32)))
      rd1090 ho32 hosz hmload64 hmload128
  exact ⟨k', C', by simpa [vatDai] using rd1113Raw⟩

theorem RD.vowFlapSin1PostCallDecodeOk
    {cA gh bl σ σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outSin1 : ByteArray} {k C : ℕ}
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin1.write 0 (healSinCalldataMem I mem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin1.size)).toNat)
      (UInt256.ofNat 6) outSin1 acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (ho32 : 32 ≤ outSin1.size) (hosz : outSin1.size < UInt256.size) :
    let vatSin1 := UInt256.ofNat (fromByteArrayBigEndian (outSin1.extract 0 32))
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin1 :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin1.write 0 (healSinCalldataMem I mem) 128 32)
      (UInt256.ofNat 6) outSin1 acc k' C' := by
  intro vatSin1
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin1.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1277Write := rd1277
  rw [hmin] at rd1277Write
  obtain ⟨_, _, rd1295⟩ :=
    RD.vowFlapSin1CallSuccessToDecode rd1277Write (by simp)
  have hmemWrite :
      (outSin1.write 0 (healSinCalldataMem I mem) 128 32).size = 164 :=
    healSinWrite_size I mem outSin1 32 hmem (by omega) ho32
  have hread64Write :
      (outSin1.write 0 (healSinCalldataMem I mem) 128 32).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    healSinWrite_read64 I mem outSin1 32 hmem hread64 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin1.write 0 (healSinCalldataMem I mem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin1.write 0 (healSinCalldataMem I mem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (outSin1.write 0 (healSinCalldataMem I mem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin1.write 0 (healSinCalldataMem I mem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outSin1.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (outSin1.write 0 (healSinCalldataMem I mem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmemWrite]
      decide +native
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      healSinWrite_read128_32 I mem outSin1 hmem ho32]
  obtain ⟨k', C', rd1318Raw⟩ :=
    RD.vowFlapSin1ReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outSin1.extract 0 32)))
      rd1295 ho32 hosz hmload64 hmload128
  exact ⟨k', C', by simpa [vatSin1] using rd1318Raw⟩

/-- Public `flap()` wrapper prefix through the first `vat.sin` and surplus arithmetic.

The continuation receives the proved EVM state at the first `vat.dai(address(this))` call
site, together with the source-side call/decode/storage facts needed for the rest of the
`flap()` body. -/
theorem vowFlapBodyPrefix
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_sin : Batteries.RBSet AccountAddress compare} {σ_sin : AccountMap}
        {evmSinSolm : EVM.State} {outSin memSin : ByteArray} {k993 C993 : ℕ}
        {vatSin0 BumpVal surplus0 HumpVal surplusNeed : UInt256},
        memSin = outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32 →
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
          (surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
          memSin (UInt256.ofNat 6) outSin (cA_sin, σ_sin) k993 C993 →
        memSin.size = 164 →
        memSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        0 < (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (true, evmSinSolm, outSin) false →
        config.externalABI.decode? "sin" outSin =
          some [.int (Int.ofNat vatSin0.toNat)] →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨10⟩ =
          BumpVal →
        BumpVal = vowSlotWord ⟨10⟩ σ_solm I →
        surplus0 = vatSin0 + BumpVal →
        vatSin0.toNat + BumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨11⟩ =
          HumpVal →
        surplusNeed = surplus0 + HumpVal →
        surplus0.toNat + HumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        I.depth.val < 1024 →
        evmSinSolm.createdAccounts = cA_sin →
        evmSinSolm.σ₀ = σ₀ →
        evmSinSolm.blocks = bl →
        evmSinSolm.genesisBlockHeader = gh →
        evmSinSolm.executionEnv = I →
        accountMapEquiv σ_sin evmSinSolm.accountMap →
        (∀ slot : UInt256,
          Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner slot =
            vowSlotWord slot σ_sin I) →
        (∀ slot : UInt256,
          vowSlotWord slot evmSinSolm.accountMap I = vowSlotWord slot σ_solm I) →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some flapTransition :=
    vowDispatch_flap hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flap hsz4
  have hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [vowSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C :=
    vowReachFlapBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  by_cases hcodeSizeSin :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩
  · exact vowFlapVatSin0NoCodeBodyCore hcode hwv hdispatch hdecode hreach hAccounts
      hcodeSizeSin
  have hcodeSizeSinNE :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) ≠ ⟨0⟩ :=
    hcodeSizeSin
  have hcodeSizeSinSolmNE :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) ≠
        ⟨0⟩ :=
    kissDaiCodeSize_ne_accountMapEquiv hAccounts hcodeSizeSinNE
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    kissVatCode_pos_of_codeSize_ne (cA := cA) (gh := gh) (bl := bl)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSinSolmNE
  have hVatAddrOrig : kissVatAddress σ_evm I = kissVatAddress σ_solm I :=
    kissVatAddress_accountMapEquiv hAccounts
  by_cases hdepthLt : I.depth.val < 1024
  · obtain ⟨cA_sin, σ_sin, zSin, outSin, A_sin, k937, C937, rd937,
        hcallSinEvmRaw, hoszSin⟩ :=
      RD.vowFlapSin0PostCall hreach hcodeSizeSinNE hdepthLt
    cases zSin
    · have hcallSinEvm :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "sin" 0 [.address I.codeOwner]
            (false,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_sin
                  substate := A_sin
                  createdAccounts := cA_sin },
              outSin) false := by
        simpa using hcallSinEvmRaw
      obtain ⟨σ_sin_solm, A_sin_solm, hcallSinSolmRaw, _hStateSin⟩ :=
        typedCallViaEVM_initState_EVMStateEquiv hcallSinEvm
          (by simp [initState]) hAccounts
      let evmSinSolm :=
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin_solm
            substate := A_sin_solm
            createdAccounts := cA_sin }
      have hcallSinSolm :
          typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
            (false, evmSinSolm, outSin) false := by
        simpa [evmSinSolm, hVatAddrOrig] using hcallSinSolmRaw
      exact vowFlapSin0CallFailureBodyCore (acc := (cA_sin, σ_sin))
        hcode hwv hdispatch hdecode (by simpa using rd937) hoszSin hvatCodeSolm
        hcallSinSolm
    · have rd937True : RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨937⟩
          (⟨1⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord σ_evm I ::
            ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
          (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
          (UInt256.ofNat 6) outSin (cA_sin, σ_sin) k937 C937 := by
        simpa using rd937
      have hcallSinEvm :
          typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_evm I)) "sin" 0 [.address I.codeOwner]
            (true,
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ_sin
                  substate := A_sin
                  createdAccounts := cA_sin },
              outSin) false := by
        simpa using hcallSinEvmRaw
      obtain ⟨σ_sin_solm, A_sin_solm, hcallSinSolmRaw, hStateSinRaw⟩ :=
        typedCallViaEVM_initState_EVMStateEquiv hcallSinEvm
          (by simp [initState]) hAccounts
      let evmSinEvm :=
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin
            substate := A_sin
            createdAccounts := cA_sin }
      let evmSinSolm :=
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_sin_solm
            substate := A_sin_solm
            createdAccounts := cA_sin }
      have hcallSinSolm :
          typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
            (true, evmSinSolm, outSin) false := by
        simpa [evmSinSolm, hVatAddrOrig] using hcallSinSolmRaw
      have hStateSin : EVMStateEquiv evmSinEvm evmSinSolm := by
        simpa [evmSinEvm, evmSinSolm] using hStateSinRaw
      by_cases ho32Sin : 32 ≤ outSin.size
      · let vatSin0 : UInt256 :=
          UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))
        have hdecSin :
            config.externalABI.decode? "sin" outSin =
              some [.int (Int.ofNat vatSin0.toNat)] := by
          simpa [vatSin0] using vatSinDecode_ok (o := outSin) ho32Sin
        have hslotLoad : ∀ slot : UInt256,
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner slot =
              vowSlotWord slot σ_sin I := by
          intro slot
          have h := hStateSin.storageLoad_codeOwner slot
          rw [← h]
          simp [evmSinEvm, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, vowSlotWord, solcSlotWord]
        let BumpVal : UInt256 := vowSlotWord ⟨10⟩ σ_sin I
        let HumpVal : UInt256 := vowSlotWord ⟨11⟩ σ_sin I
        have hBumpLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨10⟩ =
              BumpVal := by
          simpa [BumpVal] using hslotLoad ⟨10⟩
        obtain ⟨_, _, rd978⟩ :=
          RD.vowFlapSin0PostCallDecodeOk rd937True ho32Sin hoszSin
        by_cases hover0 : UInt256.size ≤ vatSin0.toNat + BumpVal.toNat
        · exact vowFlapSurplus0AddOverflowBodyCore (acc := (cA_sin, σ_sin))
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode
            (by simpa [vatSin0] using rd978) hvatCodeSolm hcallSinSolm hdecSin
            hBumpLoad (by simp [BumpVal]) hover0
        have hfit0 : vatSin0.toNat + BumpVal.toNat < UInt256.size := by
          omega
        let surplus0 : UInt256 := vatSin0 + BumpVal
        obtain ⟨_, _, rd985⟩ :=
          RD.vowFlapSurplus0AddSuccess (by simpa [vatSin0] using rd978)
            (by simpa [BumpVal] using hfit0)
        have hHumpLoad :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨11⟩ =
              HumpVal := by
          simpa [HumpVal] using hslotLoad ⟨11⟩
        by_cases hoverNeed : UInt256.size ≤ surplus0.toNat + HumpVal.toNat
        · exact vowFlapSurplusNeedAddOverflowBodyCore (acc := (cA_sin, σ_sin))
            (evmSin := evmSinSolm) hcode hwv hdispatch hdecode
            (by simpa [surplus0, BumpVal] using rd985) hvatCodeSolm hcallSinSolm
            hdecSin hBumpLoad rfl hfit0 hHumpLoad (by simp [HumpVal]) hoverNeed
        have hfitNeed : surplus0.toNat + HumpVal.toNat < UInt256.size := by
          omega
        let surplusNeed : UInt256 := surplus0 + HumpVal
        obtain ⟨_, _, rd993⟩ :=
          RD.vowFlapSurplusNeedAddSuccess (by simpa [surplus0, BumpVal] using rd985)
            (by simpa [HumpVal] using hfitNeed)
        let memSin := outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32
        have hmemSin : memSin.size = 164 := by
          simpa [memSin] using initialHealSinWrite_size I outSin 32 (by omega) ho32Sin
        have hread64Sin :
            memSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memSin] using initialHealSinWrite_read64 I outSin 32 (by omega) ho32Sin
        have hAccountsSin : accountMapEquiv σ_sin evmSinSolm.accountMap := by
          simpa [evmSinEvm] using hStateSin.accountMap
        have hSlotSinSolm : ∀ slot : UInt256,
            vowSlotWord slot σ_sin I = vowSlotWord slot evmSinSolm.accountMap I := by
          intro slot
          simpa using vowSlotWord_accountMapEquiv (I := I) hAccountsSin slot
        have hSlotSolmStatic : ∀ slot : UInt256,
            vowSlotWord slot evmSinSolm.accountMap I = vowSlotWord slot σ_solm I := by
          intro slot
          have h := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
            (cfg := config) (σ := σ_solm)
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (evm' := evmSinSolm) (slot := slot) (default := ⟨0⟩)
            (hAccounts := by simpa [initState] using accountMapEquiv_refl σ_solm)
            hcallSinSolm
          simpa [evmSinSolm, initState, vowSlotWord, solcSlotWord] using h
        have hBumpSolm : BumpVal = vowSlotWord ⟨10⟩ σ_solm I := by
          simpa [BumpVal] using Eq.trans (hSlotSinSolm ⟨10⟩) (hSlotSolmStatic ⟨10⟩)
        have hvatLoadSin :
            Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
              vowSlotWord ⟨1⟩ σ_solm I := by
          rw [hslotLoad, hSlotSinSolm, hSlotSolmStatic]
        have hcreatedSin : evmSinSolm.createdAccounts = cA_sin := by
          simp [evmSinSolm]
        have hσ0Sin : evmSinSolm.σ₀ = σ₀ := by
          simp [evmSinSolm, initState]
        have hblocksSin : evmSinSolm.blocks = bl := by
          simp [evmSinSolm, initState]
        have hgenesisSin : evmSinSolm.genesisBlockHeader = gh := by
          simp [evmSinSolm, initState]
        have henvSin : evmSinSolm.executionEnv = I := by
          simp [evmSinSolm, initState]
        exact cont (memSin := memSin) (evmSinSolm := evmSinSolm)
          (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
          (HumpVal := HumpVal) (surplusNeed := surplusNeed) rfl
          (by simpa [memSin, surplusNeed, surplus0, HumpVal, BumpVal] using rd993)
          hmemSin hread64Sin hvatCodeSolm hcallSinSolm hdecSin hBumpLoad
          hBumpSolm rfl hfit0 hHumpLoad rfl hfitNeed hvatLoadSin hdepthLt hcreatedSin
          hσ0Sin hblocksSin hgenesisSin henvSin hAccountsSin hslotLoad
          hSlotSolmStatic
      · have hshortRet : outSin.size < 32 := Nat.lt_of_not_ge ho32Sin
        have hminShort :
            (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat =
              outSin.size :=
          kissDaiMin32_toNat_of_lt hshortRet
        have rd937Short := rd937True
        rw [hminShort] at rd937Short
        obtain ⟨_, _, rd955⟩ :=
          RD.vowFlapSin0CallSuccessToDecode rd937Short (by simp)
        let memShort := outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size
        have hmemShort :
            memShort.size = 164 := by
          simpa [memShort] using
            initialHealSinWrite_size I outSin outSin.size (by omega) (by omega)
        have hread64Short :
            memShort.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          simpa [memShort] using
            initialHealSinWrite_read64 I outSin outSin.size (by omega) (by omega)
        have hmload64Short :
            (if (⟨64⟩ : UInt256).toNat ≥
                  memShort.size
                ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat
               (fromByteArrayBigEndian
                (memShort.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
              ⟨128⟩ :=
          mloadFreePtrValue (by rw [hmemShort]; decide) (by decide) hread64Short
        have hrev :=
          RD.vowFlapSin0ReturnDecodeShortReverts rd955 hshortRet hoszSin hmload64Short
        have hdecSin : config.externalABI.decode? "sin" outSin = none :=
          vatSinDecode_none_short hshortRet
        have hbody := vowFlapSourceVatSin0DecodeRevert (cA := cA) (gh := gh)
          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmSin := evmSinSolm) (outSin := outSin)
          hwv hvatCodeSolm hcallSinSolm hdecSin
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdepthEq : I.depth = 1024 := by
      apply Fin.ext
      have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
      omega
    exact vowFlapSin0CallDepthLimitBody hcode hwv hdispatch hdecode hreach
      hcodeSizeSinNE hvatCodeSolm hdepthEq

/-- Public `flap()` wrapper prefix through the first `vat.dai(address(this))` call.

The continuation receives the proved EVM state at the second `vat.sin(address(this))` call site. -/
theorem vowFlapBodyToSin1
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_dai : Batteries.RBSet AccountAddress compare} {σ_dai : AccountMap}
        {evmSinSolm evmDaiSolm : EVM.State} {outSin outDai memSin memDai : ByteArray}
        {k1190 C1190 : ℕ}
        {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai : UInt256},
        memDai = outDai.write 0 (vatDaiCalldataMem I memSin) 128 32 →
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1190⟩
          (⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
          memDai (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k1190 C1190 →
        memSin.size = 164 →
        memSin.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        memDai.size = 164 →
        memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        0 < (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (true, evmSinSolm, outSin) false →
        config.externalABI.decode? "sin" outSin =
          some [.int (Int.ofNat vatSin0.toNat)] →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨10⟩ =
          BumpVal →
        BumpVal = vowSlotWord ⟨10⟩ σ_solm I →
        surplus0 = vatSin0 + BumpVal →
        vatSin0.toNat + BumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨11⟩ =
          HumpVal →
        surplusNeed = surplus0 + HumpVal →
        surplus0.toNat + HumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        0 < (UInt256.ofNat
          ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmSinSolm (EVM.address (kissVatAddress σ_solm I)) "dai" 0
          [.address I.codeOwner] (true, evmDaiSolm, outDai) false →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat vatDai.toNat)] →
        surplusNeed.toNat ≤ vatDai.toNat →
        Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        I.depth.val < 1024 →
        evmDaiSolm.createdAccounts = cA_dai →
        evmDaiSolm.σ₀ = σ₀ →
        evmDaiSolm.blocks = bl →
        evmDaiSolm.genesisBlockHeader = gh →
        evmDaiSolm.executionEnv = I →
        accountMapEquiv σ_dai evmDaiSolm.accountMap →
        (∀ slot : UInt256,
          Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner slot =
            vowSlotWord slot σ_dai I) →
        (∀ slot : UInt256,
          vowSlotWord slot evmDaiSolm.accountMap I = vowSlotWord slot σ_solm I) →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some flapTransition :=
    vowDispatch_flap hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flap hsz4
  refine vowFlapBodyPrefix
    (fun {cA_sin} {σ_sin} {evmSinSolm} {outSin} {memSin} {k993} {C993}
        {vatSin0} {BumpVal} {surplus0} {HumpVal} {surplusNeed}
        hmemSinDef rd993 hmemSin hread64Sin hvatCodeSolm hcallSinSolm hdecSin
        hBumpLoad hBumpSolm hsurplus0 hfit0 hHumpLoad hsurplusNeed hfitNeed hvatLoadSin
        hdepthLt hcreatedSin hσ0Sin hblocksSin hgenesisSin henvSin hAccountsSin hslotLoad
        hSlotSinStatic =>
      ?_) hcode hsize hperm hwv hsel hAccounts
  have hslotVatSin :
      vowSlotWord ⟨1⟩ σ_sin I = vowSlotWord ⟨1⟩ σ_solm I := by
    rw [← hslotLoad ⟨1⟩]
    exact hvatLoadSin
  have hslotVatAcc :
      vowSlotWord ⟨1⟩ evmSinSolm.accountMap I = vowSlotWord ⟨1⟩ σ_solm I := by
    calc
      vowSlotWord ⟨1⟩ evmSinSolm.accountMap I = vowSlotWord ⟨1⟩ σ_sin I := by
        exact (vowSlotWord_accountMapEquiv (I := I) hAccountsSin ⟨1⟩).symm
      _ = vowSlotWord ⟨1⟩ σ_solm I := hslotVatSin
  have hTargetSinSolm :
      kissDaiTargetWord evmSinSolm.accountMap I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hslotVatAcc]
  have haddrDai :
      kissVatAddress σ_solm I =
        AccountAddress.ofUInt256 (kissDaiTargetWord evmSinSolm.accountMap I) := by
    rw [hTargetSinSolm]
    exact kissVatAddress_eq_daiTarget_account σ_solm I
  have hVatAddrSin : kissVatAddress σ_sin I = kissVatAddress σ_solm I := by
    apply Fin.ext
    simp [kissVatAddress, vowAddressReturnWord, hslotVatSin]
  by_cases hcodeSizeDai :
      Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) =
        ⟨0⟩
  · have hcodeSizeDaiSolm :
        Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
            (kissDaiTargetWord evmSinSolm.accountMap I) = ⟨0⟩ :=
      kissDaiCodeSize_zero_accountMapEquiv hAccountsSin hcodeSizeDai
    have hvatNoCodeDai :
        (UInt256.ofNat
          ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_zero_lookup_code_zero
          (σ := evmSinSolm.accountMap)
          (target := kissDaiTargetWord evmSinSolm.accountMap I)
          (addr := kissVatAddress σ_solm I) haddrDai hcodeSizeDaiSolm
    exact vowFlapDai0NoCodeBodyCore (acc := (cA_sin, σ_sin))
      (evmSin := evmSinSolm) hcode hwv hdispatch hdecode rd993 hmemSin hread64Sin
      hcodeSizeDai hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0
      hHumpLoad hsurplusNeed hfitNeed hvatLoadSin hvatNoCodeDai
  have hcodeSizeDaiNE :
      Reasoning.Theory.extCodeSizeWord σ_sin (kissDaiTargetWord σ_sin I) ≠
        ⟨0⟩ :=
    hcodeSizeDai
  have hcodeSizeDaiSolmNE :
      Reasoning.Theory.extCodeSizeWord evmSinSolm.accountMap
          (kissDaiTargetWord evmSinSolm.accountMap I) ≠ ⟨0⟩ :=
    kissDaiCodeSize_ne_accountMapEquiv hAccountsSin hcodeSizeDaiNE
  have hvatCodeDai :
      0 < (UInt256.ofNat
        ((evmSinSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmSinSolm.accountMap)
        (target := kissDaiTargetWord evmSinSolm.accountMap I)
        (addr := kissVatAddress σ_solm I) haddrDai hcodeSizeDaiSolmNE
  obtain ⟨cA_dai, σ_dai, zDai, outDai, A_dai, k1072, C1072, rd1072,
      hcallDaiEvmRaw, hoszDai⟩ :=
    RD.vowFlapDai0PostCall rd993 hmemSin hread64Sin hcodeSizeDaiNE hdepthLt
  let evmDaiEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_sin
        createdAccounts := cA_sin }
  let evmDaiEvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_dai
        substate := A_dai
        createdAccounts := cA_dai }
  have hcallDaiEvm :
      typedCallViaEVM config evmDaiEvmIn
        (EVM.address (kissVatAddress σ_sin I)) "dai" 0 [.address I.codeOwner]
        (zDai, evmDaiEvmOut, outDai) false := by
    simpa [evmDaiEvmIn, evmDaiEvmOut] using hcallDaiEvmRaw
  let evmDaiSolmBase := { evmSinSolm with substate := evmDaiEvmIn.substate }
  have hcallCreated :
      evmDaiSolmBase.createdAccounts = evmDaiEvmIn.createdAccounts := by
    simpa [evmDaiSolmBase, evmDaiEvmIn] using hcreatedSin
  have hcallEnv : evmDaiSolmBase.executionEnv = evmDaiEvmIn.executionEnv := by
    simpa [evmDaiSolmBase, evmDaiEvmIn, initState] using henvSin
  obtain ⟨σ_dai_solm, A_dai_solm0, hcallDaiSolmBase, hAccountsDai⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmDaiSolmBase)
      hcallDaiEvm hAccountsSin
      (by simpa [evmDaiEvmIn, evmDaiSolmBase, initState] using hσ0Sin.symm)
      hcallCreated
      (by simpa [evmDaiEvmIn, evmDaiSolmBase, initState] using hgenesisSin)
      (by simpa [evmDaiEvmIn, evmDaiSolmBase, initState] using hblocksSin)
      (by simp [evmDaiSolmBase])
      hcallEnv
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBase : evmDaiSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmDaiSolmBase, henvSin] using hdepthNeI
  obtain ⟨A_dai_solm, hcallDaiSolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallDaiSolmBase hdepthNeBase
      evmSinSolm.substate
  let evmDaiSolm :=
    { evmSinSolm with
        accountMap := σ_dai_solm
        substate := A_dai_solm
        createdAccounts := cA_dai }
  have hcallDaiSolm :
      typedCallViaEVM config evmSinSolm
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (zDai, evmDaiSolm, outDai) false := by
    simpa [evmDaiSolm, evmDaiSolmBase, hVatAddrSin] using hcallDaiSolmRaw
  cases zDai
  · exact vowFlapDai0CallFailureBodyCore (acc := (cA_dai, σ_dai))
      (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
      hcode hwv hdispatch hdecode (by simpa using rd1072) hoszDai hvatCodeSolm
      hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0 hHumpLoad hsurplusNeed
      hfitNeed hvatLoadSin hvatCodeDai (by simpa using hcallDaiSolm)
  · have rd1072True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1072⟩
        (⟨1⟩ :: ⟨164⟩ :: ⟨1814410054⟩ :: kissDaiTargetWord (cA_sin, σ_sin).2 I ::
          surplusNeed :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
        (outDai.write 0 (vatDaiCalldataMem I memSin) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outDai.size)).toNat)
        (UInt256.ofNat 6) outDai (cA_dai, σ_dai) k1072 C1072 := by
      simpa using rd1072
    have hcallDaiSolmTrue :
        typedCallViaEVM config evmSinSolm
          (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
          (true, evmDaiSolm, outDai) false := by
      simpa using hcallDaiSolm
    by_cases ho32Dai : 32 ≤ outDai.size
    · let vatDai : UInt256 :=
        UInt256.ofNat (fromByteArrayBigEndian (outDai.extract 0 32))
      have hdecDai :
          config.externalABI.decode? "dai" outDai =
            some [.int (Int.ofNat vatDai.toNat)] := by
        simpa [vatDai] using kissDaiDecode_ok (o := outDai) ho32Dai
      let memDai := outDai.write 0 (vatDaiCalldataMem I memSin) 128 32
      have hmemDai : memDai.size = 164 := by
        simpa [memDai] using vatDaiWrite_size I outDai 32 hmemSin (by omega) ho32Dai
      have hread64Dai :
          memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memDai] using
          vatDaiWrite_read64 I outDai 32 hmemSin hread64Sin (by omega) ho32Dai
      obtain ⟨_, _, rd1113⟩ :=
        RD.vowFlapDai0PostCallDecodeOk rd1072True hmemSin hread64Sin ho32Dai
          hoszDai
      by_cases hinsuff : vatDai.toNat < surplusNeed.toNat
      · exact vowFlapDai0InsufficientSurplusBodyCore (acc := (cA_dai, σ_dai))
          (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
          hcode hwv hdispatch hdecode (by simpa [vatDai] using rd1113)
          hmemDai hread64Dai
          hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0 hHumpLoad
          hsurplusNeed hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolmTrue hdecDai
          hinsuff
      have henough : surplusNeed.toNat ≤ vatDai.toNat := by
        omega
      obtain ⟨_, _, rd1190⟩ :=
        RD.vowFlapDai0Enough (by simpa [vatDai] using rd1113) henough
      have hStateDai : EVMStateEquiv evmDaiEvmOut evmDaiSolm := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [evmDaiEvmOut, evmDaiSolm, initState] using henvSin.symm
        · simp [evmDaiEvmOut, evmDaiSolm]
        · simpa [evmDaiEvmOut, evmDaiSolm] using hAccountsDai
      have hslotDaiLoad : ∀ slot : UInt256,
          Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner slot =
            vowSlotWord slot σ_dai I := by
        intro slot
        have h := hStateDai.storageLoad_codeOwner slot
        rw [← h]
        simp [evmDaiEvmOut, initState, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, vowSlotWord, solcSlotWord]
      have hAccountsDaiOut : accountMapEquiv σ_dai evmDaiSolm.accountMap := by
        simpa [evmDaiEvmOut, evmDaiSolm] using hAccountsDai
      have henvDai : evmDaiSolm.executionEnv = I := by
        simpa [evmDaiSolm] using henvSin
      have hSlotDaiStatic : ∀ slot : UInt256,
          vowSlotWord slot evmDaiSolm.accountMap I = vowSlotWord slot σ_solm I := by
        intro slot
        have hstatic := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
          (cfg := config) (σ := evmSinSolm.accountMap)
          (evm := evmSinSolm) (evm' := evmDaiSolm) (slot := slot) (default := ⟨0⟩)
          (hAccounts := accountMapEquiv_refl evmSinSolm.accountMap)
          hcallDaiSolmTrue
        have hslot :
            vowSlotWord slot evmDaiSolm.accountMap I =
              vowSlotWord slot evmSinSolm.accountMap I := by
          simpa [vowSlotWord, solcSlotWord, henvDai, henvSin] using hstatic
        rw [hslot, hSlotSinStatic slot]
      have hvatLoadDai :
          Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨1⟩ =
            vowSlotWord ⟨1⟩ σ_solm I := by
        have hDaiAcc :=
          vowSlotWord_accountMapEquiv (I := I) hAccountsDaiOut ⟨1⟩
        calc
          Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner ⟨1⟩ =
              vowSlotWord ⟨1⟩ σ_dai I := hslotDaiLoad ⟨1⟩
          _ = vowSlotWord ⟨1⟩ evmDaiSolm.accountMap I := hDaiAcc
          _ = vowSlotWord ⟨1⟩ σ_solm I := hSlotDaiStatic ⟨1⟩
      have hcreatedDai : evmDaiSolm.createdAccounts = cA_dai := by
        simp [evmDaiSolm]
      have hσ0Dai : evmDaiSolm.σ₀ = σ₀ := by
        simpa [evmDaiSolm] using hσ0Sin
      have hblocksDai : evmDaiSolm.blocks = bl := by
        simpa [evmDaiSolm] using hblocksSin
      have hgenesisDai : evmDaiSolm.genesisBlockHeader = gh := by
        simpa [evmDaiSolm] using hgenesisSin
      exact cont (memDai := memDai) (evmSinSolm := evmSinSolm)
        (evmDaiSolm := evmDaiSolm) (vatSin0 := vatSin0) (BumpVal := BumpVal)
        (surplus0 := surplus0) (HumpVal := HumpVal) (surplusNeed := surplusNeed)
        (vatDai := vatDai) rfl
        (by simpa [memDai] using rd1190)
        hmemSin hread64Sin hmemDai hread64Dai hvatCodeSolm hcallSinSolm hdecSin
        hBumpLoad hBumpSolm hsurplus0 hfit0 hHumpLoad hsurplusNeed hfitNeed hvatLoadSin
        hvatCodeDai hcallDaiSolmTrue hdecDai henough hvatLoadDai hdepthLt hcreatedDai
        hσ0Dai hblocksDai hgenesisDai henvDai hAccountsDaiOut hslotDaiLoad
        hSlotDaiStatic
    · have hshortDai : outDai.size < 32 := Nat.lt_of_not_ge ho32Dai
      exact vowFlapDai0DecodeShortBodyCore (acc := (cA_dai, σ_dai))
        (evmSin := evmSinSolm) (evmDai := evmDaiSolm)
        hcode hwv hdispatch hdecode rd1072True hmemSin hread64Sin hshortDai
        hoszDai hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0
        hHumpLoad hsurplusNeed hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolmTrue

/-- Public `flap()` wrapper prefix through the second `vat.sin(address(this))` call. -/
theorem vowFlapBodyToSub
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_sin1 : Batteries.RBSet AccountAddress compare} {σ_sin1 : AccountMap}
        {evmSin0 evmDai evmSin1 : EVM.State}
        {outSin0 outDai outSin1 memDai memSin1 : ByteArray}
        {k1318 C1318 : ℕ}
        {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai vatSin1 : UInt256},
        memSin1 = outSin1.write 0 (healSinCalldataMem I memDai) 128 32 →
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
          (vatSin1 :: ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
          memSin1 (UInt256.ofNat 6) outSin1 (cA_sin1, σ_sin1) k1318 C1318 →
        memDai.size = 164 →
        memDai.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        memSin1.size = 164 →
        memSin1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        0 < (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (true, evmSin0, outSin0) false →
        config.externalABI.decode? "sin" outSin0 =
          some [.int (Int.ofNat vatSin0.toNat)] →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨10⟩ = BumpVal →
        BumpVal = vowSlotWord ⟨10⟩ σ_solm I →
        surplus0 = vatSin0 + BumpVal →
        vatSin0.toNat + BumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨11⟩ = HumpVal →
        surplusNeed = surplus0 + HumpVal →
        surplus0.toNat + HumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        0 < (UInt256.ofNat
          ((evmSin0.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ_solm I)) "dai" 0
          [.address I.codeOwner] (true, evmDai, outDai) false →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat vatDai.toNat)] →
        evmDai.executionEnv.codeOwner = I.codeOwner →
        surplusNeed.toNat ≤ vatDai.toNat →
        Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        0 < (UInt256.ofNat
          ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
          [.address I.codeOwner] (true, evmSin1, outSin1) false →
        config.externalABI.decode? "sin" outSin1 =
          some [.int (Int.ofNat vatSin1.toNat)] →
        I.depth.val < 1024 →
        evmSin1.createdAccounts = cA_sin1 →
        evmSin1.σ₀ = σ₀ →
        evmSin1.blocks = bl →
        evmSin1.genesisBlockHeader = gh →
        evmSin1.executionEnv = I →
        accountMapEquiv σ_sin1 evmSin1.accountMap →
        (∀ slot : UInt256,
          Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner slot =
            vowSlotWord slot σ_sin1 I) →
        (∀ slot : UInt256,
          vowSlotWord slot evmSin1.accountMap I = vowSlotWord slot σ_solm I) →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some flapTransition :=
    vowDispatch_flap hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flap hsz4
  refine vowFlapBodyToSin1
    (fun {cA_dai} {σ_dai} {evmSinSolm} {evmDaiSolm} {outSin} {outDai}
        {memSin} {memDai} {k1190} {C1190} {vatSin0} {BumpVal} {surplus0}
        {HumpVal} {surplusNeed} {vatDai} hmemDaiDef rd1190 hmemSin hread64Sin
        hmemDai hread64Dai hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hBumpSolm
        hsurplus0 hfit0 hHumpLoad hsurplusNeed hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolm
        hdecDai henough hvatLoadDai hdepthLt hcreatedDai hσ0Dai hblocksDai
        hgenesisDai henvDai hAccountsDai hslotDaiLoad hSlotDaiStatic => ?_)
    hcode hsize hperm hwv hsel hAccounts
  have hownerDai : evmDaiSolm.executionEnv.codeOwner = I.codeOwner := by
    simp [henvDai]
  have hTargetDaiSolm :
      kissDaiTargetWord evmDaiSolm.accountMap I = kissDaiTargetWord σ_solm I := by
    have hslot := hSlotDaiStatic ⟨1⟩
    simp [kissDaiTargetWord, hslot]
  have haddrSin1 :
      kissVatAddress σ_solm I =
        AccountAddress.ofUInt256 (kissDaiTargetWord evmDaiSolm.accountMap I) := by
    rw [hTargetDaiSolm]
    exact kissVatAddress_eq_daiTarget_account σ_solm I
  have hVatAddrDai : kissVatAddress σ_dai I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hDaiAcc := vowSlotWord_accountMapEquiv (I := I) hAccountsDai ⟨1⟩
    have hslot : vowSlotWord ⟨1⟩ σ_dai I = vowSlotWord ⟨1⟩ σ_solm I := by
      rw [hDaiAcc, hSlotDaiStatic ⟨1⟩]
    simp [kissVatAddress, vowAddressReturnWord, hslot]
  by_cases hcodeSizeSin1 :
      Reasoning.Theory.extCodeSizeWord σ_dai (kissDaiTargetWord σ_dai I) =
        ⟨0⟩
  · have hcodeSizeSin1Solm :
        Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
            (kissDaiTargetWord evmDaiSolm.accountMap I) = ⟨0⟩ :=
      kissDaiCodeSize_zero_accountMapEquiv hAccountsDai hcodeSizeSin1
    have hvatNoCodeSin1 :
        (UInt256.ofNat
          ((evmDaiSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat = 0 := by
      simpa [State.lookupAccount] using
        extCodeSizeWord_zero_lookup_code_zero
          (σ := evmDaiSolm.accountMap)
          (target := kissDaiTargetWord evmDaiSolm.accountMap I)
          (addr := kissVatAddress σ_solm I) haddrSin1 hcodeSizeSin1Solm
    exact vowFlapSin1NoCodeBodyCore (acc := (cA_dai, σ_dai))
      (evmSin0 := evmSinSolm) (evmDai := evmDaiSolm)
      hcode hwv hdispatch hdecode rd1190 hmemDai hread64Dai hcodeSizeSin1
      hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0 hHumpLoad
      hsurplusNeed hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolm hdecDai
      henough hvatLoadDai hvatNoCodeSin1
  have hcodeSizeSin1NE :
      Reasoning.Theory.extCodeSizeWord σ_dai (kissDaiTargetWord σ_dai I) ≠
        ⟨0⟩ :=
    hcodeSizeSin1
  have hcodeSizeSin1SolmNE :
      Reasoning.Theory.extCodeSizeWord evmDaiSolm.accountMap
          (kissDaiTargetWord evmDaiSolm.accountMap I) ≠ ⟨0⟩ :=
    kissDaiCodeSize_ne_accountMapEquiv hAccountsDai hcodeSizeSin1NE
  have hvatCodeSin1 :
      0 < (UInt256.ofNat
        ((evmDaiSolm.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmDaiSolm.accountMap)
        (target := kissDaiTargetWord evmDaiSolm.accountMap I)
        (addr := kissVatAddress σ_solm I) haddrSin1 hcodeSizeSin1SolmNE
  obtain ⟨cA_sin1, σ_sin1, zSin1, outSin1, A_sin1, k1277, C1277,
      rd1277, hcallSin1EvmRaw, hoszSin1⟩ :=
    RD.vowFlapSin1PostCall rd1190 hmemDai hread64Dai hcodeSizeSin1NE hdepthLt
  let evmSin1EvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_dai
        createdAccounts := cA_dai }
  let evmSin1EvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_sin1
        substate := A_sin1
        createdAccounts := cA_sin1 }
  have hcallSin1Evm :
      typedCallViaEVM config evmSin1EvmIn
        (EVM.address (kissVatAddress σ_dai I)) "sin" 0 [.address I.codeOwner]
        (zSin1, evmSin1EvmOut, outSin1) false := by
    simpa [evmSin1EvmIn, evmSin1EvmOut] using hcallSin1EvmRaw
  let evmSin1SolmBase := { evmDaiSolm with substate := evmSin1EvmIn.substate }
  have hcallCreatedSin1 :
      evmSin1SolmBase.createdAccounts = evmSin1EvmIn.createdAccounts := by
    simpa [evmSin1SolmBase, evmSin1EvmIn] using hcreatedDai
  have hcallEnvSin1 : evmSin1SolmBase.executionEnv = evmSin1EvmIn.executionEnv := by
    simpa [evmSin1SolmBase, evmSin1EvmIn, initState] using henvDai
  obtain ⟨σ_sin1_solm, A_sin1_solm0, hcallSin1SolmBase, hAccountsSin1⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSin1SolmBase)
      hcallSin1Evm hAccountsDai
      (by simpa [evmSin1EvmIn, evmSin1SolmBase, initState] using hσ0Dai.symm)
      hcallCreatedSin1
      (by simpa [evmSin1EvmIn, evmSin1SolmBase, initState] using hgenesisDai)
      (by simpa [evmSin1EvmIn, evmSin1SolmBase, initState] using hblocksDai)
      (by simp [evmSin1SolmBase])
      hcallEnvSin1
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBase : evmSin1SolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmSin1SolmBase, henvDai] using hdepthNeI
  obtain ⟨A_sin1_solm, hcallSin1SolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallSin1SolmBase hdepthNeBase
      evmDaiSolm.substate
  let evmSin1Solm :=
    { evmDaiSolm with
        accountMap := σ_sin1_solm
        substate := A_sin1_solm
        createdAccounts := cA_sin1 }
  have hcallSin1Solm :
      typedCallViaEVM config evmDaiSolm
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (zSin1, evmSin1Solm, outSin1) false := by
    simpa [evmSin1Solm, evmSin1SolmBase, hVatAddrDai] using hcallSin1SolmRaw
  cases zSin1
  · exact vowFlapSin1CallFailureBodyCore (acc := (cA_sin1, σ_sin1))
      (evmSin0 := evmSinSolm) (evmDai := evmDaiSolm) (evmSin1 := evmSin1Solm)
      hcode hwv hdispatch hdecode (by simpa using rd1277) hoszSin1 hvatCodeSolm
      hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0 hHumpLoad hsurplusNeed
      hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolm hdecDai hownerDai henough
      hvatLoadDai hvatCodeSin1 (by simpa using hcallSin1Solm)
  · have rd1277True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        (⟨1⟩ :: healSinEndPtr :: healSinSelector :: kissDaiTargetWord (cA_dai, σ_dai).2 I ::
          ⟨1325⟩ :: ⟨1333⟩ :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
        (outSin1.write 0 (healSinCalldataMem I memDai) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin1.size)).toNat)
        (UInt256.ofNat 6) outSin1 (cA_sin1, σ_sin1) k1277 C1277 := by
      simpa using rd1277
    have hcallSin1SolmTrue :
        typedCallViaEVM config evmDaiSolm
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (true, evmSin1Solm, outSin1) false := by
      simpa using hcallSin1Solm
    by_cases ho32Sin1 : 32 ≤ outSin1.size
    · let vatSin1 : UInt256 :=
        UInt256.ofNat (fromByteArrayBigEndian (outSin1.extract 0 32))
      have hdecSin1 :
          config.externalABI.decode? "sin" outSin1 =
            some [.int (Int.ofNat vatSin1.toNat)] := by
        simpa [vatSin1] using vatSinDecode_ok (o := outSin1) ho32Sin1
      obtain ⟨_, _, rd1318⟩ :=
        RD.vowFlapSin1PostCallDecodeOk rd1277True hmemDai hread64Dai ho32Sin1
          hoszSin1
      let memSin1 := outSin1.write 0 (healSinCalldataMem I memDai) 128 32
      have hmemSin1 : memSin1.size = 164 := by
        simpa [memSin1] using healSinWrite_size I memDai outSin1 32 hmemDai
          (by omega) ho32Sin1
      have hread64Sin1 :
          memSin1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
        simpa [memSin1] using
          healSinWrite_read64 I memDai outSin1 32 hmemDai hread64Dai
            (by omega) ho32Sin1
      have hStateSin1 : EVMStateEquiv evmSin1EvmOut evmSin1Solm := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [evmSin1EvmOut, evmSin1Solm, initState] using henvDai.symm
        · simp [evmSin1EvmOut, evmSin1Solm]
        · simpa [evmSin1EvmOut, evmSin1Solm] using hAccountsSin1
      have hslotSin1Load : ∀ slot : UInt256,
          Solm.EVM.storageLoad evmSin1Solm evmSin1Solm.executionEnv.codeOwner slot =
            vowSlotWord slot σ_sin1 I := by
        intro slot
        have h := hStateSin1.storageLoad_codeOwner slot
        rw [← h]
        simp [evmSin1EvmOut, initState, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, vowSlotWord, solcSlotWord]
      have hAccountsSin1Out : accountMapEquiv σ_sin1 evmSin1Solm.accountMap := by
        simpa [evmSin1EvmOut, evmSin1Solm] using hAccountsSin1
      have hcreatedSin1 : evmSin1Solm.createdAccounts = cA_sin1 := by
        simp [evmSin1Solm]
      have hσ0Sin1 : evmSin1Solm.σ₀ = σ₀ := by
        simpa [evmSin1Solm] using hσ0Dai
      have hblocksSin1 : evmSin1Solm.blocks = bl := by
        simpa [evmSin1Solm] using hblocksDai
      have hgenesisSin1 : evmSin1Solm.genesisBlockHeader = gh := by
        simpa [evmSin1Solm] using hgenesisDai
      have henvSin1 : evmSin1Solm.executionEnv = I := by
        simpa [evmSin1Solm] using henvDai
      have hSlotSin1Static : ∀ slot : UInt256,
          vowSlotWord slot evmSin1Solm.accountMap I = vowSlotWord slot σ_solm I := by
        intro slot
        have hstatic := typedCallViaEVM_static_storage_findD_of_accountMapEquiv
          (cfg := config) (σ := evmDaiSolm.accountMap)
          (evm := evmDaiSolm) (evm' := evmSin1Solm) (slot := slot)
          (default := ⟨0⟩)
          (hAccounts := accountMapEquiv_refl evmDaiSolm.accountMap)
          hcallSin1SolmTrue
        have hslot :
            vowSlotWord slot evmSin1Solm.accountMap I =
              vowSlotWord slot evmDaiSolm.accountMap I := by
          simpa [vowSlotWord, solcSlotWord, henvSin1, henvDai] using hstatic
        rw [hslot, hSlotDaiStatic slot]
      exact cont (memSin1 := memSin1) (evmSin0 := evmSinSolm)
        (evmDai := evmDaiSolm) (evmSin1 := evmSin1Solm)
        (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
        (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
        (vatSin1 := vatSin1) rfl (by simpa [memSin1, vatSin1] using rd1318)
        hmemDai hread64Dai hmemSin1 hread64Sin1 hvatCodeSolm hcallSinSolm hdecSin
        hBumpLoad hBumpSolm hsurplus0 hfit0 hHumpLoad hsurplusNeed hfitNeed hvatLoadSin
        hvatCodeDai hcallDaiSolm hdecDai hownerDai henough hvatLoadDai hvatCodeSin1
        hcallSin1SolmTrue hdecSin1 hdepthLt hcreatedSin1 hσ0Sin1 hblocksSin1
        hgenesisSin1 henvSin1 hAccountsSin1Out hslotSin1Load hSlotSin1Static
    · have hshortSin1 : outSin1.size < 32 := Nat.lt_of_not_ge ho32Sin1
      exact vowFlapSin1DecodeShortBodyCore (acc := (cA_sin1, σ_sin1))
        (evmSin0 := evmSinSolm) (evmDai := evmDaiSolm) (evmSin1 := evmSin1Solm)
        hcode hwv hdispatch hdecode rd1277True hmemDai hread64Dai hshortSin1
        hoszSin1 hvatCodeSolm hcallSinSolm hdecSin hBumpLoad hsurplus0 hfit0
        hHumpLoad hsurplusNeed hfitNeed hvatLoadSin hvatCodeDai hcallDaiSolm
        hdecDai hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1SolmTrue

/-- Public `flap()` wrapper prefix through the checked subtractions and zero-debt gate. -/
theorem vowFlapBodyToKick
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (cont :
      ∀ {cA_sin1 : Batteries.RBSet AccountAddress compare} {σ_sin1 : AccountMap}
        {evmSin0 evmDai evmSin1 : EVM.State}
        {outSin0 outDai outSin1 memSin1 : ByteArray} {k1403 C1403 : ℕ}
        {vatSin0 BumpVal surplus0 HumpVal surplusNeed vatDai vatSin1 freeSin debt :
          UInt256},
        RD vowBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1403⟩
          (⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
          memSin1 (UInt256.ofNat 6) outSin1 (cA_sin1, σ_sin1) k1403 C1403 →
        memSin1.size = 164 →
        memSin1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
        0 < (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
          (true, evmSin0, outSin0) false →
        config.externalABI.decode? "sin" outSin0 =
          some [.int (Int.ofNat vatSin0.toNat)] →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨10⟩ = BumpVal →
        BumpVal = vowSlotWord ⟨10⟩ σ_solm I →
        surplus0 = vatSin0 + BumpVal →
        vatSin0.toNat + BumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨11⟩ = HumpVal →
        surplusNeed = surplus0 + HumpVal →
        surplus0.toNat + HumpVal.toNat < UInt256.size →
        Solm.EVM.storageLoad evmSin0 evmSin0.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        0 < (UInt256.ofNat
          ((evmSin0.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmSin0 (EVM.address (kissVatAddress σ_solm I)) "dai" 0
          [.address I.codeOwner] (true, evmDai, outDai) false →
        config.externalABI.decode? "dai" outDai =
          some [.int (Int.ofNat vatDai.toNat)] →
        evmDai.executionEnv.codeOwner = I.codeOwner →
        surplusNeed.toNat ≤ vatDai.toNat →
        Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
          vowSlotWord ⟨1⟩ σ_solm I →
        0 < (UInt256.ofNat
          ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
            (fun acc => acc.code.size))).toNat →
        typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
          [.address I.codeOwner] (true, evmSin1, outSin1) false →
        config.externalABI.decode? "sin" outSin1 =
          some [.int (Int.ofNat vatSin1.toNat)] →
        Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ =
          vowSlotWord ⟨5⟩ σ_sin1 I →
        freeSin = UInt256.sub vatSin1 (vowSlotWord ⟨5⟩ σ_sin1 I) →
        (vowSlotWord ⟨5⟩ σ_sin1 I).toNat ≤ vatSin1.toNat →
        Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ =
          vowSlotWord ⟨6⟩ σ_sin1 I →
        debt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ σ_sin1 I) →
        (vowSlotWord ⟨6⟩ σ_sin1 I).toNat ≤ freeSin.toNat →
        debt = ⟨0⟩ →
        I.depth.val < 1024 →
        evmSin1.createdAccounts = cA_sin1 →
        evmSin1.σ₀ = σ₀ →
        evmSin1.blocks = bl →
        evmSin1.genesisBlockHeader = gh →
        evmSin1.executionEnv = I →
        accountMapEquiv σ_sin1 evmSin1.accountMap →
        (∀ slot : UInt256,
          Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner slot =
            vowSlotWord slot σ_sin1 I) →
        (∀ slot : UInt256,
          vowSlotWord slot evmSin1.accountMap I = vowSlotWord slot σ_solm I) →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some flapTransition :=
    vowDispatch_flap hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flap hsz4
  refine vowFlapBodyToSub
    (fun {cA_sin1} {σ_sin1} {evmSin0} {evmDai} {evmSin1} {outSin0} {outDai}
        {outSin1} {memDai} {memSin1} {k1318} {C1318} {vatSin0} {BumpVal}
        {surplus0} {HumpVal} {surplusNeed} {vatDai} {vatSin1} hmemSin1Def rd1318
        hmemDai hread64Dai hmemSin1 hread64Sin1 hvatCodeSolm hcallSin0 hdecSin0
        hBumpLoad0 hBumpSolm hsurplus0 hfit0 hHumpLoad0 hsurplusNeed hfitNeed hvatLoadSin0
        hvatCodeDai hcallDai hdecDai hownerDai henough hvatLoadDai hvatCodeSin1
        hcallSin1 hdecSin1 hdepthLt hcreatedSin1 hσ0Sin1 hblocksSin1 hgenesisSin1
        henvSin1 hAccountsSin1 hslotSin1Load hSlotSin1Static => ?_)
    hcode hsize hperm hwv hsel hAccounts
  let SinVal : UInt256 := vowSlotWord ⟨5⟩ σ_sin1 I
  let AshVal : UInt256 := vowSlotWord ⟨6⟩ σ_sin1 I
  have hSinLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨5⟩ = SinVal := by
    simpa [SinVal] using hslotSin1Load ⟨5⟩
  by_cases hfreeUnder : vatSin1.toNat < SinVal.toNat
  · exact vowFlapFreeSinUnderflowBodyCore (acc := (cA_sin1, σ_sin1))
      (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
      hcode hwv hdispatch hdecode (by simpa [SinVal] using rd1318)
      (by simpa [SinVal] using hfreeUnder)
      hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hfit0 hHumpLoad0
      hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
      henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1
      (by simpa [SinVal] using hSinLoad)
  have hfreeOk : SinVal.toNat ≤ vatSin1.toNat := by
    omega
  let freeSin : UInt256 := UInt256.sub vatSin1 SinVal
  obtain ⟨_, _, rd1325⟩ :=
    RD.vowFlapFreeSinSubSuccess (by simpa [SinVal] using rd1318)
      (by simpa [SinVal] using hfreeOk)
  have hAshLoad :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨6⟩ = AshVal := by
    simpa [AshVal] using hslotSin1Load ⟨6⟩
  by_cases hdebtUnder : freeSin.toNat < AshVal.toNat
  · exact vowFlapDebtUnderflowBodyCore (acc := (cA_sin1, σ_sin1))
      (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
      hcode hwv hdispatch hdecode (by simpa [freeSin, SinVal] using rd1325)
      (by simpa [AshVal] using hdebtUnder)
      hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hfit0 hHumpLoad0
      hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
      henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1
      (by simpa [SinVal] using hSinLoad) rfl hfreeOk
      (by simpa [AshVal] using hAshLoad)
  have hdebtOk : AshVal.toNat ≤ freeSin.toNat := by
    omega
  let debt : UInt256 := UInt256.sub freeSin AshVal
  obtain ⟨_, _, rd1333⟩ :=
    RD.vowFlapDebtSubSuccess (by simpa [freeSin, SinVal] using rd1325)
      (by simpa [AshVal] using hdebtOk)
  by_cases hdebtNe : debt ≠ ⟨0⟩
  · exact vowFlapDebtNotZeroBodyCore (acc := (cA_sin1, σ_sin1))
      (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
      hcode hwv hdispatch hdecode (by simpa [debt, freeSin, AshVal] using rd1333)
      hdebtNe hmemSin1 hread64Sin1 hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0
      hsurplus0 hfit0 hHumpLoad0 hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai
      hcallDai hdecDai hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1
      hdecSin1 (by simpa [SinVal] using hSinLoad) rfl hfreeOk
      (by simpa [AshVal] using hAshLoad) rfl hdebtOk
  have hdebtZero : debt = ⟨0⟩ := not_not.mp hdebtNe
  obtain ⟨_, _, rd1403⟩ :=
    RD.vowFlapDebtZero (by simpa [debt, freeSin, AshVal] using rd1333) hdebtZero
  exact cont (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
    (vatSin0 := vatSin0) (BumpVal := BumpVal) (surplus0 := surplus0)
    (HumpVal := HumpVal) (surplusNeed := surplusNeed) (vatDai := vatDai)
    (vatSin1 := vatSin1) (freeSin := freeSin) (debt := debt)
    (by simpa [freeSin, debt, SinVal, AshVal] using rd1403)
    hmemSin1 hread64Sin1 hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hBumpSolm
    hsurplus0 hfit0 hHumpLoad0 hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai hcallDai
    hdecDai hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1
    (by simpa [SinVal] using hSinLoad) rfl hfreeOk
    (by simpa [AshVal] using hAshLoad) rfl hdebtOk hdebtZero hdepthLt hcreatedSin1
    hσ0Sin1 hblocksSin1 hgenesisSin1 henvSin1 hAccountsSin1 hslotSin1Load
    hSlotSin1Static

theorem vowFlapBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch : dispatchMsg contract I.calldata = some flapTransition :=
    vowDispatch_flap hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ rfl hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅ :=
    vowDecode_flap hsz4
  refine vowFlapBodyToKick
    (fun {cA_sin1} {σ_sin1} {evmSin0} {evmDai} {evmSin1} {outSin0} {outDai}
        {outSin1} {memSin1} {k1403} {C1403} {vatSin0} {BumpVal} {surplus0}
        {HumpVal} {surplusNeed} {vatDai} {vatSin1} {freeSin} {debt} rd1403
        hmemSin1 hread64Sin1 hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hBumpSolm
        hsurplus0 hfit0 hHumpLoad0 hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai
        hcallDai hdecDai hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1
        hdecSin1 hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hdebtZero hdepthLt
        hcreatedSin1 hσ0Sin1 hblocksSin1 hgenesisSin1 henvSin1 hAccountsSin1
        hslotSin1Load hSlotSin1Static => ?_)
    hcode hsize hperm hwv hsel hAccounts
  have hBumpSin1 : vowSlotWord ⟨10⟩ σ_sin1 I = BumpVal := by
    have hacc := vowSlotWord_accountMapEquiv (I := I) hAccountsSin1 ⟨10⟩
    calc
      vowSlotWord ⟨10⟩ σ_sin1 I =
          vowSlotWord ⟨10⟩ evmSin1.accountMap I := hacc
      _ = vowSlotWord ⟨10⟩ σ_solm I := hSlotSin1Static ⟨10⟩
      _ = BumpVal := hBumpSolm.symm
  have hBumpLoad1 :
      Solm.EVM.storageLoad evmSin1 evmSin1.executionEnv.codeOwner ⟨10⟩ = BumpVal := by
    simpa [hBumpSin1] using hslotSin1Load ⟨10⟩
  have hownerSin1 : evmSin1.executionEnv.codeOwner = I.codeOwner := by
    simp [henvSin1]
  by_cases hcodeSizeKick :
      Reasoning.Theory.extCodeSizeWord σ_sin1 (vowAddressReturnWord ⟨2⟩ σ_sin1 I) =
        ⟨0⟩
  · have hcodeSizeKickSolm :
        Reasoning.Theory.extCodeSizeWord evmSin1.accountMap
            (vowAddressReturnWord ⟨2⟩ evmSin1.accountMap I) = ⟨0⟩ :=
      flapFlapperCodeSize_zero_accountMapEquiv hAccountsSin1 hcodeSizeKick
    have hflapperNoCode :
        (UInt256.ofNat
          ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      flapFlapperCode_zero_of_codeSize_zero evmSin1 I hownerSin1 hcodeSizeKickSolm
    exact vowFlapKickNoCodeBodyCore (acc := (cA_sin1, σ_sin1))
      (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
      hcode hwv hdispatch hdecode rd1403 hmemSin1 hread64Sin1 hcodeSizeKick
      hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hfit0 hHumpLoad0
      hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai
      henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk
      hAshLoad hdebt hdebtOk hdebtZero hflapperNoCode
  have hcodeSizeKickNE :
      Reasoning.Theory.extCodeSizeWord σ_sin1 (vowAddressReturnWord ⟨2⟩ σ_sin1 I) ≠
        ⟨0⟩ :=
    hcodeSizeKick
  have hcodeSizeKickSolmNE :
      Reasoning.Theory.extCodeSizeWord evmSin1.accountMap
          (vowAddressReturnWord ⟨2⟩ evmSin1.accountMap I) ≠ ⟨0⟩ :=
    flapFlapperCodeSize_ne_accountMapEquiv hAccountsSin1 hcodeSizeKickNE
  have hflapperCode :
      0 < (UInt256.ofNat
        ((evmSin1.lookupAccount (flapFlapperAddressOf evmSin1)).option 0
          (fun acc => acc.code.size))).toNat :=
    flapFlapperCode_pos_of_codeSize_ne evmSin1 I hownerSin1 hcodeSizeKickSolmNE
  obtain ⟨cA_kick, σ_kick, zKick, outKick, A_kick, k1498, C1498, rd1498,
      hcallKickEvmRaw, houtKickSize⟩ :=
    RD.vowFlapKickPostCall rd1403 hmemSin1 hread64Sin1 hcodeSizeKickNE hperm hdepthLt
  let evmKickEvmIn :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_sin1
        createdAccounts := cA_sin1 }
  let evmKickEvmOut :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_kick
        substate := A_kick
        createdAccounts := cA_kick }
  have hTargetEq :
      vowAddressReturnWord ⟨2⟩ σ_sin1 I =
        vowAddressReturnWord ⟨2⟩ evmSin1.accountMap I :=
    flapFlapperTargetWord_accountMapEquiv hAccountsSin1
  have hFlapperAddr :
      flapFlapperAddressOf evmSin1 =
        AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ evmSin1.accountMap I) :=
    flapFlapperAddressOf_eq_vowAddressReturnWord evmSin1 I hownerSin1
  have hKickTargetAddr :
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σ_sin1 I).toNat) =
        EVM.address (flapFlapperAddressOf evmSin1) := by
    calc
      EVM.address (AccountAddress.ofNat (vowAddressReturnWord ⟨2⟩ σ_sin1 I).toNat)
          = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ σ_sin1 I) :=
            flapKickAddress_eq_target σ_sin1 I
      _ = AccountAddress.ofUInt256 (vowAddressReturnWord ⟨2⟩ evmSin1.accountMap I) := by
            rw [hTargetEq]
      _ = EVM.address (flapFlapperAddressOf evmSin1) := by
            rw [← hFlapperAddr]
            apply Eq.symm
            apply Fin.ext
            simp [EVM.address, EVM.uintN]
            exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
  have hcallKickEvm :
      typedCallViaEVM config evmKickEvmIn
        (EVM.address (flapFlapperAddressOf evmSin1)) "kick" 0
        [.int (Int.ofNat BumpVal.toNat), .int 0]
        (zKick, evmKickEvmOut, outKick) true := by
    simpa [evmKickEvmIn, evmKickEvmOut, hKickTargetAddr, hBumpSin1] using hcallKickEvmRaw
  let evmKickSolmBase := { evmSin1 with substate := evmKickEvmIn.substate }
  have hcallCreatedKick :
      evmKickSolmBase.createdAccounts = evmKickEvmIn.createdAccounts := by
    simpa [evmKickSolmBase, evmKickEvmIn] using hcreatedSin1
  have hcallEnvKick :
      evmKickSolmBase.executionEnv = evmKickEvmIn.executionEnv := by
    simpa [evmKickSolmBase, evmKickEvmIn, initState] using henvSin1
  obtain ⟨σ_kick_solm, A_kick_solm0, hcallKickSolmBase, hAccountsKick⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmKickSolmBase)
      hcallKickEvm hAccountsSin1
      (by simpa [evmKickEvmIn, evmKickSolmBase, initState] using hσ0Sin1.symm)
      hcallCreatedKick
      (by simpa [evmKickEvmIn, evmKickSolmBase, initState] using hgenesisSin1)
      (by simpa [evmKickEvmIn, evmKickSolmBase, initState] using hblocksSin1)
      (by simp [evmKickSolmBase])
      hcallEnvKick
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hdepthEq
    rw [hdepthEq] at hdepthLt
    norm_num at hdepthLt
  have hdepthNeBaseKick : evmKickSolmBase.executionEnv.depth ≠ 1024 := by
    simpa [evmKickSolmBase, henvSin1] using hdepthNeI
  obtain ⟨A_kick_solm, hcallKickSolmRaw⟩ :=
    typedCallViaEVM_zero_setSubstate hcallKickSolmBase hdepthNeBaseKick evmSin1.substate
  let evmKickSolm :=
    { evmSin1 with
        accountMap := σ_kick_solm
        substate := A_kick_solm
        createdAccounts := cA_kick }
  have hcallKickSolm :
      typedCallViaEVM config evmSin1 (EVM.address (flapFlapperAddressOf evmSin1))
        "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
        (zKick, evmKickSolm, outKick) true := by
    simpa [evmKickSolm, evmKickSolmBase] using hcallKickSolmRaw
  cases zKick
  · exact vowFlapKickCallFailureBodyCore (acc := (cA_kick, σ_kick))
      (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
      (evmKick := evmKickSolm) (SinVal := vowSlotWord ⟨5⟩ σ_sin1 I)
      (AshVal := vowSlotWord ⟨6⟩ σ_sin1 I)
      hcode hwv hdispatch hdecode (by simpa using rd1498) houtKickSize hvatCodeSolm
      hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hfit0 hHumpLoad0 hsurplusNeed
      hfitNeed hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai henough
      hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk hAshLoad
      hdebt hdebtOk hdebtZero hBumpLoad1 hflapperCode (by simpa using hcallKickSolm)
  · have rd1498True : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1498⟩
        (⟨1⟩ :: flapKickEndPtr :: flapKickSelectorWord ::
          vowAddressReturnWord ⟨2⟩ σ_sin1 I :: ⟨0⟩ :: ⟨357⟩ :: vowSelWord I :: [])
        (outKick.write 0 (flapKickCalldataMem BumpVal memSin1) flapKickOutPtr.toNat
          (min flapKickOutSize (UInt256.ofNat outKick.size)).toNat)
        (UInt256.ofNat 7) outKick (cA_kick, σ_kick) k1498 C1498 := by
      simpa [hBumpSin1] using rd1498
    have hcallKickSolmTrue :
        typedCallViaEVM config evmSin1 (EVM.address (flapFlapperAddressOf evmSin1))
          "kick" 0 [.int (Int.ofNat BumpVal.toNat), .int 0]
          (true, evmKickSolm, outKick) true := by
      simpa using hcallKickSolm
    by_cases ho32Kick : 32 ≤ outKick.size
    · let id : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (outKick.extract 0 32))
      have hcreatedFinal : (cA_kick, σ_kick).1 = evmKickSolm.createdAccounts := by
        rfl
      have hAccountsFinal : accountMapEquiv (cA_kick, σ_kick).2 evmKickSolm.accountMap := by
        simpa [evmKickEvmOut, evmKickSolm] using hAccountsKick
      exact vowFlapKickSuccessBodyCore (acc := (cA_kick, σ_kick))
        (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
        (evmKick := evmKickSolm) (id := id) (SinVal := vowSlotWord ⟨5⟩ σ_sin1 I)
        (AshVal := vowSlotWord ⟨6⟩ σ_sin1 I)
        hcode hwv hdispatch hdecode (by simpa using rd1498True)
        hmemSin1 hread64Sin1 ho32Kick houtKickSize rfl hvatCodeSolm
        hcallSin0 hdecSin0 hBumpLoad0 hsurplus0 hfit0 hHumpLoad0 hsurplusNeed
        hfitNeed hvatLoadSin0 hvatCodeDai hcallDai hdecDai hownerDai henough
        hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1 hSinLoad hfree hfreeOk hAshLoad
        hdebt hdebtOk hdebtZero hBumpLoad1 hflapperCode hcallKickSolmTrue
        hcreatedFinal hAccountsFinal
    · have hshortKick : outKick.size < 32 := Nat.lt_of_not_ge ho32Kick
      have hminKick :
          (min flapKickOutSize (UInt256.ofNat outKick.size)).toNat = outKick.size := by
        simpa [flapKickOutSize] using kissDaiMin32_toNat_of_lt hshortKick
      have rd1498Short := rd1498True
      rw [hminKick, show flapKickOutPtr.toNat = 128 from by decide +native] at rd1498Short
      obtain ⟨k1516, C1516, rd1516⟩ :=
        RD.vowFlapKickCallSuccessToDecode rd1498Short (by simp)
      have hmemKickShort :
          (outKick.write 0 (flapKickCalldataMem BumpVal memSin1) 128 outKick.size).size =
            196 :=
        flapKickWrite_size BumpVal outKick outKick.size hmemSin1 (by omega) (by omega)
      have hread64KickShort :
          (outKick.write 0 (flapKickCalldataMem BumpVal memSin1) 128 outKick.size
            ).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        flapKickWrite_read64 BumpVal outKick outKick.size hmemSin1 hread64Sin1
          (by omega) (by omega)
      have hmload64KickShort :
          (if (⟨64⟩ : UInt256).toNat ≥
                (outKick.write 0 (flapKickCalldataMem BumpVal memSin1) 128 outKick.size).size
              ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat
             (fromByteArrayBigEndian
              ((outKick.write 0 (flapKickCalldataMem BumpVal memSin1) 128 outKick.size
                ).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
            ⟨128⟩ :=
        mloadFreePtrValue (by rw [hmemKickShort]; decide) (by decide) hread64KickShort
      exact vowFlapKickDecodeShortBodyCore (acc := (cA_kick, σ_kick))
        (evmSin0 := evmSin0) (evmDai := evmDai) (evmSin1 := evmSin1)
        (evmKick := evmKickSolm) (SinVal := vowSlotWord ⟨5⟩ σ_sin1 I)
        (AshVal := vowSlotWord ⟨6⟩ σ_sin1 I)
        hcode hwv hdispatch hdecode (by simpa using rd1516) hshortKick houtKickSize
        hmload64KickShort hvatCodeSolm hcallSin0 hdecSin0 hBumpLoad0 hsurplus0
        hfit0 hHumpLoad0 hsurplusNeed hfitNeed hvatLoadSin0 hvatCodeDai hcallDai
        hdecDai hownerDai henough hvatLoadDai hvatCodeSin1 hcallSin1 hdecSin1
        hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hdebtZero hBumpLoad1
        hflapperCode hcallKickSolmTrue

end Benchmarks.Dss.Vow
