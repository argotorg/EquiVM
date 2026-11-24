import Benchmarks.CurveVault.MemoryActive
import Benchmarks.CurveVault.InitializeStorage
import Benchmarks.CurveVault.TokenCallSource
import Benchmarks.CurveVault.Calls
import Benchmarks.CurveVault.RuntimeBlocks_002

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

def vaultInitializeConfigState (I : ExecutionEnv) (evm : State) (amm controller collateral precision : UInt256) : State :=
  Stele.EVM.storageStore
    (Stele.EVM.storageStore
      (Stele.EVM.storageStore
        (Stele.EVM.storageStore
          (Stele.EVM.storageStore evm I.codeOwner ⟨1⟩ collateral)
          I.codeOwner ⟨4⟩ (UInt256.ofNat I.source.val))
        I.codeOwner ⟨2⟩ amm)
      I.codeOwner ⟨3⟩ controller)
    I.codeOwner ⟨15⟩ precision

def vaultInitializeConfigAccounts (I : ExecutionEnv) (σ : AccountMap) (amm controller collateral precision : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨1⟩ collateral) ⟨4⟩ (UInt256.ofNat I.source.val))
        ⟨2⟩ amm) ⟨3⟩ controller) ⟨15⟩ precision

theorem vaultInitializeConfigSource {I : ExecutionEnv} {s0 evm : State} {σ : AccountMap}
    {locals : Store} {amm controller collateral precision : UInt256}
    (hs : SourceState s0 I σ evm)
    (ha : locals.get? "_amm_" = some (.address (AccountAddress.ofNat amm.toNat)))
    (hc : locals.get? "_controller_" = some (.address (AccountAddress.ofNat controller.toNat)))
    (hl : locals.get? "_collateral_token_" = some (.address (AccountAddress.ofNat collateral.toNat)))
    (hp : locals.get? "borrowed_precision" = some (.int (Int.ofNat precision.toNat)))
    (hbase : ∀ name ∈ ["_collateral_token", "_factory", "_amm", "_controller", "precision"], locals.get? name = none)
    (hacanon : amm.toNat < EVM.addressModulus) (hccanon : controller.toNat < EVM.addressModulus)
    (hlcanon : collateral.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals} evm (initializeTransition.body.drop 5 |>.take 5)
      (.ok {contract := contract, locals := locals} (vaultInitializeConfigState I evm amm controller collateral precision)) ∧
    SourceState s0 I (vaultInitializeConfigAccounts I σ amm controller collateral precision)
      (vaultInitializeConfigState I evm amm controller collateral precision) := by
  let evm1 := Stele.EVM.storageStore evm I.codeOwner ⟨1⟩ collateral
  let evm2 := Stele.EVM.storageStore evm1 I.codeOwner ⟨4⟩ (UInt256.ofNat I.source.val)
  let evm3 := Stele.EVM.storageStore evm2 I.codeOwner ⟨2⟩ amm
  let evm4 := Stele.EVM.storageStore evm3 I.codeOwner ⟨3⟩ controller
  have hs1 := hs.storageWrite ⟨1⟩ collateral
  have hs2 := hs1.storageWrite ⟨4⟩ (UInt256.ofNat I.source.val)
  have hs3 := hs2.storageWrite ⟨2⟩ amm
  have hs4 := hs3.storageWrite ⟨3⟩ controller
  have he1 : evm1.executionEnv = I := hs1.env
  have he2 : evm2.executionEnv = I := hs2.env
  have he3 : evm3.executionEnv = I := hs3.env
  have he4 : evm4.executionEnv = I := hs4.env
  refine ⟨?_, hs4.storageWrite ⟨15⟩ precision⟩
  have hw (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
      UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w := by
    simpa only [keyValueToWord_address] using keyValueToWord_address_of_canonical w hcanon
  have sl : ExecStmt fork config {contract := contract, locals := locals} evm initializeTransition.body[5]!
      (.ok {contract := contract, locals := locals} evm1) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [hs.env] using hperm)) (by simp only [evalExpr?, hl, EvalResult.ofOption]; rfl)
      (by simpa only [hs.env, hw collateral hlcanon] using (vaultAssignScalarAddress evm locals
        "_collateral_token" ⟨1⟩ (AccountAddress.ofNat collateral.toNat) (hbase _ (by decide +kernel)) rfl rfl))
  have sf : ExecStmt fork config {contract := contract, locals := locals} evm1 initializeTransition.body[6]!
      (.ok {contract := contract, locals := locals} evm2) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [he1] using hperm)) (by simpa only [he1] using evalExpr_caller (cfg := config) (stele := {contract := contract, locals := locals}) evm1)
      (by simpa only [he1] using (vaultAssignScalarAddress evm1 locals
        "_factory" ⟨4⟩ I.source (hbase _ (by decide +kernel)) rfl rfl))
  have sa : ExecStmt fork config {contract := contract, locals := locals} evm2 initializeTransition.body[7]!
      (.ok {contract := contract, locals := locals} evm3) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [he2] using hperm)) (by simp only [evalExpr?, ha, EvalResult.ofOption]; rfl)
      (by simpa only [he2, hw amm hacanon] using (vaultAssignScalarAddress evm2 locals
        "_amm" ⟨2⟩ (AccountAddress.ofNat amm.toNat) (hbase _ (by decide +kernel)) rfl rfl))
  have sc : ExecStmt fork config {contract := contract, locals := locals} evm3 initializeTransition.body[8]!
      (.ok {contract := contract, locals := locals} evm4) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [he3] using hperm)) (evalExpr_castAddressUint256_word hccanon (by simp only [evalExpr?, hc, EvalResult.ofOption]))
      (by simpa only [he3] using vaultAssignController evm3 locals controller (hbase _ (by decide +kernel)) hccanon)
  have sp : ExecStmt fork config {contract := contract, locals := locals} evm4 initializeTransition.body[9]!
      (.ok {contract := contract, locals := locals} (vaultInitializeConfigState I evm amm controller collateral precision)) :=
    ExecStmt.assign (hperm := Or.inr (by simpa only [he4] using hperm)) (by simp only [evalExpr?, hp, EvalResult.ofOption]; rfl)
      (by simpa only [he4] using (vaultAssignScalarUint256 evm4 locals "precision" ⟨15⟩ precision
        (hbase _ (by decide +kernel)) rfl rfl (by decide +kernel)))
  exact ExecBlock.consNormal sl (ExecBlock.consNormal sf (ExecBlock.consNormal sa
    (ExecBlock.consNormal sc (ExecBlock.consNormal sp ExecBlock.nil))))

theorem vaultInitializeConfigWrites {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store} {amm controller collateral token exponent : UInt256}
    (hs : SourceState s0 I σ evm)
    (ha : locals.get? "_amm_" = some (.address (AccountAddress.ofNat amm.toNat)))
    (hc : locals.get? "_controller_" = some (.address (AccountAddress.ofNat controller.toNat)))
    (hl : locals.get? "_collateral_token_" = some (.address (AccountAddress.ofNat collateral.toNat)))
    (hp : locals.get? "borrowed_precision" = some (.int (Int.ofNat (UInt256.exp ⟨10⟩ exponent).toNat)))
    (hbase : ∀ name ∈ ["_collateral_token", "_factory", "_amm", "_controller", "precision"], locals.get? name = none)
    (hacanon : amm.toNat < EVM.addressModulus) (hccanon : controller.toNat < EVM.addressModulus)
    (hlcanon : collateral.toNat < EVM.addressModulus)
    (hsize : mem.size = 320)
    (hma : memLoad (UInt256.ofNat 64) mem = amm) (hmc : memLoad (UInt256.ofNat 96) mem = controller)
    (hmt : memLoad (UInt256.ofNat 128) mem = token) (hml : memLoad (UInt256.ofNat 160) mem = collateral)
    (hperm : I.perm = true) (haw : aw.toNat ≤ 10) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 327) (exponent :: R) mem aw rdata σ k C) :
    ∃ (evm' : State) (σ' : AccountMap) (mem' : ByteArray) (gasArg aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm (initializeTransition.body.drop 5 |>.take 5)
        (.ok {contract := contract, locals := locals} evm') ∧
      SourceState s0 I σ' evm' ∧ aw'.toNat ≤ 10 ∧ mem'.size = 320 ∧ WordMemoryRange mem mem' 0 192 ∧
      config.externalABI.encode? "symbol" [] = some (mem'.readWithPadding 316 4) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 388)
        (gasArg :: token :: ⟨316⟩ :: ⟨4⟩ :: ⟨288⟩ :: ⟨96⟩ :: token :: R) mem' aw' rdata σ' k' C' := by
  let precision := UInt256.exp ⟨10⟩ exponent
  let mem0 := precision.toByteArray.write 0 mem 192 32
  let mem1 := (UInt256.ofNat 2514000705).toByteArray.write 0 mem0 288 32
  have hgap (m : ByteArray) (off : Nat) (hsmall : off ≤ 288) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hframe0 : WordMemoryRange mem mem0 0 192 :=
    wordMemoryRange_write mem precision 192 0 192 (hgap _ _ (by omega)) (Or.inl (by omega))
  have hm0 (off : Nat) (hsmall : off + 32 ≤ 192) : memLoad (UInt256.ofNat off) mem0 = memLoad (UInt256.ofNat off) mem :=
    hframe0.load off (by omega) hsmall (by omega) (by change off < 2 ^ 256; omega)
  have hma0 := (hm0 64 (by omega)).trans hma
  have hmc0 := (hm0 96 (by omega)).trans hmc
  have hmt0 := (hm0 128 (by omega)).trans hmt
  have hml0 := (hm0 160 (by omega)).trans hml
  have hmp0 : memLoad (UInt256.ofNat 192) mem0 = precision :=
    memLoad_write_back _ _ 192 (by decide +kernel) (hgap _ _ (by omega))
  obtain ⟨hsource, hs'⟩ := vaultInitializeConfigSource (fork := fork) (hperm := hperm) hs ha hc hl hp hbase hacanon hccanon hlcanon
  obtain ⟨gasArg, k', C', rd388⟩ := vaultBlocks.vault_block_327 hstack hperm h
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 388)
    (gasArg :: memLoad (UInt256.ofNat 128) mem0 :: ⟨316⟩ :: ⟨4⟩ :: ⟨288⟩ :: ⟨96⟩ :: memLoad (UInt256.ofNat 128) mem0 :: R)
    mem1 _ rdata (vaultInitializeConfigAccounts I σ (memLoad (UInt256.ofNat 64) mem0)
      (memLoad (UInt256.ofNat 96) mem0) (memLoad (UInt256.ofNat 160) mem0) (memLoad (UInt256.ofNat 192) mem0)) k' C' at rd388
  rw [hma0, hmc0, hmt0, hml0, hmp0] at rd388
  refine ⟨_, _, mem1, gasArg, _, k', C', hsource, hs', ?_, ?_, ?_, ?_, rd388⟩
  · repeat' apply memoryActive_le (bound := 10) ?_ (by decide +kernel)
    exact haw
  · change (writeWord mem0 288 (UInt256.ofNat 2514000705)).size = 320
    rw [writeWord_size _ _ _ (hgap _ _ (by omega))]
    change max (writeWord mem 192 precision).size 320 = 320
    rw [writeWord_size _ _ _ (hgap _ _ (by omega)), hsize]
    rfl
  · exact hframe0.trans (wordMemoryRange_write mem0 (UInt256.ofNat 2514000705) 288 0 192
      (hgap _ _ (by omega)) (Or.inl (by omega)))
  · exact vyperNullaryCallData _ _ mem0 288 (by decide +kernel) (hgap _ _ (by omega))

end Benchmarks.CurveVault
