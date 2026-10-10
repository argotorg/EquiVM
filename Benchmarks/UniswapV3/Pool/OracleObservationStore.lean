import Benchmarks.UniswapV3.Pool.ObservationWriteFields
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def oracleObservationState (evm : EVM.State) (index : UInt256) (obs : OracleObservation) : EVM.State :=
  let e0 := observationFieldState evm index .timestamp obs
  let e1 := observationFieldState e0 index .cumulative obs
  let e2 := observationFieldState e1 index .secondsPerLiquidity obs
  observationFieldState e2 index .initialized obs

theorem oracleObservationWrite (evm : EVM.State) (index : UInt256) (obs : OracleObservation) :
    solidityWriteStorage? storageBackend.locate? evm
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat))]⟩ observationStorageType obs.value =
      .ok (oracleObservationState evm index obs) := by
  let e0 := observationFieldState evm index .timestamp obs
  let e1 := observationFieldState e0 index .cumulative obs
  let e2 := observationFieldState e1 index .secondsPerLiquidity obs
  have h0 := observationWriteFieldStore evm index .timestamp obs
  have h1 := observationWriteFieldStore e0 index .cumulative obs
  have h2 := observationWriteFieldStore e1 index .secondsPerLiquidity obs
  have h3 := observationWriteFieldStore e2 index .initialized obs
  have hl0 := observationWriteLocate index .timestamp
  have hl1 := observationWriteLocate index .cumulative
  have hl2 := observationWriteLocate index .secondsPerLiquidity
  have hl3 := observationWriteLocate index .initialized
  dsimp only [ObservationWriteField.name] at hl0 hl1 hl2 hl3
  dsimp only [ObservationWriteField.value] at h0 h1 h2 h3
  dsimp only [e0, e1, e2] at h1 h2 h3
  simp only [observationStorageType, OracleObservation.value, solidityWriteStorage?,
    solidityWriteFields?, ↓reduceIte, List.cons_append, List.nil_append,
    solidityLeafLoc?_of_leaf hl0, solidityLeafLoc?_of_leaf hl1,
    solidityLeafLoc?_of_leaf hl2, solidityLeafLoc?_of_leaf hl3,
    h0, h1, h2, h3, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

def oracleObservationWord (obs : OracleObservation) (old : UInt256) : UInt256 :=
  let w0 := packedFieldUpdate old obs.timestamp 0 32
  let w1 := packedFieldUpdate w0 (EVM.wordOfInt obs.tickCumulative) 32 56
  let w2 := packedFieldUpdate w1 obs.secondsPerLiquidity 88 160
  packedFieldUpdate w2 obs.initialized.toUInt256 248 8

theorem oracleObservationState_eq (evm : EVM.State) (index : UInt256) (obs : OracleObservation) :
    oracleObservationState evm index obs =
      modifyStorageWord evm (observationSlot index) (oracleObservationWord obs) := by
  simp only [oracleObservationState, observationFieldState, modifyStorageWord_comp]
  rfl

theorem oracleObservationState_executionEnv (evm : EVM.State) (index : UInt256)
    (obs : OracleObservation) : (oracleObservationState evm index obs).executionEnv =
      evm.executionEnv := by
  rw [oracleObservationState_eq]
  exact storageStore_executionEnv _ _ _ _

def oracleObservationMap (σ : AccountMap) (ee : ExecutionEnv) (index : UInt256)
    (obs : OracleObservation) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (observationSlot index)
    (oracleObservationWord obs (solcSlotWordAt (observationSlot index) σ ee))

theorem SourceState.oracleObservation {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (index : UInt256) (obs : OracleObservation) :
    SourceState s0 ee (oracleObservationMap σ ee index obs) (oracleObservationState evm index obs) := by
  rw [oracleObservationState_eq]
  exact hs.readModifyWrite (observationSlot index) (oracleObservationWord obs)

theorem assignOracleObservation (locals imms : Store) (evm : EVM.State) (expr : Expr)
    (index : UInt256) (obs : OracleObservation) (hbase : locals.get? "observations" = none)
    (he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm expr =
      .ok (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"observations", [.aindex expr]⟩ obs.value =
      .ok ({contract := contract, locals := locals, immutables := imms},
        oracleObservationState evm index obs) := by
  have hbound : arrayIndexInBounds? config evm contract.storage "observations" []
      (.int (Int.ofNat index.toNat)) = .ok () := by rw [observationArrayBounds, if_pos hin]
  have hresolve : resolveStorageRef? config
      {contract := contract, locals := locals, immutables := imms} evm
      ⟨"observations", [.aindex expr]⟩ =
      .ok (⟨"observations", [.aindex (.int (Int.ofNat index.toNat))]⟩, observationStorageType) :=
    resolveStorageRef?_ok hbase (evalStorageRef_aindex_ok he rfl hbound) rfl
  simp only [assignStorageRef?, hresolve, poolStorageBackend_eq, solidityStorageBackend,
    oracleObservationWrite, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
