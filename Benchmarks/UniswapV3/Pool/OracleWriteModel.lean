import Benchmarks.UniswapV3.Pool.OracleSearchModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

structure OracleWriteArgs where
  index : UInt256
  time : UInt256
  tick : Int
  liquidity : UInt256
  cardinality : UInt256
  cardinalityNext : UInt256

def OracleWriteArgs.Fits (a : OracleWriteArgs) : Prop :=
  a.index.toNat < 2 ^ 16 ∧ a.time.toNat < 2 ^ 32 ∧
    (-(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23) ∧ a.liquidity.toNat < 2 ^ 128 ∧
    a.cardinality.toNat < 2 ^ 16 ∧ a.cardinalityNext.toNat < 2 ^ 16

def oracleWriteLast (a : OracleWriteArgs) (evm : EVM.State) : OracleObservation :=
  oracleStoredObservation a.index evm.accountMap evm.executionEnv

def oracleWriteSame (a : OracleWriteArgs) (evm : EVM.State) : Bool :=
  decide ((oracleWriteLast a evm).timestamp = a.time)

def oracleWriteCardinalityPred (a : OracleWriteArgs) : UInt256 :=
  UInt256.land (UInt256.sub a.cardinality ⟨1⟩) (UInt256.ofNat 65535)

def oracleWriteGrows (a : OracleWriteArgs) : Bool :=
  decide (a.cardinality.toNat < a.cardinalityNext.toNat) &&
    decide (a.index = oracleWriteCardinalityPred a)

def oracleWriteCardinality (a : OracleWriteArgs) : UInt256 :=
  if oracleWriteGrows a then a.cardinalityNext else a.cardinality

def oracleWriteIndex (a : OracleWriteArgs) : UInt256 :=
  oracleSearchLeft a.index (oracleWriteCardinality a)

def oracleWriteResultObservation (a : OracleWriteArgs) (evm : EVM.State) : OracleObservation :=
  oracleTransformed (oracleWriteLast a evm) a.time a.tick a.liquidity

theorem oracleWriteCardinality_lt (a : OracleWriteArgs) (hfit : a.Fits) :
    (oracleWriteCardinality a).toNat < 2 ^ 16 := by
  unfold oracleWriteCardinality
  split_ifs
  · exact hfit.2.2.2.2.2
  · exact hfit.2.2.2.2.1

theorem oracleWriteIndex_lt (a : OracleWriteArgs) (hfit : a.Fits)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) : (oracleWriteIndex a).toNat < 65535 :=
  oracleSearchRemainder_lt _ _ hn (oracleWriteCardinality_lt a hfit)

def oracleWriteFunction : FunctionDecl := contract.functions[25]!

theorem oracleWriteLookup : lookupCallable? contract "Oracle_write" =
    some oracleWriteFunction.toCallable := rfl

def oracleWriteLocals (a : OracleWriteArgs) : Store :=
  let locals := (∅ : Store).insert "cardinalityNext" (.int (Int.ofNat a.cardinalityNext.toNat))
  let locals := locals.insert "cardinality" (.int (Int.ofNat a.cardinality.toNat))
  let locals := locals.insert "liquidity" (.int (Int.ofNat a.liquidity.toNat))
  let locals := locals.insert "tick" (.int a.tick)
  let locals := locals.insert "blockTimestamp" (.int (Int.ofNat a.time.toNat))
  locals.insert "index" (.int (Int.ofNat a.index.toNat))

def oracleWriteFrame (imms : Store) (a : OracleWriteArgs) : Frame :=
  {contract := contract, locals := oracleWriteLocals a, immutables := imms}

def oracleWriteZeroFrame (imms : Store) (a : OracleWriteArgs) : Frame :=
  let locals := ((oracleWriteLocals a).insert "indexUpdated" (.int 0)).insert "cardinalityUpdated" (.int 0)
  {oracleWriteFrame imms a with locals := locals}

def oracleWriteLastFrame (imms : Store) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  let locals := (oracleWriteZeroFrame imms a).locals.insert "last" (oracleWriteLast a evm).value
  {oracleWriteZeroFrame imms a with locals := locals}

def oracleWriteCardinalityFrame (imms : Store) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  let locals := (oracleWriteLastFrame imms a evm).locals.insert "cardinalityUpdated"
    (.int (Int.ofNat (oracleWriteCardinality a).toNat))
  {oracleWriteLastFrame imms a evm with locals := locals}

def oracleWriteIndexFrame (imms : Store) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  let locals := (oracleWriteCardinalityFrame imms a evm).locals.insert "indexUpdated"
    (.int (Int.ofNat (oracleWriteIndex a).toNat))
  {oracleWriteCardinalityFrame imms a evm with locals := locals}

def oracleWriteTransformedFrame (imms : Store) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  let locals := (oracleWriteIndexFrame imms a evm).locals.insert "__c0"
    (oracleWriteResultObservation a evm).value
  {oracleWriteIndexFrame imms a evm with locals := locals}

theorem oracleWriteBind (a : OracleWriteArgs) :
    bindParams? oracleWriteFunction.params
      [.int (Int.ofNat a.index.toNat), .int (Int.ofNat a.time.toNat), .int a.tick,
        .int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat a.cardinality.toNat),
        .int (Int.ofNat a.cardinalityNext.toNat)] = some (oracleWriteLocals a) := rfl

end Benchmarks.UniswapV3.Pool
