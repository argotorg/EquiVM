import Benchmarks.UniswapV3.Pool.BurnOwedSource
import Benchmarks.UniswapV3.Pool.PositionOwedPair
import Benchmarks.UniswapV3.Pool.PositionUpdateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnOwedWord (old x0 x1 : UInt256) : UInt256 :=
  protocolFeeUpdateWord false
    (protocolFeeUpdateWord true old (uint128Word (positionOwedPart true old + x1)))
    (uint128Word (positionOwedPart false old + x0))

theorem burnOwedWord_evm (old x0 x1 : UInt256) :
    burnOwedWord old x0 x1 =
      UInt256.lor
        (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1)))
          (UInt256.lor (UInt256.land old (UInt256.ofNat (2 ^ 128 - 1)))
            (UInt256.mul (UInt256.ofNat (2 ^ 128))
              (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
                (x1 + UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
                  (UInt256.div old (UInt256.ofNat (2 ^ 128))))))))
        (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
          (x0 + UInt256.land old (UInt256.ofNat (2 ^ 128 - 1)))) := by
  simp only [burnOwedWord, protocolFeeUpdateWord, Bool.false_eq_true, if_false, if_true,
    uint128Word_clean (uint128Word_lt _)]
  rw [u256_lor_comm (uint128Word _), u256_land_comm old,
    u256_land_comm (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1))),
    u256_mul_comm (UInt256.ofNat (2 ^ 128))]
  simp only [positionOwedPart, Bool.false_eq_true, if_false, if_true, uint128Word]
  rw [u256_add_comm x0, u256_add_comm x1]

theorem SourceState.burnOwed {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (key : UInt256) (a0 a1 : Int) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
        (burnOwedWord (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee)
          (burnAmount a0) (burnAmount a1)))
      (burnOwedState key a0 a1 evm) := by
  let f := fun old ↦ protocolFeeUpdateWord false
    (protocolFeeUpdateWord true old (burnOwedValue key a0 a1 evm true))
    (burnOwedValue key a0 a1 evm false)
  have hf := hs.readModifyWrite (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) f
  change SourceState s0 ee
    (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
      (f (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee)))
    (modifyStorageWord evm (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) f) at hf
  rw [burnOwedState, storePositionOwedPair_eq]
  simpa only [f, burnOwedValue, positionOwedWord_eq, ← hs.accounts, hs.env,
    Bool.false_eq_true, if_false, if_true, burnOwedWord] using hf

end Benchmarks.UniswapV3.Pool
