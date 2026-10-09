import Benchmarks.CompoundIII.Comet.UserBasicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def UserBasicData.normalized (basic : UserBasicData) : UserBasicData :=
  { basic with principal := UInt256.signextend (UInt256.ofNat 12) basic.principal }

theorem userBasicValue_normalized (basic : UserBasicData) :
    userBasicValue basic.normalized = userBasicValue basic := by
  simp only [userBasicValue, userBasicValues, UserBasicData.normalized, signed104_signextend]

theorem UserBasicMemory.normalized {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    UserBasicMemory mem ptr basic.normalized := by
  apply h.congr
  intro i hi
  interval_cases i <;> simp only [userBasicMemWord, UserBasicData.normalized,
    show (⟨12⟩ : UInt256) = UInt256.ofNat 12 from rfl, signextend104_idem]

theorem UserBasicData.normalized_principal (basic : UserBasicData) :
    UInt256.signextend ⟨12⟩ basic.normalized.principal = basic.normalized.principal :=
  signextend104_idem basic.principal

end Benchmarks.CompoundIII.Comet
