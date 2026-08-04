import Examples.Ripemd160Old.DecodeGenerated.Chunk60

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes61 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8406⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨8408⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8409⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8410⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8411⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8412⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8413⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8414⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8415⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨8417⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8418⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8419⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨8421⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨8422⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8423⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨8424⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8425⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8426⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1))),
  (⟨8428⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8429⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8430⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨8432⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8433⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8434⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8435⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8436⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8437⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8438⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8439⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8440⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨8442⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8443⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8444⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8445⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8446⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8447⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8448⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8449⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨8451⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8452⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8453⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨8455⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8456⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8457⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8458⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8459⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8460⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8461⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨8462⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨8464⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8465⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8466⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨8468⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨8469⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8470⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8471⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8472⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8473⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1))),
  (⟨8475⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none)),
  (⟨8476⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none)),
  (⟨8477⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨8479⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨8480⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none)),
  (⟨8481⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8482⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8483⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none)),
  (⟨8484⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1732584193⟩, 4))),
  (⟨8489⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8490⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4023233417⟩, 4))),
  (⟨8495⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8496⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2562383102⟩, 4))),
  (⟨8501⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8502⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨271733878⟩, 4))),
  (⟨8507⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8508⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨3285377520⟩, 4))),
  (⟨8513⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8514⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8516⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨8517⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨8518⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1))),
  (⟨8520⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8521⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2))),
  (⟨8524⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8525⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8526⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8527⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8528⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8530⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨8531⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨8532⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨8533⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8534⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨8536⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨8537⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none)),
  (⟨8538⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none)),
  (⟨8539⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none)),
  (⟨8540⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8618⟩, 2))),
  (⟨8543⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨8544⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨8545⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes61_correct : ∀ i : Fin generatedDecodes61.size,
    decode runtimeBytecode generatedDecodes61[i].1 = generatedDecodes61[i].2 := by
  native_decide

theorem decode_8406 : decode runtimeBytecode ⟨8406⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨0, by decide⟩
theorem decode_8408 : decode runtimeBytecode ⟨8408⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨1, by decide⟩
theorem decode_8409 : decode runtimeBytecode ⟨8409⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨2, by decide⟩
theorem decode_8410 : decode runtimeBytecode ⟨8410⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨3, by decide⟩
theorem decode_8411 : decode runtimeBytecode ⟨8411⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨4, by decide⟩
theorem decode_8412 : decode runtimeBytecode ⟨8412⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨5, by decide⟩
theorem decode_8413 : decode runtimeBytecode ⟨8413⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨6, by decide⟩
theorem decode_8414 : decode runtimeBytecode ⟨8414⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨7, by decide⟩
theorem decode_8415 : decode runtimeBytecode ⟨8415⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨8, by decide⟩
theorem decode_8417 : decode runtimeBytecode ⟨8417⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨9, by decide⟩
theorem decode_8418 : decode runtimeBytecode ⟨8418⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨10, by decide⟩
theorem decode_8419 : decode runtimeBytecode ⟨8419⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨11, by decide⟩
theorem decode_8421 : decode runtimeBytecode ⟨8421⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨12, by decide⟩
theorem decode_8422 : decode runtimeBytecode ⟨8422⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨13, by decide⟩
theorem decode_8423 : decode runtimeBytecode ⟨8423⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨14, by decide⟩
theorem decode_8424 : decode runtimeBytecode ⟨8424⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨15, by decide⟩
theorem decode_8425 : decode runtimeBytecode ⟨8425⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨16, by decide⟩
theorem decode_8426 : decode runtimeBytecode ⟨8426⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨17, by decide⟩
theorem decode_8428 : decode runtimeBytecode ⟨8428⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨18, by decide⟩
theorem decode_8429 : decode runtimeBytecode ⟨8429⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨19, by decide⟩
theorem decode_8430 : decode runtimeBytecode ⟨8430⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨20, by decide⟩
theorem decode_8432 : decode runtimeBytecode ⟨8432⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨21, by decide⟩
theorem decode_8433 : decode runtimeBytecode ⟨8433⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨22, by decide⟩
theorem decode_8434 : decode runtimeBytecode ⟨8434⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨23, by decide⟩
theorem decode_8435 : decode runtimeBytecode ⟨8435⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨24, by decide⟩
theorem decode_8436 : decode runtimeBytecode ⟨8436⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨25, by decide⟩
theorem decode_8437 : decode runtimeBytecode ⟨8437⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨26, by decide⟩
theorem decode_8438 : decode runtimeBytecode ⟨8438⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨27, by decide⟩
theorem decode_8439 : decode runtimeBytecode ⟨8439⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨28, by decide⟩
theorem decode_8440 : decode runtimeBytecode ⟨8440⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨29, by decide⟩
theorem decode_8442 : decode runtimeBytecode ⟨8442⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨30, by decide⟩
theorem decode_8443 : decode runtimeBytecode ⟨8443⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨31, by decide⟩
theorem decode_8444 : decode runtimeBytecode ⟨8444⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨32, by decide⟩
theorem decode_8445 : decode runtimeBytecode ⟨8445⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨33, by decide⟩
theorem decode_8446 : decode runtimeBytecode ⟨8446⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨34, by decide⟩
theorem decode_8447 : decode runtimeBytecode ⟨8447⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨35, by decide⟩
theorem decode_8448 : decode runtimeBytecode ⟨8448⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨36, by decide⟩
theorem decode_8449 : decode runtimeBytecode ⟨8449⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨37, by decide⟩
theorem decode_8451 : decode runtimeBytecode ⟨8451⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨38, by decide⟩
theorem decode_8452 : decode runtimeBytecode ⟨8452⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨39, by decide⟩
theorem decode_8453 : decode runtimeBytecode ⟨8453⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨40, by decide⟩
theorem decode_8455 : decode runtimeBytecode ⟨8455⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨41, by decide⟩
theorem decode_8456 : decode runtimeBytecode ⟨8456⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨42, by decide⟩
theorem decode_8457 : decode runtimeBytecode ⟨8457⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨43, by decide⟩
theorem decode_8458 : decode runtimeBytecode ⟨8458⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨44, by decide⟩
theorem decode_8459 : decode runtimeBytecode ⟨8459⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨45, by decide⟩
theorem decode_8460 : decode runtimeBytecode ⟨8460⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨46, by decide⟩
theorem decode_8461 : decode runtimeBytecode ⟨8461⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨47, by decide⟩
theorem decode_8462 : decode runtimeBytecode ⟨8462⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨48, by decide⟩
theorem decode_8464 : decode runtimeBytecode ⟨8464⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨49, by decide⟩
theorem decode_8465 : decode runtimeBytecode ⟨8465⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨50, by decide⟩
theorem decode_8466 : decode runtimeBytecode ⟨8466⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨51, by decide⟩
theorem decode_8468 : decode runtimeBytecode ⟨8468⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨52, by decide⟩
theorem decode_8469 : decode runtimeBytecode ⟨8469⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨53, by decide⟩
theorem decode_8470 : decode runtimeBytecode ⟨8470⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨54, by decide⟩
theorem decode_8471 : decode runtimeBytecode ⟨8471⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨55, by decide⟩
theorem decode_8472 : decode runtimeBytecode ⟨8472⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨56, by decide⟩
theorem decode_8473 : decode runtimeBytecode ⟨8473⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨57, by decide⟩
theorem decode_8475 : decode runtimeBytecode ⟨8475⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨58, by decide⟩
theorem decode_8476 : decode runtimeBytecode ⟨8476⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.AND), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨59, by decide⟩
theorem decode_8477 : decode runtimeBytecode ⟨8477⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨60, by decide⟩
theorem decode_8479 : decode runtimeBytecode ⟨8479⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨61, by decide⟩
theorem decode_8480 : decode runtimeBytecode ⟨8480⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.SUB), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨62, by decide⟩
theorem decode_8481 : decode runtimeBytecode ⟨8481⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨63, by decide⟩
theorem decode_8482 : decode runtimeBytecode ⟨8482⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨64, by decide⟩
theorem decode_8483 : decode runtimeBytecode ⟨8483⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE8), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨65, by decide⟩
theorem decode_8484 : decode runtimeBytecode ⟨8484⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨1732584193⟩, 4)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨66, by decide⟩
theorem decode_8489 : decode runtimeBytecode ⟨8489⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨67, by decide⟩
theorem decode_8490 : decode runtimeBytecode ⟨8490⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨4023233417⟩, 4)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨68, by decide⟩
theorem decode_8495 : decode runtimeBytecode ⟨8495⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨69, by decide⟩
theorem decode_8496 : decode runtimeBytecode ⟨8496⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨2562383102⟩, 4)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨70, by decide⟩
theorem decode_8501 : decode runtimeBytecode ⟨8501⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨71, by decide⟩
theorem decode_8502 : decode runtimeBytecode ⟨8502⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨271733878⟩, 4)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨72, by decide⟩
theorem decode_8507 : decode runtimeBytecode ⟨8507⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨73, by decide⟩
theorem decode_8508 : decode runtimeBytecode ⟨8508⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH4), some (⟨3285377520⟩, 4)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨74, by decide⟩
theorem decode_8513 : decode runtimeBytecode ⟨8513⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨75, by decide⟩
theorem decode_8514 : decode runtimeBytecode ⟨8514⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨76, by decide⟩
theorem decode_8516 : decode runtimeBytecode ⟨8516⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨77, by decide⟩
theorem decode_8517 : decode runtimeBytecode ⟨8517⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨78, by decide⟩
theorem decode_8518 : decode runtimeBytecode ⟨8518⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨160⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨79, by decide⟩
theorem decode_8520 : decode runtimeBytecode ⟨8520⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨80, by decide⟩
theorem decode_8521 : decode runtimeBytecode ⟨8521⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨512⟩, 2)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨81, by decide⟩
theorem decode_8524 : decode runtimeBytecode ⟨8524⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨82, by decide⟩
theorem decode_8525 : decode runtimeBytecode ⟨8525⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨83, by decide⟩
theorem decode_8526 : decode runtimeBytecode ⟨8526⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨84, by decide⟩
theorem decode_8527 : decode runtimeBytecode ⟨8527⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨85, by decide⟩
theorem decode_8528 : decode runtimeBytecode ⟨8528⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨86, by decide⟩
theorem decode_8530 : decode runtimeBytecode ⟨8530⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨87, by decide⟩
theorem decode_8531 : decode runtimeBytecode ⟨8531⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨88, by decide⟩
theorem decode_8532 : decode runtimeBytecode ⟨8532⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨89, by decide⟩
theorem decode_8533 : decode runtimeBytecode ⟨8533⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨90, by decide⟩
theorem decode_8534 : decode runtimeBytecode ⟨8534⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨91, by decide⟩
theorem decode_8536 : decode runtimeBytecode ⟨8536⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨92, by decide⟩
theorem decode_8537 : decode runtimeBytecode ⟨8537⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.DIV), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨93, by decide⟩
theorem decode_8538 : decode runtimeBytecode ⟨8538⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP5), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨94, by decide⟩
theorem decode_8539 : decode runtimeBytecode ⟨8539⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.LT), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨95, by decide⟩
theorem decode_8540 : decode runtimeBytecode ⟨8540⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8618⟩, 2)) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨96, by decide⟩
theorem decode_8543 : decode runtimeBytecode ⟨8543⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨97, by decide⟩
theorem decode_8544 : decode runtimeBytecode ⟨8544⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨98, by decide⟩
theorem decode_8545 : decode runtimeBytecode ⟨8545⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes61] using generatedDecodes61_correct ⟨99, by decide⟩

end Ripemd160Old
